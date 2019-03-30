//! Elaboration of lists clauses to case trees.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{IntroParam, Literal, Pattern, SpannedString, Term};
use mltt_core::syntax::{core, domain, AppMode, LiteralIntro};
use mltt_span::FileSpan;
use std::collections::VecDeque;

use super::{check_term, do_closure_app, literal, synth_term, synth_universe, Context};

////////////////////////////////////////////////////////////////////////////////////////////////////
// Top-level Implementation
////////////////////////////////////////////////////////////////////////////////////////////////////

/// A pattern clause
pub struct Clause<'file> {
    /// The parameters that are still waiting to be elaborated
    concrete_params: &'file [IntroParam<'file>],
    /// The expected body type for this clause
    concrete_body_ty: Option<&'file Term<'file>>,
    /// The concrete body of this clause
    concrete_body: &'file Term<'file>,
}

impl<'file> Clause<'file> {
    pub fn new(
        concrete_params: &'file [IntroParam<'file>],
        concrete_body_ty: Option<&'file Term<'file>>,
        concrete_body: &'file Term<'file>,
    ) -> Clause<'file> {
        Clause {
            concrete_params,
            concrete_body_ty,
            concrete_body,
        }
    }
}

/// Check that a given clause conforms to an expected type, and elaborates
/// it into a case tree.
///
/// Returns the elaborated term.
pub fn check_clause(
    context: &Context,
    case_span: FileSpan,
    clause: Clause<'_>,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    check_clauses(context, case_span, &[], vec![clause], expected_ty)
}

/// Synthesize the type of a clause, elaborating it into a case tree.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_clause(
    context: &Context,
    case_span: FileSpan,
    clause: Clause<'_>,
) -> Result<(core::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    synth_clauses(context, case_span, &[], vec![clause])
}

/// Check that the given clauses conform to an expected type, and elaborate
/// them into a case tree.
///
/// Returns the elaborated term.
pub fn check_clauses(
    context: &Context,
    _case_span: FileSpan,
    scrutinees: &[Term<'_>],
    clauses: Vec<Clause<'_>>,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    let mut context = context.clone();

    let (params, clause_states, body_ty) = intro_params(&mut context, clauses, expected_ty)?;
    // FIXME: not the right level
    let default = core::RcTerm::from(core::Term::PrimitiveAbort(
        context.read_back(None, expected_ty)?,
        "entered unreachable code".to_owned(),
    ));
    let body = check_branches(&context, &params, clause_states, &default, &body_ty)?;

    Ok(done(params, body))
}

/// Synthesize the type of the clauses, elaborating them into a case tree.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_clauses(
    context: &Context,
    case_span: FileSpan,
    scrutinees: &[Term<'_>],
    clauses: Vec<Clause<'_>>,
) -> Result<(core::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    // TODO: replicate the behaviour of `check_clauses`

    match clauses.split_first() {
        Some((clause, [])) => {
            if let Some(param) = clause.concrete_params.first() {
                // TODO: We will be able to type this once we have annotated patterns!
                return Err(
                    Diagnostic::new_error("unable to infer the type of parameter")
                        .with_label(DiagnosticLabel::new_primary(param.span())),
                );
            }

            synth_clause_body(&context, clause)
        },
        Some((_, _)) => Err(
            Diagnostic::new_error("multi clause functions are not yet supported")
                .with_label(DiagnosticLabel::new_primary(case_span)),
        ),
        None => Err(
            Diagnostic::new_error("empty case matches are not yet supported")
                .with_label(DiagnosticLabel::new_primary(case_span)),
        ),
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper types
////////////////////////////////////////////////////////////////////////////////////////////////////

/// The state of a pattern clause, part-way through evaluation
pub struct ClauseState<'file> {
    /// The patterns that have currently been discovered by comparing to the
    /// expected application mode (from the type).
    checked_patterns: VecDeque<CheckedPattern<'file>>,
    /// The variable binders we have traversed over.
    ///
    /// We'll add these to the context once we are ready to elaborate the body
    /// of the clause.
    binders: Vec<(Option<SpannedString<'file>>, CheckedParam)>,
    /// The expected body type for this clause.
    concrete_body_ty: Option<&'file Term<'file>>,
    /// The concrete body of this clause.
    concrete_body: &'file Term<'file>,
}

enum CheckedPattern<'file> {
    Var(Option<SpannedString<'file>>),
    Literal(Literal<'file>),
}

impl<'file> From<&Pattern<'file>> for CheckedPattern<'file> {
    fn from(src: &Pattern<'file>) -> CheckedPattern<'file> {
        match src {
            Pattern::Var(name) => CheckedPattern::Var(Some(name.clone())),
            Pattern::Literal(literal) => CheckedPattern::Literal(literal.clone()),
        }
    }
}

/// A top level parameter
#[derive(Clone)]
struct CheckedParam {
    app_mode: AppMode,
    var: domain::RcValue,
    ty: domain::RcType,
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper functions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Introduce the parameters that we need for this set of clauses
fn intro_params<'file>(
    context: &mut Context,
    mut clauses: Vec<Clause<'file>>,
    expected_ty: &domain::RcType,
) -> Result<(Vec<CheckedParam>, Vec<ClauseState<'file>>, domain::RcType), Diagnostic<FileSpan>> {
    log::trace!("introduce parameters");

    let mut params = Vec::new();
    let mut clause_states = clauses
        .iter()
        .map(|clause| ClauseState {
            checked_patterns: VecDeque::new(),
            binders: Vec::new(),
            concrete_body_ty: clause.concrete_body_ty,
            concrete_body: clause.concrete_body,
        })
        .collect::<Vec<_>>();

    // FIXME: This is a hideous mess

    let mut expected_ty = expected_ty.clone();

    while let Some((app_mode, param_ty, next_body_ty)) = next_expected_param(&expected_ty) {
        let mut is_done = false;

        for (clause, clause_state) in Iterator::zip(clauses.iter_mut(), clause_states.iter_mut()) {
            use self::CheckedPattern::Var;

            match (is_done, clause.concrete_params.split_first()) {
                (false, Some((param, rest_params))) => match check_param(param, &app_mode)? {
                    pattern @ Var(None) => clause_state.checked_patterns.push_back(pattern),
                    pattern => {
                        clause.concrete_params = rest_params;
                        clause_state.checked_patterns.push_back(pattern);
                    },
                },
                (true, Some((first_param, rest_params))) => {
                    let span = match rest_params.last() {
                        None => first_param.span(),
                        Some(last_param) => FileSpan::merge(first_param.span(), last_param.span()),
                    };
                    return Err(Diagnostic::new_error("too many parameters")
                        .with_label(DiagnosticLabel::new_primary(span)));
                },
                (false, None) => is_done = true,
                (true, None) => continue,
            }
        }

        if is_done {
            break;
        }

        // Introduce the parameter
        let param_var = context.local_bind(None, param_ty.clone());
        params.push(CheckedParam {
            app_mode: app_mode.clone(),
            var: param_var.clone(),
            ty: param_ty.clone(),
        });

        // Update the body type
        expected_ty = do_closure_app(next_body_ty, param_var)?;
    }

    Ok((params, clause_states, expected_ty))
}

/// Get the next expected parameter from the expected type
fn next_expected_param<'ty>(
    expected_ty: &'ty domain::RcType,
) -> Option<(&'ty AppMode, &'ty domain::RcValue, &'ty domain::AppClosure)> {
    match expected_ty.as_ref() {
        domain::Value::FunType(app_mode, param_ty, body_ty) => Some((app_mode, param_ty, body_ty)),
        _ => None,
    }
}

/// Check that a given parameter matches the expected application mode, and
/// return the pattern inside it.
fn check_param<'file>(
    param: &'file IntroParam<'file>,
    expected_app_mode: &AppMode,
) -> Result<CheckedPattern<'file>, Diagnostic<FileSpan>> {
    log::trace!("check param:\t{}\tapp mode:\t{}", param, expected_app_mode);

    // TODO: Pattern type checking?

    match (param, expected_app_mode) {
        (IntroParam::Explicit(pattern), AppMode::Explicit) => Ok(CheckedPattern::from(pattern)),
        (IntroParam::Implicit(_, intro_label, pattern), AppMode::Implicit(ty_label))
        | (IntroParam::Instance(_, intro_label, pattern), AppMode::Instance(ty_label))
            if intro_label.slice == ty_label.0 =>
        {
            match pattern {
                None => Ok(CheckedPattern::Var(Some(intro_label.clone()))),
                Some(pattern) => Ok(CheckedPattern::from(pattern)),
            }
        },
        (_, AppMode::Implicit(_)) | (_, AppMode::Instance(_)) => Ok(CheckedPattern::Var(None)),
        (IntroParam::Implicit(span, _, _), AppMode::Explicit)
        | (IntroParam::Instance(span, _, _), AppMode::Explicit) => {
            let message = "unexpected parameter pattern";
            Err(Diagnostic::new_error(message).with_label(
                DiagnosticLabel::new_primary(*span).with_message("this parameter is not needed"),
            ))
        },
    }
}

/// Implements the 'mixture rule' and the 'empty rule'
fn check_branches(
    context: &Context,
    params: &[CheckedParam],
    clauses: Vec<ClauseState<'_>>,
    default: &core::RcTerm,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("check branches");

    match params.split_first() {
        None => check_branches_empty(context, clauses, default, expected_body_ty),
        Some(params) => check_branches_mixture(context, params, clauses, default, expected_body_ty),
    }
}

/// Implements the 'empty rule'
fn check_branches_empty(
    context: &Context,
    clauses: Vec<ClauseState<'_>>,
    _default: &core::RcTerm,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("check branches empty");

    // foldr FATBAR default [body | ([], body) <- clauses]

    // > Regarding the fat bar, I implemented that as something like
    // > `t1 [] t2 == let f () = t1 in t2[fail/f()]`, plus some inlining
    // > of `f` when it's only used once or very small
    //
    // - [Ollef](https://gitter.im/pikelet-lang/Lobby?at=5c91f5bc8aa66959b63dfa40)

    // for clause in clauses.iter().rev() {
    //     let body = check_clause_body(context, clause, expected_body_ty)?;
    // }

    // Ok(core::RcTerm::from(core::Term::Let(
    //     default.clone(),
    //     unimplemented!("check_branches"),
    // )))

    match clauses.split_first() {
        Some((clause, [])) => check_clause_body(context, clause, expected_body_ty),
        Some((_, _)) => Err(Diagnostic::new_error(
            "multi clause functions are not yet supported",
        )),
        None => Err(Diagnostic::new_error(
            "empty case matches are not yet supported",
        )),
    }
}

enum PatternGroup<'file> {
    Var(Vec<ClauseState<'file>>),
    Literal(Vec<(Literal<'file>, ClauseState<'file>)>),
}

// Group patterns by the kind of the first pattern in each clause
fn group_first_patterns<'file>(
    first_param: &CheckedParam,
    clauses: Vec<ClauseState<'file>>,
) -> Vec<PatternGroup<'file>> {
    let mut groups = Vec::new();
    for mut clause in clauses {
        match clause.checked_patterns.pop_front() {
            None => panic!("not enough patterns"),
            Some(CheckedPattern::Var(name)) => {
                // Introduce the appropriate binder when we see a variable
                clause.binders.push((name, first_param.clone()));

                match groups.last_mut() {
                    Some(PatternGroup::Var(clauses)) => clauses.push(clause),
                    _ => groups.push(PatternGroup::Var(vec![clause])),
                }
            },
            Some(CheckedPattern::Literal(literal)) => match groups.last_mut() {
                Some(PatternGroup::Literal(clauses)) => clauses.push((literal, clause)),
                _ => groups.push(PatternGroup::Literal(vec![(literal, clause)])),
            },
        }
    }
    groups
}

/// Implements the 'mixture rule' and the 'variable rule'
fn check_branches_mixture<'file>(
    context: &Context,
    (first_param, rest_params): (&CheckedParam, &[CheckedParam]),
    clauses: Vec<ClauseState<'_>>,
    default: &core::RcTerm,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("check branches mixture");

    group_first_patterns(first_param, clauses)
        .into_iter()
        .rev()
        .fold(Ok(default.clone()), |default, group| match group {
            PatternGroup::Var(clauses) => {
                // TODO: let bindings of binders
                // Ok(core::RcTerm::from(core::Term::Let(
                //     context.read_back(None, &first_param.var)?,
                //     check_branches(context, rest_params, clauses, &default?, expected_body_ty)?,
                // )))
                check_branches(context, rest_params, clauses, &default?, expected_body_ty)
            },
            PatternGroup::Literal(clauses) => {
                let params = (first_param, rest_params);
                check_branches_literal(context, params, clauses, &default?, expected_body_ty)
            },
        })
}

/// Implements the 'literal rule' (adapted from the 'constructor rule').
fn check_branches_literal<'file>(
    context: &Context,
    (first_param, rest_params): (&CheckedParam, &[CheckedParam]),
    clauses: Vec<(Literal<'file>, ClauseState<'file>)>,
    default: &core::RcTerm,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("check branches literal");

    let mut grouped_clauses = Vec::<(LiteralIntro, Vec<ClauseState<'file>>)>::new();

    for (literal, clause) in clauses {
        let literal_intro = literal::check(&context, &literal, &first_param.ty)?;
        match grouped_clauses.binary_search_by(|(l, _)| l.partial_cmp(&literal_intro).unwrap()) {
            Ok(index) => grouped_clauses.get_mut(index).unwrap().1.push(clause),
            Err(index) => grouped_clauses.insert(index, (literal_intro, vec![clause])),
        }
    }

    let clauses = grouped_clauses
        .into_iter()
        .map(|(literal_intro, clauses)| {
            let body = check_branches(context, rest_params, clauses, default, expected_body_ty)?;
            Ok((literal_intro, body))
        })
        .collect::<Result<Vec<_>, _>>()?;

    Ok(core::RcTerm::from(core::Term::LiteralElim(
        context.read_back(None, &first_param.var)?,
        clauses.into(),
        default.clone(), // FIXME: bind?
    )))
}

/// Check that the body of the given clause conforms to they expected type, and
/// elaborate it.
fn check_clause_body(
    context: &Context,
    clause: &ClauseState<'_>,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("check clause body");

    let mut context = context.clone();

    for (name, param) in &clause.binders {
        context.local_define(
            name.as_ref().map(|name| name.to_string()),
            param.var.clone(),
            param.ty.clone(),
        );
    }

    match clause.concrete_body_ty {
        None => check_term(&context, clause.concrete_body, &expected_body_ty),
        Some(concrete_body_ty) => {
            let (body_ty, _) = synth_universe(&context, concrete_body_ty)?;
            let body_ty = context.eval(concrete_body_ty.span(), &body_ty)?;
            let body = check_term(&context, clause.concrete_body, &body_ty)?;
            // TODO: Ensure that this is respecting variance correctly!
            context.expect_subtype(clause.concrete_body.span(), &body_ty, &expected_body_ty)?;
            Ok(body)
        },
    }
}

/// Synthesize the type of the body of a clause, and elaborate it.
fn synth_clause_body(
    context: &Context,
    clause: &Clause<'_>,
) -> Result<(core::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    match clause.concrete_body_ty {
        None => synth_term(context, clause.concrete_body),
        Some(concrete_body_ty) => {
            let (body_ty, _) = synth_universe(context, concrete_body_ty)?;
            let body_ty = context.eval(concrete_body_ty.span(), &body_ty)?;
            let body = check_term(context, clause.concrete_body, &body_ty)?;
            Ok((body, body_ty))
        },
    }
}

/// Finish elaborating the patterns into a case tree by converting the
/// introduced parameters into function introductions.
fn done(intro_app_modes: Vec<CheckedParam>, body: core::RcTerm) -> core::RcTerm {
    intro_app_modes.into_iter().rev().fold(body, |acc, param| {
        core::RcTerm::from(core::Term::FunIntro(param.app_mode, acc))
    })
}
