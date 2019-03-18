//! Elaboration of lists clauses to case trees.

use language_reporting::{Diagnostic, Label as DiagnosticLabel};
use mltt_concrete::{IntroParam, Literal, Pattern, SpannedString, Term};
use mltt_core::syntax::{core, domain, AppMode, LiteralIntro};
use mltt_span::FileSpan;
use std::borrow::Cow;

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
    scrutinees: &[Term<'_>],
    clause: Clause<'_>,
    expected_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    check_clauses(context, case_span, scrutinees, vec![clause], expected_ty)
}

/// Synthesize the type of a clause, elaborating it into a case tree.
///
/// Returns the elaborated term and its synthesized type.
pub fn synth_clause(
    context: &Context,
    case_span: FileSpan,
    scrutinees: &[Term<'_>],
    clause: Clause<'_>,
) -> Result<(core::RcTerm, domain::RcType), Diagnostic<FileSpan>> {
    synth_clauses(context, case_span, scrutinees, vec![clause])
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

    let (params, scrutinees, intro_app_modes, intro_clauses, body_ty) =
        intro_params(&mut context, &scrutinees, clauses, expected_ty)?;

    let default = abort_unreachable(&context, &body_ty)?;
    let body = check_branches(&context, &params, intro_clauses, &default, &body_ty)?;

    Ok(done(scrutinees, intro_app_modes, body))
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

    if !scrutinees.is_empty() {
        return Err(
            Diagnostic::new_error("arguments to pattern matches are not yet supported")
                .with_label(DiagnosticLabel::new_primary(case_span)),
        );
    }

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
pub struct IntroClause<'file> {
    context: Context,
    /// The patterns that have currently been discovered by comparing to the
    /// expected application mode (from the type). These are listed in reverse
    /// order for easy popping!
    checked_patterns: Vec<CheckedPattern<'file>>,
    /// The expected body type for this clause
    concrete_body_ty: Option<&'file Term<'file>>,
    /// The concrete body of this clause
    concrete_body: &'file Term<'file>,
}

impl<'file> IntroClause<'file> {
    fn split_first_pattern(mut self) -> Option<(NextPattern<'file>, IntroClause<'file>)> {
        self.checked_patterns.pop().map(|pattern| match pattern {
            None => (NextPattern::Var(None), self),
            Some(pattern) => match pattern.as_ref() {
                Pattern::Var(name) => (NextPattern::Var(Some(name.clone())), self),
                Pattern::Literal(literal) => (NextPattern::Literal(literal.clone()), self),
            },
        })
    }
}

enum NextPattern<'file> {
    Var(Option<SpannedString<'file>>),
    Literal(Literal<'file>),
}

/// A top level parameter introduction
struct TopLevelParam {
    var: domain::RcValue,
    ty: domain::RcType,
}

/// A checked pattern.
///
/// We use `Some` if a parameter of the matching application mode was found,
/// or `None` if we need to generate a fresh variable name for the parameter,
/// because it was an implicit or instance parameter that we need to skip.
type CheckedPattern<'file> = Option<Cow<'file, Pattern<'file>>>;

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helper functions
////////////////////////////////////////////////////////////////////////////////////////////////////

/// Introduce the parameters that we need for this set of clauses
fn intro_params<'file>(
    context: &mut Context,
    concrete_scrutinees: &[Term<'file>],
    mut concrete_clauses: Vec<Clause<'file>>,
    expected_ty: &domain::RcType,
) -> Result<
    (
        Vec<TopLevelParam>,
        Vec<(core::RcTerm, domain::RcType)>,
        Vec<AppMode>,
        Vec<IntroClause<'file>>,
        domain::RcType,
    ),
    Diagnostic<FileSpan>,
> {
    log::trace!("introduce parameters");

    let mut scrutinees = Vec::with_capacity(concrete_scrutinees.len());
    let mut params = Vec::with_capacity(concrete_scrutinees.len());
    let mut intro_clauses = concrete_clauses
        .iter()
        .map(|clause| (Vec::new(), clause.concrete_body_ty, clause.concrete_body))
        .collect::<Vec<_>>();

    // FIXME: This is a hideous mess

    for concrete_scrutinee in concrete_scrutinees {
        let (scrutinee, scrutinee_ty) = synth_term(context, concrete_scrutinee)?;

        let mut is_done = false;

        for (clause, intro_clauses) in
            Iterator::zip(concrete_clauses.iter_mut(), intro_clauses.iter_mut())
        {
            match (is_done, clause.concrete_params.split_first()) {
                (false, Some((param, rest_params))) => {
                    match check_param(param, &AppMode::Explicit)? {
                        pattern @ None => intro_clauses.0.push(pattern),
                        pattern @ Some(_) => {
                            clause.concrete_params = rest_params;
                            intro_clauses.0.push(pattern);
                        },
                    }
                },
                (true, Some(_)) => unimplemented!("too many patterns"),
                (false, None) => is_done = true,
                (true, None) => continue,
            }
        }

        if is_done {
            break;
        }

        scrutinees.push((scrutinee, scrutinee_ty.clone()));

        // Introduce the parameter
        let param_var = context.local_bind(None, scrutinee_ty.clone());
        params.push(TopLevelParam {
            var: param_var.clone(),
            ty: scrutinee_ty,
        });
    }

    let mut expected_ty = expected_ty.clone();
    let mut intro_app_modes = Vec::new();

    while let Some((app_mode, param_ty, next_body_ty)) = next_expected_param(&expected_ty) {
        let mut is_done = false;

        for (clause, intro_clauses) in
            Iterator::zip(concrete_clauses.iter_mut(), intro_clauses.iter_mut())
        {
            match (is_done, clause.concrete_params.split_first()) {
                (false, Some((param, rest_params))) => match check_param(param, &app_mode)? {
                    pattern @ None => intro_clauses.0.push(pattern),
                    pattern @ Some(_) => {
                        clause.concrete_params = rest_params;
                        intro_clauses.0.push(pattern);
                    },
                },
                (true, Some(_)) => unimplemented!("too many patterns"),
                (false, None) => is_done = true,
                (true, None) => continue,
            }
        }

        if is_done {
            break;
        }

        // Introduce the parameter
        let param_var = context.local_bind(None, param_ty.clone());
        intro_app_modes.push(app_mode.clone());
        params.push(TopLevelParam {
            var: param_var.clone(),
            ty: param_ty,
        });

        // Update the body type, if necessary
        if let Some(next_body_ty) = next_body_ty {
            expected_ty = do_closure_app(&next_body_ty, param_var)?;
        }
    }

    let intro_clauses = intro_clauses
        .into_iter()
        .map(|(mut checked_patterns, concrete_body_ty, concrete_body)| {
            checked_patterns.reverse();
            IntroClause {
                context: context.clone(),
                checked_patterns,
                concrete_body_ty,
                concrete_body,
            }
        })
        .collect();

    Ok((
        params,
        scrutinees,
        intro_app_modes,
        intro_clauses,
        expected_ty,
    ))
}

/// A term that aborts in the case of an unreachable clause
fn abort_unreachable(
    context: &Context,
    ty: &domain::RcValue,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    Ok(core::RcTerm::from(core::Term::PrimitiveAbort(
        context.read_back(None, ty)?,
        "entered unreachable code".to_owned(),
    )))
}

/// Get the next expected parameter from the expected type
fn next_expected_param<'ty>(
    expected_ty: &'ty domain::RcType,
) -> Option<(
    &'ty AppMode,
    domain::RcValue,
    Option<&'ty domain::AppClosure>,
)> {
    if let domain::Value::FunType(app_mode, param_ty, body_ty) = expected_ty.as_ref() {
        log::trace!("next param:\tparam: {}", app_mode);
        Some((app_mode, param_ty.clone(), Some(body_ty)))
    } else {
        log::trace!("next param:\tdone!");
        None
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
        (IntroParam::Explicit(pattern), AppMode::Explicit) => Ok(Some(Cow::Borrowed(pattern))),
        (IntroParam::Implicit(_, intro_label, pattern), AppMode::Implicit(ty_label))
        | (IntroParam::Instance(_, intro_label, pattern), AppMode::Instance(ty_label))
            if intro_label.slice == ty_label.0 =>
        {
            match pattern {
                None => Ok(Some(Cow::Owned(Pattern::Var(intro_label.clone())))),
                Some(pattern) => Ok(Some(Cow::Borrowed(pattern))),
            }
        },
        (_, AppMode::Implicit(_)) | (_, AppMode::Instance(_)) => Ok(None),
        (IntroParam::Implicit(span, _, _), AppMode::Explicit)
        | (IntroParam::Instance(span, _, _), AppMode::Explicit) => {
            let message = "unexpected parameter pattern";
            Err(Diagnostic::new_error(message).with_label(
                DiagnosticLabel::new_primary(*span).with_message("this parameter is not needed"),
            ))
        },
    }
}

enum PatternGroup<'file> {
    Var(Vec<(Option<SpannedString<'file>>, IntroClause<'file>)>),
    Literal(Vec<(Literal<'file>, IntroClause<'file>)>),
}

/// Group patterns by the kind of the first pattern in each clause
fn group_by_first_patterns<'clauses, 'file>(
    clauses: Vec<IntroClause<'file>>,
) -> Vec<PatternGroup<'file>> {
    log::trace!("grouping patterns");

    let mut groups = Vec::new();

    for clause in clauses {
        match clause.split_first_pattern() {
            None => panic!("not enough patterns"),
            Some((NextPattern::Var(name), clause)) => match groups.last_mut() {
                Some(PatternGroup::Var(var_clauses)) => var_clauses.push((name, clause)),
                _ => groups.push(PatternGroup::Var(vec![(name, clause)])),
            },
            Some((NextPattern::Literal(literal), clause)) => match groups.last_mut() {
                Some(PatternGroup::Literal(lit_clauses)) => lit_clauses.push((literal, clause)),
                _ => groups.push(PatternGroup::Literal(vec![(literal, clause)])),
            },
        }
    }

    groups
}

/// Implements the 'mixture rule' and the 'empty rule'
fn check_branches(
    context: &Context,
    params: &[TopLevelParam],
    clauses: Vec<IntroClause<'_>>,
    default: &core::RcTerm,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("check branches");

    match params.split_first() {
        None => {
            // foldr FATBAR default [body | ([], body) <- clauses]

            // > Regarding the fat bar, I implemented that as something like
            // > `t1 [] t2 == let f () = t1 in t2[fail/f()]`, plus some inlining
            // > of `f` when it's only used once or very small
            //
            // - [Ollef](https://gitter.im/pikelet-lang/Lobby?at=5c91f5bc8aa66959b63dfa40)

            // for clause in clauses.iter().rev() {
            //     let body = clause.done()?;
            // }

            // Ok(core::RcTerm::from(core::Term::Let(
            //     default.clone(),
            //     unimplemented!("check_branches"),
            // )))

            match clauses.split_first() {
                Some((clause, [])) => check_clause_body(clause, expected_body_ty),
                Some((_, _)) => Err(Diagnostic::new_error(
                    "multi clause functions are not yet supported",
                )),
                None => Err(Diagnostic::new_error(
                    "empty case matches are not yet supported",
                )),
            }
        },
        Some(params) => group_by_first_patterns(clauses).into_iter().rev().fold(
            Ok(default.clone()),
            |default, group| match group {
                PatternGroup::Var(clauses) => {
                    check_branches_var(context, params, clauses, &default?, expected_body_ty)
                },
                PatternGroup::Literal(clauses) => {
                    check_branches_literal(context, params, clauses, &default?, expected_body_ty)
                },
            },
        ),
    }
}

/// Implements the 'variable rule'.
fn check_branches_var<'file>(
    context: &Context,
    (first_param, rest_params): (&TopLevelParam, &[TopLevelParam]),
    clauses: Vec<(Option<SpannedString<'file>>, IntroClause<'file>)>,
    default: &core::RcTerm,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("check branches var");

    let clauses = clauses
        .into_iter()
        .map(|(var_name, mut clause)| {
            clause.context.local_define(
                var_name.map(|name| name.to_string()),
                first_param.var.clone(),
                first_param.ty.clone(),
            );

            clause
        })
        .collect::<Vec<_>>();

    check_branches(context, rest_params, clauses, default, expected_body_ty)
}

/// Implements the 'literal rule' (adapted from the 'constructor rule').
fn check_branches_literal<'file>(
    context: &Context,
    (first_param, rest_params): (&TopLevelParam, &[TopLevelParam]),
    clauses: Vec<(Literal<'file>, IntroClause<'file>)>,
    default: &core::RcTerm,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    log::trace!("check branches literal");

    let mut grouped_clauses = Vec::<(LiteralIntro, Vec<IntroClause<'file>>)>::new();

    for (literal, clause) in clauses {
        let literal_intro = literal::check(&clause.context, &literal, &first_param.ty)?;
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
    clause: &IntroClause<'_>,
    expected_body_ty: &domain::RcType,
) -> Result<core::RcTerm, Diagnostic<FileSpan>> {
    match clause.concrete_body_ty {
        None => check_term(&clause.context, clause.concrete_body, &expected_body_ty),
        Some(concrete_body_ty) => {
            let (body_ty, _) = synth_universe(&clause.context, concrete_body_ty)?;
            let body_ty = clause.context.eval(concrete_body_ty.span(), &body_ty)?;
            let body = check_term(&clause.context, clause.concrete_body, &body_ty)?;
            // TODO: Ensure that this is respecting variance correctly!
            clause.context.expect_subtype(
                clause.concrete_body.span(),
                &body_ty,
                &expected_body_ty,
            )?;
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
/// introduced parameters into function introductions, and applying the
/// arguments as function eliminations.
fn done(
    scrutinees: Vec<(core::RcTerm, domain::RcType)>,
    intro_app_modes: Vec<AppMode>,
    body: core::RcTerm,
) -> core::RcTerm {
    let body = intro_app_modes
        .into_iter()
        .rev()
        .fold(body, |acc, app_mode| {
            core::RcTerm::from(core::Term::FunIntro(app_mode, acc))
        });

    scrutinees
        .into_iter()
        .rev()
        .fold(body, |acc, (scrutinee, _)| {
            core::RcTerm::from(core::Term::Let(scrutinee, acc))
        })
}
