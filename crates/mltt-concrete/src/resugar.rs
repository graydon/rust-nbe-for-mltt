//! Convert the core syntax into the concrete syntax.
//!
//! We add back in syntactic sugar that was lost during elaboration, and also
//! the necessary parentheses needed to appropriately group expressions.

use mltt_core::syntax::{core, DbIndex, UniverseLevel};

use crate::{Pattern, RecordIntroField, RecordTypeField, Term};

pub struct Env {
    counter: usize,
    names: Vec<String>,
}

impl Env {
    pub fn new() -> Env {
        Env {
            counter: 0,
            names: Vec::new(),
        }
    }

    pub fn lookup_index(&self, index: DbIndex) -> String {
        match self.names.get(self.names.len() - (index.0 + 1) as usize) {
            Some(name) => name.clone(),
            None => format!("free{}", index.0),
        }
    }

    pub fn with_binding<T>(&mut self, f: impl Fn(&mut Env) -> T) -> (String, T) {
        // TODO: use name hint to improve variable names
        let name = format!("x{}", self.counter);
        self.counter += 1;
        self.names.push(name.clone());
        let result = f(self);
        self.names.pop();
        (name, result)
    }
}

pub fn resugar(term: &core::RcTerm) -> Term {
    resugar_env(term, &mut Env::new())
}

pub fn resugar_env(term: &core::RcTerm, env: &mut Env) -> Term {
    // Using precedence climbing (mirroring the language grammar) in
    // order to cut down on extraneous parentheses.

    fn resugar_term(term: &core::RcTerm, env: &mut Env) -> Term {
        match term.as_ref() {
            core::Term::Let(def, /* def_ty, */ body) => {
                let def = resugar_app(def, env);
                let (def_name, body) = env.with_binding(|env| resugar_term(body, env));
                Term::Let(def_name, Box::new(def), Box::new(body))
            },
            core::Term::FunIntro(/* param_ty, */ body) => {
                let (param_name, body) = env.with_binding(|env| resugar_app(body, env));
                // TODO: flatten params
                Term::FunIntro(vec![Pattern::Var(param_name)], Box::new(body))
            },
            _ => resugar_arrow(term, env),
        }
    }

    fn resugar_arrow(term: &core::RcTerm, env: &mut Env) -> Term {
        match term.as_ref() {
            core::Term::FunType(param_ty, body_ty) => {
                let param_ty = resugar_term(param_ty, env);
                let (param_name, body_ty) = env.with_binding(|env| resugar_app(body_ty, env));
                // TODO: only use `param_name` if it is used in `body_ty`
                // TODO: flatten params
                Term::FunType(vec![(vec![param_name], param_ty)], Box::new(body_ty))
            },
            core::Term::RecordType(ty_fields) => {
                let ty_fields = ty_fields
                    .iter()
                    .map(|(_, label, ty)| RecordTypeField {
                        docs: Vec::new(),
                        label: label.0.clone(),
                        ann: resugar_term(ty, env),
                    })
                    .collect();

                Term::RecordType(ty_fields)
            },
            core::Term::RecordIntro(intro_fields) => {
                let intro_fields = intro_fields
                    .iter()
                    .map(|(label, body)| {
                        // TODO: Punned fields
                        // TODO: Function sugar
                        RecordIntroField::Explicit {
                            label: label.0.clone(),
                            patterns: Vec::new(),
                            body_ty: None,
                            body: resugar_term(body, env),
                        }
                    })
                    .collect();

                Term::RecordIntro(intro_fields)
            },
            _ => resugar_app(term, env),
        }
    }

    fn resugar_app(term: &core::RcTerm, env: &mut Env) -> Term {
        match term.as_ref() {
            core::Term::FunApp(fun, arg) => match resugar_term(fun, env) {
                Term::FunApp(fun, mut args) => {
                    args.push(resugar_atomic(arg, env));
                    Term::FunApp(fun, args)
                },
                fun => Term::FunApp(Box::new(fun), vec![resugar_atomic(arg, env)]),
            },
            _ => resugar_atomic(term, env),
        }
    }

    fn resugar_atomic(term: &core::RcTerm, env: &mut Env) -> Term {
        match term.as_ref() {
            core::Term::Var(index) => Term::Var(env.lookup_index(*index)),
            core::Term::RecordProj(record, label) => {
                Term::RecordProj(Box::new(resugar_atomic(record, env)), label.0.clone())
            },
            core::Term::Universe(UniverseLevel(0)) => Term::Universe(None),
            core::Term::Universe(UniverseLevel(level)) => Term::Universe(Some(*level)),
            _ => Term::Parens(Box::new(resugar_term(term, env))),
        }
    }

    resugar_term(term, env)
}
