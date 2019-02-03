//! The unchecked raw syntax

use mltt_core::syntax::UniverseLevel;
use pretty::{BoxDoc, Doc};
use std::fmt;
use std::rc::Rc;

use super::Literal;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RcTerm {
    pub inner: Rc<Term>,
}

impl From<Term> for RcTerm {
    fn from(src: Term) -> RcTerm {
        RcTerm {
            inner: Rc::new(src),
        }
    }
}

impl fmt::Display for RcTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// Raw terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// Variables
    Var(String),
    /// Literals
    Literal(Literal),
    /// Let bindings
    Let(String, RcTerm, RcTerm),
    /// A term that is explicitly annotated with a type
    Ann(RcTerm, RcTerm),

    /// Dependent function types
    FunType(Option<String>, RcTerm, RcTerm),
    /// Introduce a function
    FunIntro(String, RcTerm),
    /// Apply a function to an argument
    FunApp(RcTerm, RcTerm),

    /// Dependent pair types
    PairType(Option<String>, RcTerm, RcTerm),
    /// Introduce a pair
    PairIntro(RcTerm, RcTerm),
    /// Project the first element of a pair
    PairFst(RcTerm),
    /// Project the second element of a pair
    PairSnd(RcTerm),

    /// Universe of types
    Universe(UniverseLevel),
}

impl RcTerm {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        self.inner.to_doc()
    }
}

impl Term {
    /// Convert the term into a pretty-printable document
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        // Using precedence climbing (mirroring the language grammar) in
        // order to cut down on extraneous parentheses.

        fn to_doc_term(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::Ann(term, ann) => Doc::nil()
                    .append(to_doc_expr(&*term.inner))
                    .append(Doc::space())
                    .append(":")
                    .append(Doc::space())
                    .append(to_doc_app(&*ann.inner)),
                _ => to_doc_expr(term),
            }
        }

        fn to_doc_expr(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::Let(name, def, body) => Doc::nil()
                    .append("let")
                    .append(Doc::space())
                    .append(Doc::as_string(name))
                    .append(Doc::space())
                    .append("=")
                    .append(Doc::space())
                    .append(to_doc_app(&*def.inner))
                    .append(Doc::space())
                    .append("in")
                    .append(Doc::space())
                    .append(to_doc_term(&*body.inner)),
                Term::FunType(Some(name), param_ty, body_ty) => Doc::nil()
                    .append(Doc::group(
                        Doc::nil()
                            .append("Fun")
                            .append(Doc::space())
                            .append("(")
                            .append(Doc::as_string(name))
                            .append(Doc::space())
                            .append(":")
                            .append(Doc::space())
                            .append(to_doc_term(&*param_ty.inner))
                            .append(")"),
                    ))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(&*body_ty.inner)),
                Term::FunIntro(_, body) => Doc::nil()
                    .append("fun")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append("=>")
                    .append(Doc::space())
                    .append(to_doc_app(&*body.inner)),
                Term::PairType(_, fst_ty, snd_ty) => Doc::nil()
                    .append("Pair")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append("_")
                    .append(Doc::space())
                    .append(":")
                    .append(to_doc_term(&*fst_ty.inner))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(&*snd_ty.inner))
                    .append(Doc::space())
                    .append("}"),
                Term::PairIntro(fst, snd) => Doc::nil()
                    .append("pair")
                    .append(Doc::space())
                    .append("{")
                    .append(Doc::space())
                    .append(to_doc_term(&*fst.inner))
                    .append(",")
                    .append(Doc::space())
                    .append(to_doc_term(&*snd.inner))
                    .append(Doc::space())
                    .append("}"),
                _ => to_doc_arrow(term),
            }
        }

        fn to_doc_arrow(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::FunType(None, param_ty, body_ty) => Doc::nil()
                    .append(to_doc_app(&*param_ty.inner))
                    .append(Doc::space())
                    .append("->")
                    .append(Doc::space())
                    .append(to_doc_app(&*body_ty.inner)),
                _ => to_doc_app(term),
            }
        }

        fn to_doc_app(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::FunApp(fun, arg) => Doc::nil()
                    .append(to_doc_term(&*fun.inner))
                    .append(Doc::space())
                    .append(to_doc_atomic(&*arg.inner)),
                _ => to_doc_atomic(term),
            }
        }

        fn to_doc_atomic(term: &Term) -> Doc<BoxDoc<()>> {
            match term {
                Term::Var(name) => Doc::as_string(name),
                Term::Literal(Literal::String(value)) => Doc::as_string(value),
                Term::Literal(Literal::Char(value)) => Doc::as_string(value),
                Term::Literal(Literal::Int(value)) => Doc::as_string(value),
                Term::Literal(Literal::Float(value)) => Doc::as_string(value),
                Term::PairFst(pair) => to_doc_atomic(&*pair.inner).append(".1"),
                Term::PairSnd(pair) => to_doc_atomic(&*pair.inner).append(".2"),
                Term::Universe(UniverseLevel(level)) => {
                    Doc::text("Type^").append(Doc::as_string(level))
                },
                _ => Doc::text("(").append(to_doc_term(term)).append(")"),
            }
        }

        to_doc_term(self)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_doc().pretty(100_000).fmt(f)
    }
}
