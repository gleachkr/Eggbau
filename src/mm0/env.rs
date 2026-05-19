use std::fmt;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct Mm0Env {
    pub sorts: Vec<SortDecl>,
    pub terms: Vec<TermDecl>,
    pub theorems: Vec<TheoremDecl>,
    pub notations: Vec<NotationDecl>,
    pub metadata: MetadataIndex,
    pub diagnostics: Vec<Mm0Diagnostic>,
}

impl Mm0Env {
    pub fn theorem(&self, name: &str) -> Option<&TheoremDecl> {
        self.theorems.iter().find(|theorem| theorem.name == name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SortDecl {
    pub name: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct TermDecl {
    pub name: String,
    pub binders: Vec<BinderDecl>,
    pub input_sorts: Vec<String>,
    pub result_sort: String,
    pub unsupported_reason: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct TheoremDecl {
    pub name: String,
    pub kind: AssertionKind,
    pub binders: Vec<BinderDecl>,
    pub hypotheses: Vec<Formula>,
    pub conclusion: Formula,
    pub unsupported_reason: Option<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AssertionKind {
    Axiom,
    Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct BinderDecl {
    pub name: String,
    pub sort: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Formula {
    pub source: String,
    pub expr: Option<MathExpr>,
    pub unsupported_reason: Option<String>,
}

impl Formula {
    pub fn head(&self) -> Option<&str> {
        match self.expr.as_ref()? {
            MathExpr::Atom { name } => Some(name),
            MathExpr::App { head, .. } => Some(head),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum MathExpr {
    Atom { name: String },
    App { head: String, args: Vec<MathExpr> },
}

impl MathExpr {
    pub fn head(&self) -> &str {
        match self {
            Self::Atom { name } => name,
            Self::App { head, .. } => head,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct MetadataIndex {
    pub relations: Vec<RelationAnnotation>,
    pub congruences: Vec<CongruenceAnnotation>,
    pub saturations: Vec<SaturationAnnotation>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct RelationAnnotation {
    pub sort: String,
    pub relation: String,
    pub reflexivity: String,
    pub transitivity: String,
    pub symmetry: String,
    pub transport: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CongruenceAnnotation {
    pub theorem: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SaturationAnnotation {
    pub theorem: String,
    pub mode: SaturationMode,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SaturationMode {
    Ltr,
    Rtl,
    Both,
    Horn,
}

impl SaturationMode {
    pub(crate) fn parse(token: &str) -> Option<Self> {
        match token {
            "ltr" | "left-to-right" => Some(Self::Ltr),
            "rtl" | "right-to-left" => Some(Self::Rtl),
            "both" | "bidirectional" => Some(Self::Both),
            "horn" => Some(Self::Horn),
            _ => None,
        }
    }
}

impl fmt::Display for SaturationMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ltr => f.write_str("ltr"),
            Self::Rtl => f.write_str("rtl"),
            Self::Both => f.write_str("both"),
            Self::Horn => f.write_str("horn"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct NotationDecl {
    pub kind: NotationKind,
    pub term: Option<String>,
    pub tokens: Vec<String>,
    pub precedence: Option<String>,
    pub associativity: Option<NotationAssociativity>,
    pub items: Vec<NotationItem>,
    pub source: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NotationKind {
    Delimiter,
    Prefix,
    Infixl,
    Infixr,
    General,
    Coercion,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NotationAssociativity {
    Left,
    Right,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum NotationItem {
    Const {
        token: String,
        precedence: Option<String>,
    },
    Var {
        name: String,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Mm0Diagnostic {
    pub line: usize,
    pub message: String,
}
