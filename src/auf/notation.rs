use std::collections::BTreeMap;

use crate::cert::{Formula, Term};
use crate::mm0::{Mm0Env, NotationAssociativity, NotationDecl, NotationItem, NotationKind};

use super::render::AufRenderError;

#[derive(Clone, Debug)]
pub struct NotationRenderEnv {
    notations: BTreeMap<String, SelectedNotation>,
}

impl NotationRenderEnv {
    pub fn from_mm0(env: &Mm0Env) -> Self {
        let arities = env
            .terms
            .iter()
            .map(|term| {
                let arity = if term.input_sorts.is_empty() {
                    term.binders.len()
                } else {
                    term.input_sorts.len()
                };
                (term.name.as_str(), arity)
            })
            .collect::<BTreeMap<_, _>>();
        let mut notations = BTreeMap::new();
        for notation in &env.notations {
            let Some(term) = notation.term.clone() else {
                continue;
            };
            let arity = arities.get(term.as_str()).copied().unwrap_or(0);
            notations.insert(term, SelectedNotation::from_decl(notation, arity));
        }
        Self { notations }
    }

    pub fn render_formula(&self, formula: &Formula) -> Result<String, AufRenderError> {
        self.render_formula_body(formula)
    }

    pub fn render_term(&self, term: &Term) -> Result<String, AufRenderError> {
        self.render_term_at(term, 0, ChildSide::Only)
            .map(|rendered| rendered.text)
    }

    fn render_formula_body(&self, formula: &Formula) -> Result<String, AufRenderError> {
        match formula {
            Formula::Atom { pred, args } => self.render_head_args(pred, args),
            Formula::Rel { rel, lhs, rhs } => {
                self.render_head_args(rel, &[lhs.clone(), rhs.clone()])
            }
        }
    }

    fn render_head_args(&self, head: &str, args: &[Term]) -> Result<String, AufRenderError> {
        if args.is_empty() {
            return self
                .render_named_nullary(head, 0)
                .map(|rendered| rendered.text);
        }
        let term = Term::App {
            head: head.to_owned(),
            args: args.to_vec(),
        };
        match self.notations.get(head) {
            Some(_) => self.render_term(&term),
            None => self.render_kernel_application(head, args),
        }
    }

    fn render_term_at(
        &self,
        term: &Term,
        min_precedence: u32,
        side: ChildSide,
    ) -> Result<RenderedTerm, AufRenderError> {
        let rendered = match term {
            Term::Var { name } => self.render_named_nullary(name, min_precedence)?,
            Term::App { head, args } if args.is_empty() => {
                self.render_named_nullary(head, min_precedence)?
            }
            Term::App { head, args } => match self.notations.get(head) {
                Some(SelectedNotation::Printable(notation)) => {
                    self.render_notated_application(head, args, notation, min_precedence, side)?
                }
                Some(SelectedNotation::Unsupported { kind, source }) => {
                    return Err(AufRenderError::UnsupportedNotation {
                        term: head.clone(),
                        kind: kind.clone(),
                        declaration: source.clone(),
                    });
                }
                None => RenderedTerm {
                    text: format!("({})", self.render_kernel_application(head, args)?),
                },
            },
            Term::Lit { literal } => {
                return Err(AufRenderError::UnsupportedLiteral {
                    literal: literal.clone(),
                });
            }
        };
        Ok(rendered)
    }

    fn render_named_nullary(
        &self,
        name: &str,
        min_precedence: u32,
    ) -> Result<RenderedTerm, AufRenderError> {
        match self.notations.get(name) {
            Some(SelectedNotation::Printable(notation)) if notation.arity() == 0 => {
                let rendered = self.render_notated_application(
                    name,
                    &[],
                    notation,
                    min_precedence,
                    ChildSide::Only,
                )?;
                Ok(rendered)
            }
            Some(SelectedNotation::Unsupported { kind, source }) => {
                Err(AufRenderError::UnsupportedNotation {
                    term: name.to_owned(),
                    kind: kind.clone(),
                    declaration: source.clone(),
                })
            }
            Some(SelectedNotation::Printable(_)) | None => Ok(RenderedTerm {
                text: name.to_owned(),
            }),
        }
    }

    fn render_notated_application(
        &self,
        head: &str,
        args: &[Term],
        notation: &PrintableNotation,
        min_precedence: u32,
        side: ChildSide,
    ) -> Result<RenderedTerm, AufRenderError> {
        if args.len() != notation.arity() {
            return Ok(RenderedTerm {
                text: format!("({})", self.render_kernel_application(head, args)?),
            });
        }

        let text = match notation {
            PrintableNotation::Prefix {
                token, precedence, ..
            } => self.render_prefix(token, *precedence, args)?,
            PrintableNotation::Infix {
                token,
                precedence,
                associativity,
            } => self.render_infix(token, *precedence, *associativity, args)?,
            PrintableNotation::General(general) => self.render_general(general, args)?,
        };
        let precedence = notation.precedence();
        let text = if needs_parentheses(precedence, notation.associativity(), min_precedence, side)
        {
            format!("({text})")
        } else {
            text
        };
        Ok(RenderedTerm { text })
    }

    fn render_prefix(
        &self,
        token: &str,
        precedence: u32,
        args: &[Term],
    ) -> Result<String, AufRenderError> {
        if args.is_empty() {
            return Ok(token.to_owned());
        }
        let mut parts = Vec::with_capacity(args.len() + 1);
        parts.push(token.to_owned());
        for (idx, arg) in args.iter().enumerate() {
            let required = if idx + 1 == args.len() {
                precedence
            } else {
                u32::MAX
            };
            parts.push(self.render_term_at(arg, required, ChildSide::Only)?.text);
        }
        Ok(parts.join(" "))
    }

    fn render_infix(
        &self,
        token: &str,
        precedence: u32,
        associativity: NotationAssociativity,
        args: &[Term],
    ) -> Result<String, AufRenderError> {
        let [lhs, rhs] = args else {
            return Ok(String::new());
        };
        let lhs_min = match associativity {
            NotationAssociativity::Left => precedence,
            NotationAssociativity::Right => precedence.saturating_add(1),
        };
        let rhs_min = match associativity {
            NotationAssociativity::Left => precedence.saturating_add(1),
            NotationAssociativity::Right => precedence,
        };
        let lhs = self.render_term_at(lhs, lhs_min, ChildSide::Left)?.text;
        let rhs = self.render_term_at(rhs, rhs_min, ChildSide::Right)?.text;
        Ok(format!("{lhs} {token} {rhs}"))
    }

    fn render_general(
        &self,
        notation: &GeneralNotation,
        args: &[Term],
    ) -> Result<String, AufRenderError> {
        let mut parts = Vec::new();
        for (idx, item) in notation.items.iter().enumerate() {
            match item {
                GeneralItem::Const { token, .. } => parts.push(token.clone()),
                GeneralItem::Var { arg_index } => {
                    let precedence = notation.variable_precedence(idx);
                    parts.push(
                        self.render_term_at(&args[*arg_index], precedence, ChildSide::Only)?
                            .text,
                    );
                }
            }
        }
        Ok(parts.join(" "))
    }

    fn render_kernel_application(
        &self,
        head: &str,
        args: &[Term],
    ) -> Result<String, AufRenderError> {
        if args.is_empty() {
            return Ok(head.to_owned());
        }
        let args = args
            .iter()
            .map(|term| {
                self.render_term_at(term, 0, ChildSide::Only)
                    .map(|rendered| render_kernel_argument(term, rendered.text))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("{} {}", head, args.join(" ")))
    }
}

fn render_kernel_argument(term: &Term, rendered: String) -> String {
    match term {
        Term::Var { .. } => rendered,
        Term::App { args, .. } if args.is_empty() => rendered,
        Term::App { .. } | Term::Lit { .. } => format!("({rendered})"),
    }
}

#[derive(Clone, Debug)]
enum SelectedNotation {
    Printable(PrintableNotation),
    Unsupported { kind: String, source: String },
}

impl SelectedNotation {
    fn from_decl(decl: &NotationDecl, arity: usize) -> Self {
        match decl.kind {
            NotationKind::Prefix => decl
                .tokens
                .first()
                .map(|token| {
                    Self::Printable(PrintableNotation::Prefix {
                        token: token.clone(),
                        precedence: notation_precedence(decl),
                        arity,
                    })
                })
                .unwrap_or_else(|| unsupported(decl)),
            NotationKind::Infixl | NotationKind::Infixr => decl
                .tokens
                .first()
                .map(|token| {
                    Self::Printable(PrintableNotation::Infix {
                        token: token.clone(),
                        precedence: notation_precedence(decl),
                        associativity: if decl.kind == NotationKind::Infixr {
                            NotationAssociativity::Right
                        } else {
                            NotationAssociativity::Left
                        },
                    })
                })
                .unwrap_or_else(|| unsupported(decl)),
            NotationKind::General => match GeneralNotation::from_decl(decl) {
                Some(general) => Self::Printable(PrintableNotation::General(general)),
                None => unsupported(decl),
            },
            NotationKind::Delimiter | NotationKind::Coercion => unsupported(decl),
        }
    }
}

fn unsupported(decl: &NotationDecl) -> SelectedNotation {
    SelectedNotation::Unsupported {
        kind: format!("{:?}", decl.kind),
        source: decl.source.clone(),
    }
}

#[derive(Clone, Debug)]
enum PrintableNotation {
    Prefix {
        token: String,
        precedence: u32,
        arity: usize,
    },
    Infix {
        token: String,
        precedence: u32,
        associativity: NotationAssociativity,
    },
    General(GeneralNotation),
}

impl PrintableNotation {
    fn precedence(&self) -> u32 {
        match self {
            Self::Prefix { precedence, .. }
            | Self::Infix { precedence, .. }
            | Self::General(GeneralNotation { precedence, .. }) => *precedence,
        }
    }

    fn associativity(&self) -> Option<NotationAssociativity> {
        match self {
            Self::Infix { associativity, .. } => Some(*associativity),
            Self::General(GeneralNotation { associativity, .. }) => *associativity,
            Self::Prefix { .. } => None,
        }
    }

    fn arity(&self) -> usize {
        match self {
            Self::Prefix { arity, .. } => *arity,
            Self::Infix { .. } => 2,
            Self::General(general) => general.arity,
        }
    }
}

#[derive(Clone, Debug)]
struct GeneralNotation {
    items: Vec<GeneralItem>,
    precedence: u32,
    associativity: Option<NotationAssociativity>,
    is_infix: bool,
    arity: usize,
}

impl GeneralNotation {
    fn from_decl(decl: &NotationDecl) -> Option<Self> {
        let var_names = general_arg_names(decl);
        let arg_by_name = var_names
            .iter()
            .enumerate()
            .map(|(idx, name)| (name.clone(), idx))
            .collect::<BTreeMap<_, _>>();
        let mut items = Vec::new();
        for item in &decl.items {
            match item {
                NotationItem::Const { token, precedence } => items.push(GeneralItem::Const {
                    token: token.clone(),
                    precedence: precedence
                        .as_deref()
                        .and_then(parse_precedence_value)
                        .unwrap_or(100),
                }),
                NotationItem::Var { name } => {
                    let arg_index = *arg_by_name.get(name)?;
                    items.push(GeneralItem::Var { arg_index });
                }
            }
        }
        let is_infix = matches!(
            items.as_slice(),
            [GeneralItem::Var { .. }, GeneralItem::Const { .. }, ..]
        );
        let is_prefix = matches!(items.first(), Some(GeneralItem::Const { .. }));
        if !is_infix && !is_prefix {
            return None;
        }
        Some(Self {
            items,
            precedence: notation_precedence(decl),
            associativity: decl.associativity,
            is_infix,
            arity: var_names.len(),
        })
    }

    fn variable_precedence(&self, idx: usize) -> u32 {
        if let Some(next) = self.items[idx + 1..].iter().find_map(|item| match item {
            GeneralItem::Const { precedence, .. } => Some(*precedence),
            GeneralItem::Var { .. } => None,
        }) {
            return next.saturating_add(1);
        }
        if self.is_infix {
            return match self.associativity {
                Some(NotationAssociativity::Right) => self.precedence,
                Some(NotationAssociativity::Left) | None => self.precedence.saturating_add(1),
            };
        }
        0
    }
}

#[derive(Clone, Debug)]
enum GeneralItem {
    Const { token: String, precedence: u32 },
    Var { arg_index: usize },
}

#[derive(Clone, Debug)]
struct RenderedTerm {
    text: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ChildSide {
    Left,
    Right,
    Only,
}

fn needs_parentheses(
    precedence: u32,
    associativity: Option<NotationAssociativity>,
    min_precedence: u32,
    side: ChildSide,
) -> bool {
    if precedence < min_precedence {
        return true;
    }
    if precedence > min_precedence {
        return false;
    }
    matches!(
        (associativity, side),
        (Some(NotationAssociativity::Left), ChildSide::Right)
            | (Some(NotationAssociativity::Right), ChildSide::Left)
    )
}

fn notation_precedence(notation: &NotationDecl) -> u32 {
    notation
        .precedence
        .as_deref()
        .and_then(parse_precedence_value)
        .unwrap_or(100)
}

fn parse_precedence_value(precedence: &str) -> Option<u32> {
    match precedence {
        "max" => Some(u32::MAX),
        token => token.parse::<u32>().ok(),
    }
}

fn general_arg_names(decl: &NotationDecl) -> Vec<String> {
    let mut names = visible_names_from_notation_head(&decl.source);
    if names.is_empty() {
        for item in &decl.items {
            if let NotationItem::Var { name } = item
                && !names.contains(name)
            {
                names.push(name.clone());
            }
        }
    }
    names
}

fn visible_names_from_notation_head(source: &str) -> Vec<String> {
    let Some(rest) = source.strip_prefix("notation ") else {
        return Vec::new();
    };
    let head = rest.split_once('=').map_or(rest, |(head, _)| head);
    let Some(colon) = find_top_level_colon(head) else {
        return Vec::new();
    };
    let head = &head[..colon];
    let mut names = Vec::new();
    let mut idx = 0;
    while let Some(start_rel) = head[idx..].find('(') {
        let start = idx + start_rel;
        let Some(end_rel) = head[start + 1..].find(')') else {
            break;
        };
        let end = start + 1 + end_rel;
        if let Some((raw_names, _)) = head[start + 1..end].split_once(':') {
            names.extend(
                raw_names
                    .split_whitespace()
                    .map(|name| name.strip_prefix('.').unwrap_or(name).to_owned()),
            );
        }
        idx = end + 1;
    }
    names
}

fn find_top_level_colon(text: &str) -> Option<usize> {
    let mut depth = 0_u32;
    for (idx, ch) in text.char_indices() {
        match ch {
            '(' | '{' => depth += 1,
            ')' | '}' => depth = depth.saturating_sub(1),
            ':' if depth == 0 => return Some(idx),
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::NotationRenderEnv;
    use crate::cert::{Formula, Term};
    use crate::mm0::parse_env;

    fn env(input: &str) -> NotationRenderEnv {
        NotationRenderEnv::from_mm0(&parse_env(input).unwrap())
    }

    #[test]
    fn renders_simple_infix_relation() {
        let printer = env(r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
infixl eq: $=$ prec 10;
"#);
        let formula = Formula::rel("eq", Term::var("x"), Term::var("y"));

        assert_eq!(printer.render_formula(&formula).unwrap(), "x = y");
    }

    #[test]
    fn renders_simple_prefix() {
        let printer = env(r#"
provable sort wff;
term not (x: wff): wff;
prefix not: $¬$ prec 80;
"#);
        let formula = Formula::atom("not", vec![Term::var("p")]);

        assert_eq!(printer.render_formula(&formula).unwrap(), "¬ p");
    }

    #[test]
    fn parenthesizes_infix_associativity() {
        let printer = env(r#"
sort s;
term add (x y: s): s;
infixl add: $+$ prec 50;
"#);
        let left = Term::app(
            "add",
            vec![
                Term::app("add", vec![Term::var("a"), Term::var("b")]),
                Term::var("c"),
            ],
        );
        let right = Term::app(
            "add",
            vec![
                Term::var("a"),
                Term::app("add", vec![Term::var("b"), Term::var("c")]),
            ],
        );

        assert_eq!(printer.render_term(&left).unwrap(), "a + b + c");
        assert_eq!(printer.render_term(&right).unwrap(), "a + (b + c)");
    }

    #[test]
    fn parenthesizes_notated_terms_in_kernel_applications() {
        let printer = env(r#"
sort s;
provable sort wff;
term add (x y: s): s;
term eq (x y: s): wff;
infixl add: $+$ prec 50;
"#);
        let formula = Formula::rel(
            "eq",
            Term::app("add", vec![Term::var("x"), Term::var("y")]),
            Term::var("z"),
        );

        assert_eq!(printer.render_formula(&formula).unwrap(), "eq (x + y) z");
    }

    #[test]
    fn renders_general_prefix() {
        let printer = env(r#"
sort s;
term wrap (x y: s): s;
notation wrap (x y: s): s = ($<$:60) x ($:$:40) y ($>$:0);
"#);
        let term = Term::app("wrap", vec![Term::var("a"), Term::var("b")]);

        assert_eq!(printer.render_term(&term).unwrap(), "< a : b >");
    }

    #[test]
    fn renders_general_infix() {
        let printer = env(r#"
sort s;
term triple (x y z: s): s;
notation triple (x y z: s): s = x ($<+>$:30) y ($//$:30) z : 30 lassoc;
"#);
        let term = Term::app(
            "triple",
            vec![Term::var("a"), Term::var("b"), Term::var("c")],
        );

        assert_eq!(printer.render_term(&term).unwrap(), "a <+> b // c");
    }

    #[test]
    fn last_notation_wins() {
        let printer = env(r#"
sort s;
term add (x y: s): s;
infixl add: $+$ prec 50;
infixl add: $⊕$ prec 50;
"#);
        let term = Term::app("add", vec![Term::var("a"), Term::var("b")]);

        assert_eq!(printer.render_term(&term).unwrap(), "a ⊕ b");
    }
}
