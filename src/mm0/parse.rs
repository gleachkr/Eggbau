use std::collections::HashSet;

use thiserror::Error;

use super::env::{
    AssertionKind, BinderDecl, CongruenceAnnotation, Formula, MathExpr, MetadataIndex,
    Mm0Diagnostic, Mm0Env, RelationAnnotation, SaturationAnnotation, SaturationMode, SortDecl,
    TermDecl, TheoremDecl,
};

#[derive(Clone, Debug, Eq, PartialEq)]
enum PendingAnnotation {
    Congruence { line: usize },
    Saturation { mode: SaturationMode, line: usize },
}

#[derive(Debug, Error, Eq, PartialEq)]
#[error("MM0 parse error at line {line}: {message}")]
pub struct Mm0ParseError {
    pub line: usize,
    pub message: String,
}

impl Mm0ParseError {
    fn new(line: usize, message: impl Into<String>) -> Self {
        Self {
            line,
            message: message.into(),
        }
    }
}

#[derive(Clone, Debug)]
struct Statement {
    text: String,
    line: usize,
}

pub fn parse_env(input: &str) -> Result<Mm0Env, Mm0ParseError> {
    let mut statements = Vec::new();
    let mut metadata_events = Vec::new();
    collect_statements(input, &mut statements, &mut metadata_events)?;

    let mut env = Mm0Env::default();
    let mut names = NameIndex::default();
    let mut pending = Vec::new();
    let mut events = metadata_events.into_iter().peekable();

    for statement in statements {
        while events
            .peek()
            .is_some_and(|event: &MetadataEvent| event.line <= statement.line)
        {
            let event = events.next().expect("event just peeked");
            handle_metadata_event(event, &mut env, &mut pending)?;
        }

        parse_statement(statement, &mut env, &mut names, &mut pending)?;
    }

    for event in events {
        handle_metadata_event(event, &mut env, &mut pending)?;
    }

    if let Some(annotation) = pending.into_iter().next() {
        let line = match annotation {
            PendingAnnotation::Congruence { line } => line,
            PendingAnnotation::Saturation { line, .. } => line,
        };
        return Err(Mm0ParseError::new(
            line,
            "metadata annotation was not attached to an assertion",
        ));
    }

    Ok(env)
}

fn parse_statement(
    statement: Statement,
    env: &mut Mm0Env,
    names: &mut NameIndex,
    pending: &mut Vec<PendingAnnotation>,
) -> Result<(), Mm0ParseError> {
    let trimmed = statement.text.trim();
    if trimmed.is_empty() {
        return Ok(());
    }

    if let Some(name) = parse_sort_decl(trimmed, statement.line)? {
        require_no_pending(pending, statement.line, "sort declaration")?;
        ensure_unique_sort(&name, names, statement.line)?;
        env.sorts.push(SortDecl { name });
        return Ok(());
    }

    if trimmed.starts_with("term ") || trimmed.starts_with("def ") {
        require_no_pending(pending, statement.line, "term declaration")?;
        let term = parse_term_decl(trimmed, statement.line)?;
        ensure_unique_decl(&term.name, names, statement.line)?;
        env.terms.push(term);
        return Ok(());
    }

    if trimmed.starts_with("theorem ") || trimmed.starts_with("axiom ") {
        let theorem = parse_assertion_decl(trimmed, statement.line)?;
        ensure_unique_decl(&theorem.name, names, statement.line)?;
        attach_pending_metadata(&theorem, pending, &mut env.metadata);
        env.theorems.push(theorem);
        return Ok(());
    }

    if is_notation_directive(trimmed) {
        env.diagnostics.push(Mm0Diagnostic {
            line: statement.line,
            message: format!("unsupported notation directive ignored by eggbau: {trimmed}"),
        });
        return Ok(());
    }

    env.diagnostics.push(Mm0Diagnostic {
        line: statement.line,
        message: format!("unsupported MM0 statement ignored by eggbau: {trimmed}"),
    });
    Ok(())
}

fn parse_term_decl(text: &str, line: usize) -> Result<TermDecl, Mm0ParseError> {
    let after_keyword = text
        .strip_prefix("term ")
        .or_else(|| text.strip_prefix("def "))
        .expect("caller checked term/def prefix")
        .trim();
    let colon = find_top_level_colon(after_keyword)
        .ok_or_else(|| Mm0ParseError::new(line, "term declaration is missing a top-level ':'"))?;
    let (head, ty) = after_keyword.split_at(colon);
    let ty = ty[1..].trim();
    let (name, binders, unsupported_reason) = parse_decl_head(head, line)?;
    let ty = ty.split_once('=').map_or(ty, |(left, _)| left).trim();
    let parts = ty
        .split('>')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(ToOwned::to_owned)
        .collect::<Vec<_>>();

    let Some((result_sort, input_sorts)) = parts.split_last() else {
        return Err(Mm0ParseError::new(
            line,
            "term declaration is missing a result sort",
        ));
    };

    Ok(TermDecl {
        name,
        binders,
        input_sorts: input_sorts.to_vec(),
        result_sort: result_sort.to_owned(),
        unsupported_reason,
    })
}

fn parse_assertion_decl(text: &str, line: usize) -> Result<TheoremDecl, Mm0ParseError> {
    let (kind, rest) = if let Some(rest) = text.strip_prefix("theorem ") {
        (AssertionKind::Theorem, rest)
    } else {
        (
            AssertionKind::Axiom,
            text.strip_prefix("axiom ")
                .expect("caller checked assertion prefix"),
        )
    };

    let colon = find_top_level_colon(rest)
        .ok_or_else(|| Mm0ParseError::new(line, "assertion declaration is missing a ':'"))?;
    let (head, body) = rest.split_at(colon);
    let body = body[1..].trim();
    let (name, binders, mut unsupported_reason) = parse_decl_head(head, line)?;
    let formulas = parse_formula_sequence(body);

    let Some((conclusion, hypotheses)) = formulas.split_last() else {
        return Err(Mm0ParseError::new(
            line,
            "assertion declaration is missing a conclusion formula",
        ));
    };

    let hypotheses = hypotheses.to_vec();
    let conclusion = conclusion.clone();
    if conclusion.unsupported_reason.is_some() && unsupported_reason.is_none() {
        unsupported_reason =
            Some("conclusion formula is outside the supported prefix fragment".to_owned());
    }

    Ok(TheoremDecl {
        name,
        kind,
        binders,
        hypotheses,
        conclusion,
        unsupported_reason,
    })
}

fn parse_decl_head(
    head: &str,
    line: usize,
) -> Result<(String, Vec<BinderDecl>, Option<String>), Mm0ParseError> {
    let head = head.trim();
    let name_end = head
        .char_indices()
        .find(|(_, ch)| ch.is_whitespace() || *ch == '(' || *ch == '{')
        .map_or(head.len(), |(idx, _)| idx);
    let name = head[..name_end].trim();
    ensure_simple_ident(name, line)?;

    let rest = head[name_end..].trim();
    let mut unsupported_reason = None;
    if rest.contains('{') || rest.contains('}') {
        unsupported_reason = Some(
            "bound binders and hidden dependencies are not in eggbau's \
             supported MM0 subset"
                .to_owned(),
        );
    }
    if rest.contains('.') {
        unsupported_reason = Some(
            "hidden dummy dependencies are not in eggbau's supported MM0 \
             subset"
                .to_owned(),
        );
    }

    let (binders, binder_unsupported_reason) = parse_visible_binders(rest, line)?;
    if unsupported_reason.is_none() {
        unsupported_reason = binder_unsupported_reason;
    }
    Ok((name.to_owned(), binders, unsupported_reason))
}

fn parse_visible_binders(
    text: &str,
    line: usize,
) -> Result<(Vec<BinderDecl>, Option<String>), Mm0ParseError> {
    let mut binders = Vec::new();
    let mut unsupported_reason = None;
    let mut idx = 0;
    while let Some(start_rel) = text[idx..].find('(') {
        let start = idx + start_rel;
        let end = text[start + 1..]
            .find(')')
            .map(|end_rel| start + 1 + end_rel)
            .ok_or_else(|| Mm0ParseError::new(line, "unterminated binder group"))?;
        let group = text[start + 1..end].trim();
        let (names, sort) = group
            .split_once(':')
            .ok_or_else(|| Mm0ParseError::new(line, "binder group is missing ':'"))?;
        let mut sort_parts = sort.split_whitespace();
        let Some(sort) = sort_parts.next() else {
            return Err(Mm0ParseError::new(line, "binder group is missing a sort"));
        };
        if sort_parts.next().is_some() {
            unsupported_reason.get_or_insert_with(|| {
                "dependent binder sorts are outside the supported subset".to_owned()
            });
        }
        ensure_simple_ident(sort, line)?;
        for raw_name in names.split_whitespace() {
            let name = if let Some(name) = raw_name.strip_prefix('.') {
                unsupported_reason.get_or_insert_with(|| {
                    "hidden dummy dependencies are not in eggbau's supported MM0 \
                     subset"
                        .to_owned()
                });
                name
            } else {
                raw_name
            };
            ensure_simple_ident(name, line)?;
            binders.push(BinderDecl {
                name: name.to_owned(),
                sort: sort.to_owned(),
            });
        }
        idx = end + 1;
    }

    Ok((binders, unsupported_reason))
}

fn parse_formula_sequence(body: &str) -> Vec<Formula> {
    let mut formulas = Vec::new();
    let mut in_math = false;
    let mut start = 0;

    for (idx, ch) in body.char_indices() {
        if ch == '$' {
            if in_math {
                formulas.push(parse_formula(&body[start..idx]));
            } else {
                start = idx + 1;
            }
            in_math = !in_math;
        }
    }

    if formulas.is_empty() && !body.trim().is_empty() {
        formulas.push(parse_formula(body));
    }

    formulas
}

fn parse_formula(source: &str) -> Formula {
    let source = normalize_ws(source.trim());
    let (expr, unsupported_reason) = parse_math_expr(&source)
        .map(|expr| (Some(expr), None))
        .unwrap_or_else(|reason| (None, Some(reason)));

    Formula {
        source,
        expr,
        unsupported_reason,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MetadataEvent {
    line: usize,
    text: String,
}

fn handle_metadata_event(
    event: MetadataEvent,
    env: &mut Mm0Env,
    pending: &mut Vec<PendingAnnotation>,
) -> Result<(), Mm0ParseError> {
    let text = event.text.trim();
    if !text.starts_with('@') {
        return Ok(());
    }

    let parts = text.split_whitespace().collect::<Vec<_>>();
    match parts.as_slice() {
        ["@relation", sort, relation, refl, trans, sym, transport] => {
            env.metadata.relations.push(RelationAnnotation {
                sort: (*sort).to_owned(),
                relation: (*relation).to_owned(),
                reflexivity: (*refl).to_owned(),
                transitivity: (*trans).to_owned(),
                symmetry: (*sym).to_owned(),
                transport: (*transport != "_").then(|| (*transport).to_owned()),
            });
        }
        ["@congr"] => pending.push(PendingAnnotation::Congruence { line: event.line }),
        ["@saturation", mode] => {
            let mode = SaturationMode::parse(mode).ok_or_else(|| {
                Mm0ParseError::new(event.line, format!("unknown @saturation argument: {mode}"))
            })?;
            pending.push(PendingAnnotation::Saturation {
                mode,
                line: event.line,
            });
        }
        ["@saturation"] => {
            return Err(Mm0ParseError::new(
                event.line,
                "@saturation requires an argument",
            ));
        }
        ["@relation", ..] => {
            return Err(Mm0ParseError::new(
                event.line,
                "@relation requires: sort rel refl trans sym transport",
            ));
        }
        _ => {}
    }

    Ok(())
}

fn attach_pending_metadata(
    theorem: &TheoremDecl,
    pending: &mut Vec<PendingAnnotation>,
    metadata: &mut MetadataIndex,
) {
    for annotation in pending.drain(..) {
        match annotation {
            PendingAnnotation::Congruence { .. } => {
                metadata.congruences.push(CongruenceAnnotation {
                    theorem: theorem.name.clone(),
                });
            }
            PendingAnnotation::Saturation { mode, .. } => {
                metadata.saturations.push(SaturationAnnotation {
                    theorem: theorem.name.clone(),
                    mode,
                });
            }
        }
    }
}

fn require_no_pending(
    pending: &[PendingAnnotation],
    line: usize,
    target: &str,
) -> Result<(), Mm0ParseError> {
    if pending.is_empty() {
        return Ok(());
    }

    Err(Mm0ParseError::new(
        line,
        format!("metadata annotation cannot attach to a {target}"),
    ))
}

fn collect_statements(
    input: &str,
    statements: &mut Vec<Statement>,
    metadata_events: &mut Vec<MetadataEvent>,
) -> Result<(), Mm0ParseError> {
    let mut current = String::new();
    let mut start_line = 1;
    let mut in_math = false;

    for (line_idx, line) in input.lines().enumerate() {
        let line_no = line_idx + 1;
        let trimmed = line.trim_start();
        if trimmed.starts_with("--|") {
            if let Some(text) = trimmed.strip_prefix("--|") {
                metadata_events.push(MetadataEvent {
                    line: line_no,
                    text: text.trim().to_owned(),
                });
            }
            continue;
        }

        let code = strip_line_comment(line);
        if code.trim().is_empty() {
            continue;
        }
        if current.trim().is_empty() {
            start_line = line_no;
        }
        for ch in code.chars() {
            if ch == '$' {
                in_math = !in_math;
            }
            if ch == ';' && !in_math {
                statements.push(Statement {
                    text: current.trim().to_owned(),
                    line: start_line,
                });
                current.clear();
                start_line = line_no;
            } else {
                current.push(ch);
            }
        }
        current.push(' ');
    }

    if in_math {
        return Err(Mm0ParseError::new(
            start_line,
            "unterminated '$' math string",
        ));
    }
    if !current.trim().is_empty() {
        return Err(Mm0ParseError::new(
            start_line,
            "unterminated MM0 statement; missing ';'",
        ));
    }

    Ok(())
}

fn strip_line_comment(line: &str) -> &str {
    let mut in_math = false;
    let mut chars = line.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if ch == '$' {
            in_math = !in_math;
        }
        if ch == '#' && !in_math {
            return &line[..idx];
        }
        if ch == '-' && !in_math && chars.peek().is_some_and(|(_, next)| *next == '-') {
            return &line[..idx];
        }
    }
    line
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

fn ensure_simple_ident(name: &str, line: usize) -> Result<(), Mm0ParseError> {
    if is_simple_ident(name) {
        Ok(())
    } else {
        Err(Mm0ParseError::new(
            line,
            format!("unsupported or invalid identifier: {name}"),
        ))
    }
}

#[derive(Default)]
struct NameIndex {
    sorts: HashSet<String>,
    declarations: HashSet<String>,
}

fn ensure_unique_sort(name: &str, names: &mut NameIndex, line: usize) -> Result<(), Mm0ParseError> {
    ensure_unique_in(name, &mut names.sorts, line)
}

fn ensure_unique_decl(name: &str, names: &mut NameIndex, line: usize) -> Result<(), Mm0ParseError> {
    ensure_unique_in(name, &mut names.declarations, line)
}

fn ensure_unique_in(
    name: &str,
    names: &mut HashSet<String>,
    line: usize,
) -> Result<(), Mm0ParseError> {
    if names.insert(name.to_owned()) {
        Ok(())
    } else {
        Err(Mm0ParseError::new(
            line,
            format!("duplicate declaration name: {name}"),
        ))
    }
}

fn is_simple_ident(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    if name == "_" {
        return false;
    }
    chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn parse_sort_decl(text: &str, line: usize) -> Result<Option<String>, Mm0ParseError> {
    let parts = text.split_whitespace().collect::<Vec<_>>();
    let Some(sort_idx) = parts.iter().position(|part| *part == "sort") else {
        return Ok(None);
    };
    if sort_idx + 2 != parts.len()
        || !parts[..sort_idx]
            .iter()
            .all(|part| matches!(*part, "strict" | "free" | "provable"))
    {
        return Ok(None);
    }

    let name = parts[sort_idx + 1];
    ensure_simple_ident(name, line)?;
    Ok(Some(name.to_owned()))
}

fn is_notation_directive(text: &str) -> bool {
    ["infixl ", "infixr ", "prefix ", "coercion ", "notation "]
        .iter()
        .any(|prefix| text.starts_with(prefix))
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum MathToken {
    Ident(String),
    LParen,
    RParen,
}

fn parse_math_expr(source: &str) -> Result<MathExpr, String> {
    let tokens = tokenize_math(source)?;
    if tokens.is_empty() {
        return Err("empty formula".to_owned());
    }
    parse_math_sequence(&tokens)
}

fn tokenize_math(source: &str) -> Result<Vec<MathToken>, String> {
    let mut tokens = Vec::new();
    let mut chars = source.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if ch.is_whitespace() {
            continue;
        }
        match ch {
            '(' => tokens.push(MathToken::LParen),
            ')' => tokens.push(MathToken::RParen),
            _ if ch == '_' || ch.is_ascii_alphabetic() => {
                let mut end = idx + ch.len_utf8();
                while let Some((next_idx, next)) = chars.peek().copied() {
                    if next == '_' || next.is_ascii_alphanumeric() {
                        chars.next();
                        end = next_idx + next.len_utf8();
                    } else {
                        break;
                    }
                }
                tokens.push(MathToken::Ident(source[idx..end].to_owned()));
            }
            _ => {
                return Err(format!("formula uses unsupported notation token '{ch}'"));
            }
        }
    }
    Ok(tokens)
}

fn parse_math_sequence(tokens: &[MathToken]) -> Result<MathExpr, String> {
    let mut idx = 0;
    let mut items = Vec::new();
    while idx < tokens.len() {
        items.push(parse_math_item(tokens, &mut idx)?);
    }
    match items.as_slice() {
        [] => Err("empty formula".to_owned()),
        [one] => Ok(one.clone()),
        [MathExpr::Atom { name }, args @ ..] => Ok(MathExpr::App {
            head: name.clone(),
            args: args.to_vec(),
        }),
        _ => Err("formula is not a prefix application".to_owned()),
    }
}

fn parse_math_item(tokens: &[MathToken], idx: &mut usize) -> Result<MathExpr, String> {
    match tokens.get(*idx) {
        Some(MathToken::Ident(name)) => {
            *idx += 1;
            Ok(MathExpr::Atom { name: name.clone() })
        }
        Some(MathToken::LParen) => {
            *idx += 1;
            let start = *idx;
            let mut depth = 1_u32;
            while *idx < tokens.len() {
                match tokens[*idx] {
                    MathToken::LParen => depth += 1,
                    MathToken::RParen => {
                        depth -= 1;
                        if depth == 0 {
                            let expr = parse_math_sequence(&tokens[start..*idx])?;
                            *idx += 1;
                            return Ok(expr);
                        }
                    }
                    MathToken::Ident(_) => {}
                }
                *idx += 1;
            }
            Err("unclosed parenthesis in formula".to_owned())
        }
        Some(MathToken::RParen) => Err("unmatched ')' in formula".to_owned()),
        None => Err("unexpected end of formula".to_owned()),
    }
}

#[cfg(test)]
mod tests {
    use super::parse_env;
    use crate::mm0::SaturationMode;

    #[test]
    fn parses_stage_one_fixture_shapes() {
        let input = r#"
sort bv64;
sort wff;
term bv0: bv64;
term bv_add (x y: bv64): bv64;
term bv_eq (x y: bv64): wff;
--| @relation bv64 bv_eq bv_refl bv_trans bv_sym _
--| @congr
axiom bv_add_congr (a b c d: bv64):
  $ bv_eq a b $ > $ bv_eq c d $ >
  $ bv_eq (bv_add a c) (bv_add b d) $;
--| @saturation ltr
theorem bv_add_zero (x: bv64): $ bv_eq (bv_add x bv0) x $;
"#;
        let env = parse_env(input).unwrap();

        assert_eq!(env.sorts.len(), 2);
        assert_eq!(env.terms.len(), 3);
        assert_eq!(env.theorems.len(), 2);
        assert_eq!(env.metadata.relations.len(), 1);
        assert_eq!(env.metadata.congruences[0].theorem, "bv_add_congr");
        assert_eq!(env.metadata.saturations[0].theorem, "bv_add_zero");
        assert_eq!(env.metadata.saturations[0].mode, SaturationMode::Ltr);
        assert_eq!(env.theorem("bv_add_zero").unwrap().binders[0].name, "x");
    }

    #[test]
    fn rejects_unknown_saturation_argument() {
        let input = r#"
sort s;
--| @saturation sideways
theorem t: $ s $;
"#;
        let err = parse_env(input).unwrap_err();

        assert!(err.message.contains("unknown @saturation argument"));
    }

    #[test]
    fn allows_sort_and_term_names_to_overlap() {
        let input = r#"
sort s;
term s: s;
"#;
        let env = parse_env(input).unwrap();

        assert_eq!(env.sorts[0].name, "s");
        assert_eq!(env.terms[0].name, "s");
    }

    #[test]
    fn rejects_saturation_on_non_theorem() {
        let input = r#"
--| @saturation ltr
sort s;
"#;
        let err = parse_env(input).unwrap_err();

        assert!(err.message.contains("cannot attach to a sort declaration"));
    }

    #[test]
    fn marks_bound_binders_unsupported_without_panicking() {
        let input = r#"
sort s;
term p (x: s): s;
theorem t {x: s}: $ p x $;
"#;
        let env = parse_env(input).unwrap();

        assert!(env.theorem("t").unwrap().unsupported_reason.is_some());
    }
}
