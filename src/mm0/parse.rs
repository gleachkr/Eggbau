use std::collections::{HashMap, HashSet};

use thiserror::Error;

use super::env::{
    AssertionKind, BinderDecl, CongruenceAnnotation, Formula, MathExpr, MetadataIndex,
    Mm0Diagnostic, Mm0Env, NotationAssociativity, NotationDecl, NotationItem, NotationKind,
    RelationAnnotation, SaturationAnnotation, SaturationMode, SortDecl, TermDecl, TheoremDecl,
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

/// Parse an Aufbau local lemma header against an already parsed MM0
/// environment.
///
/// `header` is the text after the `lemma` keyword, for example
/// `local_id (x: s): $ eq x x $`. The returned declaration is theorem-like
/// so the existing proof-search and rendering pipeline can reuse it, but it
/// is not inserted into the environment or exported as a saturation rule.
pub fn parse_local_lemma_header(env: &Mm0Env, header: &str) -> Result<TheoremDecl, Mm0ParseError> {
    let text = format!("theorem {}", header.trim());
    let mut theorem = parse_assertion_decl(&text, 1, env)?;
    theorem.kind = AssertionKind::Theorem;
    Ok(theorem)
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

    if let Some(sort) = parse_sort_decl(trimmed, statement.line)? {
        require_no_pending(pending, statement.line, "sort declaration")?;
        ensure_unique_sort(&sort.name, names, statement.line)?;
        env.sorts.push(sort);
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
        let theorem = parse_assertion_decl(trimmed, statement.line, env)?;
        ensure_unique_decl(&theorem.name, names, statement.line)?;
        attach_pending_metadata(&theorem, pending, &mut env.metadata);
        env.theorems.push(theorem);
        return Ok(());
    }

    if let Some(notation) = parse_notation_decl(trimmed, statement.line)? {
        require_no_pending(pending, statement.line, "notation directive")?;
        env.notations.push(notation);
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

fn parse_assertion_decl(
    text: &str,
    line: usize,
    env: &Mm0Env,
) -> Result<TheoremDecl, Mm0ParseError> {
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
    let context = FormulaContext::from_env(env);
    let formulas = parse_formula_sequence(body, &context);

    let Some((conclusion, hypotheses)) = formulas.split_last() else {
        return Err(Mm0ParseError::new(
            line,
            "assertion declaration is missing a conclusion formula",
        ));
    };

    let hypotheses = hypotheses.to_vec();
    let conclusion = conclusion.clone();
    if formulas
        .iter()
        .any(|formula| formula.unsupported_reason.is_some())
        && unsupported_reason.is_none()
    {
        unsupported_reason =
            Some("one or more formulas are outside eggbau's supported fragment".to_owned());
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

fn parse_formula_sequence(body: &str, context: &FormulaContext) -> Vec<Formula> {
    let mut formulas = Vec::new();
    let mut in_math = false;
    let mut start = 0;

    for (idx, ch) in body.char_indices() {
        if ch == '$' {
            if in_math {
                formulas.push(parse_formula(&body[start..idx], context));
            } else {
                start = idx + 1;
            }
            in_math = !in_math;
        }
    }

    if formulas.is_empty() && !body.trim().is_empty() {
        formulas.push(parse_formula(body, context));
    }

    formulas
}

fn parse_formula(source: &str, context: &FormulaContext) -> Formula {
    let source = normalize_ws(source.trim());
    let (expr, unsupported_reason) = parse_math_expr(&source, context)
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

fn parse_sort_decl(text: &str, line: usize) -> Result<Option<SortDecl>, Mm0ParseError> {
    let parts = text.split_whitespace().collect::<Vec<_>>();
    let Some(sort_idx) = parts.iter().position(|part| *part == "sort") else {
        return Ok(None);
    };
    if sort_idx + 2 != parts.len()
        || !parts[..sort_idx]
            .iter()
            .all(|part| matches!(*part, "pure" | "strict" | "free" | "provable"))
    {
        return Ok(None);
    }

    let name = parts[sort_idx + 1];
    ensure_simple_ident(name, line)?;
    Ok(Some(SortDecl {
        name: name.to_owned(),
        provable: parts[..sort_idx].contains(&"provable"),
    }))
}

fn parse_notation_decl(text: &str, line: usize) -> Result<Option<NotationDecl>, Mm0ParseError> {
    if let Some(rest) = text.strip_prefix("delimiter ") {
        let tokens = extract_math_tokens(rest);
        let items = tokens
            .iter()
            .map(|token| NotationItem::Const {
                token: token.clone(),
                precedence: None,
            })
            .collect();
        return Ok(Some(NotationDecl {
            kind: NotationKind::Delimiter,
            term: None,
            tokens,
            precedence: None,
            associativity: None,
            items,
            source: text.to_owned(),
        }));
    }

    for (prefix, kind, assoc) in [
        ("prefix ", NotationKind::Prefix, None),
        (
            "infixl ",
            NotationKind::Infixl,
            Some(NotationAssociativity::Left),
        ),
        (
            "infixr ",
            NotationKind::Infixr,
            Some(NotationAssociativity::Right),
        ),
    ] {
        if let Some(rest) = text.strip_prefix(prefix) {
            let (term, rest) = rest
                .split_once(':')
                .ok_or_else(|| Mm0ParseError::new(line, "notation directive is missing ':'"))?;
            let term = term.trim();
            ensure_simple_ident(term, line)?;
            let tokens = extract_math_tokens(rest);
            let Some(token) = tokens.first() else {
                return Err(Mm0ParseError::new(
                    line,
                    "notation directive is missing a token",
                ));
            };
            let precedence = parse_precedence(rest);
            return Ok(Some(NotationDecl {
                kind,
                term: Some(term.to_owned()),
                tokens: vec![token.clone()],
                precedence: precedence.clone(),
                associativity: assoc,
                items: vec![NotationItem::Const {
                    token: token.clone(),
                    precedence,
                }],
                source: text.to_owned(),
            }));
        }
    }

    if let Some(rest) = text.strip_prefix("coercion ") {
        let (term, _) = rest
            .split_once(':')
            .ok_or_else(|| Mm0ParseError::new(line, "coercion directive is missing ':'"))?;
        let term = term.trim();
        ensure_simple_ident(term, line)?;
        return Ok(Some(NotationDecl {
            kind: NotationKind::Coercion,
            term: Some(term.to_owned()),
            tokens: Vec::new(),
            precedence: None,
            associativity: None,
            items: Vec::new(),
            source: text.to_owned(),
        }));
    }

    if let Some(rest) = text.strip_prefix("notation ") {
        let name_end = rest
            .char_indices()
            .find(|(_, ch)| ch.is_whitespace() || *ch == '(' || *ch == '{' || *ch == ':')
            .map_or(rest.len(), |(idx, _)| idx);
        let term = rest[..name_end].trim();
        ensure_simple_ident(term, line)?;
        let Some((_, rhs)) = text.split_once('=') else {
            return Err(Mm0ParseError::new(
                line,
                "notation directive is missing '='",
            ));
        };
        let (rhs, precedence, associativity) = split_general_notation_rhs(rhs, line)?;
        let items = parse_general_notation_items(rhs, line)?;
        let tokens = items
            .iter()
            .filter_map(|item| match item {
                NotationItem::Const { token, .. } => Some(token.clone()),
                NotationItem::Var { .. } => None,
            })
            .collect();
        return Ok(Some(NotationDecl {
            kind: NotationKind::General,
            term: Some(term.to_owned()),
            tokens,
            precedence,
            associativity,
            items,
            source: text.to_owned(),
        }));
    }

    Ok(None)
}

fn split_general_notation_rhs(
    rhs: &str,
    line: usize,
) -> Result<(&str, Option<String>, Option<NotationAssociativity>), Mm0ParseError> {
    let Some(colon) = find_general_notation_prec_colon(rhs) else {
        return Ok((rhs.trim(), None, None));
    };
    let (literals, suffix) = rhs.split_at(colon);
    let mut parts = suffix[1..].split_whitespace();
    let Some(precedence) = parts.next() else {
        return Err(Mm0ParseError::new(
            line,
            "general notation precedence is missing",
        ));
    };
    let associativity = match parts.next() {
        Some("lassoc") => Some(NotationAssociativity::Left),
        Some("rassoc") => Some(NotationAssociativity::Right),
        Some(other) => {
            return Err(Mm0ParseError::new(
                line,
                format!("unknown general notation associativity: {other}"),
            ));
        }
        None => None,
    };
    Ok((literals.trim(), Some(precedence.to_owned()), associativity))
}

fn find_general_notation_prec_colon(text: &str) -> Option<usize> {
    let mut in_math = false;
    let mut depth = 0_u32;
    for (idx, ch) in text.char_indices() {
        match ch {
            '$' => in_math = !in_math,
            '(' if !in_math => depth += 1,
            ')' if !in_math => depth = depth.saturating_sub(1),
            ':' if !in_math && depth == 0 => return Some(idx),
            _ => {}
        }
    }
    None
}

fn parse_general_notation_items(
    text: &str,
    line: usize,
) -> Result<Vec<NotationItem>, Mm0ParseError> {
    let mut items = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some((idx, ch)) = chars.peek().copied() {
        if ch.is_whitespace() {
            chars.next();
            continue;
        }
        if ch == '(' {
            chars.next();
            skip_ws(&mut chars);
            let Some((_, '$')) = chars.peek().copied() else {
                return Err(Mm0ParseError::new(
                    line,
                    "notation constant must start with '$'",
                ));
            };
            chars.next();
            let start = chars.peek().map_or(idx + ch.len_utf8(), |(idx, _)| *idx);
            let Some((end, _)) = chars.by_ref().find(|(_, next)| *next == '$') else {
                return Err(Mm0ParseError::new(line, "unterminated notation constant"));
            };
            let token = text[start..end].trim().to_owned();
            skip_ws(&mut chars);
            let precedence = if chars.peek().is_some_and(|(_, next)| *next == ':') {
                chars.next();
                skip_ws(&mut chars);
                let start = chars.peek().map_or(end, |(idx, _)| *idx);
                let mut finish = start;
                while let Some((next_idx, next)) = chars.peek().copied() {
                    if next.is_whitespace() || next == ')' {
                        break;
                    }
                    chars.next();
                    finish = next_idx + next.len_utf8();
                }
                Some(text[start..finish].to_owned())
            } else {
                None
            };
            skip_ws(&mut chars);
            match chars.next() {
                Some((_, ')')) => {}
                _ => {
                    return Err(Mm0ParseError::new(line, "notation constant is missing ')'"));
                }
            }
            items.push(NotationItem::Const { token, precedence });
            continue;
        }

        if ch == '_' || ch.is_ascii_alphabetic() {
            let start = idx;
            let mut end = idx + ch.len_utf8();
            chars.next();
            while let Some((next_idx, next)) = chars.peek().copied() {
                if next == '_' || next.is_ascii_alphanumeric() {
                    chars.next();
                    end = next_idx + next.len_utf8();
                } else {
                    break;
                }
            }
            items.push(NotationItem::Var {
                name: text[start..end].to_owned(),
            });
            continue;
        }

        return Err(Mm0ParseError::new(
            line,
            format!("unexpected token in notation pattern: {ch}"),
        ));
    }
    Ok(items)
}

fn skip_ws(chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>) {
    while chars.peek().is_some_and(|(_, ch)| ch.is_whitespace()) {
        chars.next();
    }
}

fn extract_math_tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut in_math = false;
    let mut start = 0;
    for (idx, ch) in text.char_indices() {
        if ch == '$' {
            if in_math {
                let token = text[start..idx].trim();
                if !token.is_empty() {
                    tokens.push(token.to_owned());
                }
            } else {
                start = idx + 1;
            }
            in_math = !in_math;
        }
    }
    tokens
}

fn parse_precedence(text: &str) -> Option<String> {
    text.split_once("prec")
        .and_then(|(_, rest)| rest.split_whitespace().next())
        .map(ToOwned::to_owned)
}

fn normalize_ws(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[derive(Clone, Debug)]
struct FormulaContext {
    terms: HashMap<String, usize>,
    prefixes: HashMap<String, PrefixNotation>,
    infixes: HashMap<String, InfixNotation>,
    prefix_generals: HashMap<String, Vec<GeneralNotation>>,
    infix_generals: HashMap<String, Vec<GeneralNotation>>,
}

impl FormulaContext {
    fn from_env(env: &Mm0Env) -> Self {
        let terms = env
            .terms
            .iter()
            .map(|term| (term.name.clone(), term_arity(term)))
            .collect::<HashMap<_, _>>();
        let term_args = env
            .terms
            .iter()
            .map(|term| {
                let args = term
                    .binders
                    .iter()
                    .map(|binder| binder.name.clone())
                    .collect::<Vec<_>>();
                (term.name.clone(), args)
            })
            .collect::<HashMap<_, _>>();
        let mut prefixes = HashMap::new();
        let mut infixes = HashMap::new();
        let mut prefix_generals: HashMap<String, Vec<GeneralNotation>> = HashMap::new();
        let mut infix_generals: HashMap<String, Vec<GeneralNotation>> = HashMap::new();

        for notation in &env.notations {
            let Some(term) = notation.term.clone() else {
                continue;
            };
            let arity = terms.get(&term).copied().unwrap_or(0);
            match notation.kind {
                NotationKind::Prefix => {
                    let Some(token) = notation.tokens.first().cloned() else {
                        continue;
                    };
                    prefixes.insert(
                        token,
                        PrefixNotation {
                            term,
                            arity,
                            precedence: notation_precedence(notation),
                        },
                    );
                }
                NotationKind::Infixl => {
                    let Some(token) = notation.tokens.first().cloned() else {
                        continue;
                    };
                    infixes.insert(
                        token,
                        InfixNotation {
                            term,
                            precedence: notation_precedence(notation),
                            associativity: Associativity::Left,
                        },
                    );
                }
                NotationKind::Infixr => {
                    let Some(token) = notation.tokens.first().cloned() else {
                        continue;
                    };
                    infixes.insert(
                        token,
                        InfixNotation {
                            term,
                            precedence: notation_precedence(notation),
                            associativity: Associativity::Right,
                        },
                    );
                }
                NotationKind::General => {
                    let Some(general) = general_notation_from_decl(notation, &term_args) else {
                        continue;
                    };
                    match general.lead.clone() {
                        GeneralNotationLead::Prefix { token } => {
                            prefix_generals.entry(token).or_default().push(general);
                        }
                        GeneralNotationLead::Infix { token, .. } => {
                            infix_generals.entry(token).or_default().push(general);
                        }
                    }
                }
                NotationKind::Delimiter | NotationKind::Coercion => {}
            }
        }

        Self {
            terms,
            prefixes,
            infixes,
            prefix_generals,
            infix_generals,
        }
    }
}

fn term_arity(term: &TermDecl) -> usize {
    if term.input_sorts.is_empty() {
        term.binders.len()
    } else {
        term.input_sorts.len()
    }
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

fn general_notation_from_decl(
    notation: &NotationDecl,
    term_args: &HashMap<String, Vec<String>>,
) -> Option<GeneralNotation> {
    let term = notation.term.clone()?;
    if notation.items.is_empty() {
        return None;
    }
    let args = term_args
        .get(&term)
        .filter(|args| !args.is_empty())
        .cloned()
        .unwrap_or_else(|| visible_names_from_notation_head(&notation.source));
    let pattern = notation
        .items
        .iter()
        .map(|item| match item {
            NotationItem::Const { token, precedence } => GeneralPatternItem::Literal {
                token: token.clone(),
                precedence: precedence
                    .as_deref()
                    .and_then(parse_precedence_value)
                    .unwrap_or(100),
            },
            NotationItem::Var { name } => GeneralPatternItem::Variable(name.clone()),
        })
        .collect::<Vec<_>>();
    let lead = general_notation_lead(notation)?;
    Some(GeneralNotation {
        term,
        pattern,
        args,
        lead,
        precedence: notation_precedence(notation),
        associativity: notation.associativity,
    })
}

fn general_notation_lead(notation: &NotationDecl) -> Option<GeneralNotationLead> {
    match notation.items.as_slice() {
        [NotationItem::Const { token, .. }, ..] => Some(GeneralNotationLead::Prefix {
            token: token.clone(),
        }),
        [
            NotationItem::Var { name },
            NotationItem::Const { token, .. },
            ..,
        ] => Some(GeneralNotationLead::Infix {
            lhs: name.clone(),
            token: token.clone(),
        }),
        _ => None,
    }
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

#[derive(Clone, Debug)]
struct PrefixNotation {
    term: String,
    arity: usize,
    precedence: u32,
}

#[derive(Clone, Debug)]
struct InfixNotation {
    term: String,
    precedence: u32,
    associativity: Associativity,
}

#[derive(Clone, Debug)]
struct GeneralNotation {
    term: String,
    pattern: Vec<GeneralPatternItem>,
    args: Vec<String>,
    lead: GeneralNotationLead,
    precedence: u32,
    associativity: Option<NotationAssociativity>,
}

#[derive(Clone, Debug)]
enum GeneralNotationLead {
    Prefix { token: String },
    Infix { lhs: String, token: String },
}

impl GeneralNotation {
    fn variable_precedence(&self, idx: usize) -> u32 {
        if let Some(next) = self.pattern[idx + 1..].iter().find_map(|item| match item {
            GeneralPatternItem::Literal { precedence, .. } => Some(*precedence),
            GeneralPatternItem::Variable(_) => None,
        }) {
            return next.saturating_add(1);
        }
        if matches!(self.lead, GeneralNotationLead::Infix { .. }) {
            return match self.associativity {
                Some(NotationAssociativity::Right) => self.precedence,
                Some(NotationAssociativity::Left) | None => self.precedence.saturating_add(1),
            };
        }
        0
    }
}

#[derive(Clone, Debug)]
enum GeneralPatternItem {
    Literal { token: String, precedence: u32 },
    Variable(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Associativity {
    Left,
    Right,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum MathToken {
    Atom(String),
    Symbol(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
}

fn parse_math_expr(source: &str, context: &FormulaContext) -> Result<MathExpr, String> {
    let tokens = tokenize_math(source)?;
    if tokens.is_empty() {
        return Err("empty formula".to_owned());
    }
    let mut parser = MathParser {
        tokens: &tokens,
        pos: 0,
        context,
    };
    let expr = parser.parse_expr(0)?;
    if parser.pos == tokens.len() {
        Ok(expr)
    } else {
        Err("formula has trailing tokens after parsed expression".to_owned())
    }
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
            '{' => tokens.push(MathToken::LBrace),
            '}' => tokens.push(MathToken::RBrace),
            ',' => tokens.push(MathToken::Comma),
            _ if is_atom_start(ch) => {
                let mut end = idx + ch.len_utf8();
                while let Some((next_idx, next)) = chars.peek().copied() {
                    if is_atom_continue(next) {
                        chars.next();
                        end = next_idx + next.len_utf8();
                    } else {
                        break;
                    }
                }
                if chars.peek().is_some_and(|(_, next)| *next == '.') {
                    let (dot_idx, dot) = chars.next().expect("peeked dot");
                    end = dot_idx + dot.len_utf8();
                }
                tokens.push(MathToken::Atom(source[idx..end].to_owned()));
            }
            _ => {
                let mut end = idx + ch.len_utf8();
                while let Some((next_idx, next)) = chars.peek().copied() {
                    if next.is_whitespace()
                        || matches!(next, '(' | ')' | '{' | '}' | ',')
                        || is_atom_start(next)
                    {
                        break;
                    }
                    chars.next();
                    end = next_idx + next.len_utf8();
                }
                tokens.push(MathToken::Symbol(source[idx..end].to_owned()));
            }
        }
    }
    Ok(tokens)
}

fn is_atom_start(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphabetic() || ch.is_ascii_digit()
}

fn is_atom_continue(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

struct MathParser<'a> {
    tokens: &'a [MathToken],
    pos: usize,
    context: &'a FormulaContext,
}

impl MathParser<'_> {
    fn parse_expr(&mut self, min_precedence: u32) -> Result<MathExpr, String> {
        let mut lhs = self.parse_prefix_or_application(min_precedence)?;

        loop {
            let Some(token) = self.peek_token_string() else {
                break;
            };
            if let Some(infix) = self.context.infixes.get(&token) {
                if infix.precedence < min_precedence {
                    break;
                }
                self.pos += 1;
                let rhs_precedence = match infix.associativity {
                    Associativity::Left => infix.precedence.saturating_add(1),
                    Associativity::Right => infix.precedence,
                };
                let rhs = self.parse_expr(rhs_precedence)?;
                lhs = MathExpr::App {
                    head: infix.term.clone(),
                    args: vec![lhs, rhs],
                };
                continue;
            }

            let Some(generals) = self.context.infix_generals.get(&token).cloned() else {
                break;
            };
            let mut matched = None;
            for notation in generals {
                if notation.precedence < min_precedence {
                    continue;
                }
                let start = self.pos;
                match self.match_infix_general_notation(&notation, lhs.clone())? {
                    Some(expr) => {
                        matched = Some(expr);
                        break;
                    }
                    None => self.pos = start,
                }
            }
            let Some(expr) = matched else {
                break;
            };
            lhs = expr;
        }

        Ok(lhs)
    }

    fn parse_prefix_or_application(&mut self, min_precedence: u32) -> Result<MathExpr, String> {
        let mut expr = if let Some(expr) = self.try_parse_prefix_general_notation(min_precedence)? {
            expr
        } else if let Some(token) = self.peek_notation_token() {
            if let Some(prefix) = self.context.prefixes.get(token).cloned() {
                if prefix.precedence < min_precedence {
                    return Err("operator precedence does not allow prefix notation".to_owned());
                }
                self.pos += 1;
                let mut args = Vec::new();
                for idx in 0..prefix.arity {
                    let precedence = if idx + 1 == prefix.arity {
                        prefix.precedence
                    } else {
                        u32::MAX
                    };
                    args.push(self.parse_expr(precedence)?);
                }
                if args.is_empty() {
                    MathExpr::Atom { name: prefix.term }
                } else {
                    MathExpr::App {
                        head: prefix.term,
                        args,
                    }
                }
            } else {
                self.parse_primary()?
            }
        } else {
            self.parse_primary()?
        };

        if let MathExpr::Atom { name } = &expr {
            if let Some(arity) = self.context.terms.get(name).copied() {
                if arity > 0 && self.next_starts_argument() {
                    let head = name.clone();
                    let args = (0..arity)
                        .map(|_| self.parse_expr(u32::MAX))
                        .collect::<Result<Vec<_>, _>>()?;
                    expr = MathExpr::App { head, args };
                }
            }
        }

        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<MathExpr, String> {
        let Some(token) = self.tokens.get(self.pos) else {
            return Err("unexpected end of formula".to_owned());
        };
        match token {
            MathToken::Atom(name) | MathToken::Symbol(name) => {
                self.pos += 1;
                Ok(MathExpr::Atom { name: name.clone() })
            }
            MathToken::LParen => {
                self.pos += 1;
                let expr = self.parse_expr(0)?;
                match self.tokens.get(self.pos) {
                    Some(MathToken::RParen) => {
                        self.pos += 1;
                        Ok(expr)
                    }
                    _ => Err("unclosed parenthesis in formula".to_owned()),
                }
            }
            MathToken::LBrace => Err("formula uses unknown brace notation".to_owned()),
            MathToken::RParen => Err("unmatched ')' in formula".to_owned()),
            MathToken::RBrace | MathToken::Comma => {
                Err("formula uses unsupported aggregate notation".to_owned())
            }
        }
    }

    fn try_parse_prefix_general_notation(
        &mut self,
        min_precedence: u32,
    ) -> Result<Option<MathExpr>, String> {
        let Some(token) = self.peek_token_string() else {
            return Ok(None);
        };
        let Some(generals) = self.context.prefix_generals.get(&token).cloned() else {
            return Ok(None);
        };
        for notation in generals {
            if notation.precedence < min_precedence {
                continue;
            }
            let start = self.pos;
            match self.match_prefix_general_notation(&notation)? {
                Some(expr) => return Ok(Some(expr)),
                None => self.pos = start,
            }
        }
        Ok(None)
    }

    fn match_prefix_general_notation(
        &mut self,
        notation: &GeneralNotation,
    ) -> Result<Option<MathExpr>, String> {
        let captures = HashMap::new();
        self.match_general_notation_from(notation, 0, captures)
    }

    fn match_infix_general_notation(
        &mut self,
        notation: &GeneralNotation,
        lhs: MathExpr,
    ) -> Result<Option<MathExpr>, String> {
        let GeneralNotationLead::Infix { lhs: lhs_name, .. } = &notation.lead else {
            return Ok(None);
        };
        let Some(GeneralPatternItem::Literal { token, .. }) = notation.pattern.get(1) else {
            return Ok(None);
        };
        if self.peek_token_string().as_deref() != Some(token.as_str()) {
            return Ok(None);
        }
        self.pos += 1;
        let mut captures = HashMap::new();
        captures.insert(lhs_name.clone(), lhs);
        self.match_general_notation_from(notation, 2, captures)
    }

    fn match_general_notation_from(
        &mut self,
        notation: &GeneralNotation,
        start_idx: usize,
        mut captures: HashMap<String, MathExpr>,
    ) -> Result<Option<MathExpr>, String> {
        for idx in start_idx..notation.pattern.len() {
            match &notation.pattern[idx] {
                GeneralPatternItem::Literal { token, .. } => {
                    if self.peek_token_string().as_deref() != Some(token.as_str()) {
                        return Ok(None);
                    }
                    self.pos += 1;
                }
                GeneralPatternItem::Variable(name) => {
                    let precedence = notation.variable_precedence(idx);
                    let expr = self.parse_expr(precedence)?;
                    captures.insert(name.clone(), expr);
                }
            }
        }

        let args = notation
            .args
            .iter()
            .map(|name| {
                captures
                    .get(name)
                    .cloned()
                    .ok_or_else(|| format!("notation pattern did not bind {name}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        if args.is_empty() {
            Ok(Some(MathExpr::Atom {
                name: notation.term.clone(),
            }))
        } else {
            Ok(Some(MathExpr::App {
                head: notation.term.clone(),
                args,
            }))
        }
    }

    fn peek_notation_token(&self) -> Option<&str> {
        match self.tokens.get(self.pos)? {
            MathToken::Atom(token) | MathToken::Symbol(token) => Some(token),
            MathToken::LParen
            | MathToken::RParen
            | MathToken::LBrace
            | MathToken::RBrace
            | MathToken::Comma => None,
        }
    }

    fn peek_token_string(&self) -> Option<String> {
        token_string(self.tokens.get(self.pos)?)
    }

    fn next_starts_argument(&self) -> bool {
        match self.tokens.get(self.pos) {
            Some(MathToken::Atom(_)) | Some(MathToken::LParen) => true,
            Some(MathToken::LBrace) => self.context.prefix_generals.contains_key("{"),
            Some(MathToken::Symbol(token)) => {
                self.context.prefixes.contains_key(token)
                    || self.context.prefix_generals.contains_key(token)
            }
            Some(MathToken::RParen) | Some(MathToken::RBrace) | Some(MathToken::Comma) | None => {
                false
            }
        }
    }
}

fn token_string(token: &MathToken) -> Option<String> {
    match token {
        MathToken::Atom(token) | MathToken::Symbol(token) => Some(token.clone()),
        MathToken::LParen => Some("(".to_owned()),
        MathToken::RParen => Some(")".to_owned()),
        MathToken::LBrace => Some("{".to_owned()),
        MathToken::RBrace => Some("}".to_owned()),
        MathToken::Comma => Some(",".to_owned()),
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
provable sort wff;
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
    fn records_provable_sort_modifier() {
        let env = parse_env("pure strict provable free sort prop;").unwrap();

        assert_eq!(env.sorts[0].name, "prop");
        assert!(env.sorts[0].provable);
        assert!(env.sort_is_provable("prop"));
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
