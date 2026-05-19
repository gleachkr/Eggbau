use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt::Write as _;

use serde::{Deserialize, Serialize};

use crate::cert::{self, Certificate, EqualityTranslationInput, HypothesisFiat, LocalProofVar};
use crate::export::{self, ExportEnv, ExportTermKind};
use crate::mm0::{Formula, MathExpr, Mm0Env, TheoremDecl};
use crate::{Diagnostic, DiagnosticSeverity, EggbauError, PINNED_EGGLOG};

/// Result of the stage-0 proof API spike.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EgglogProofApiSpike {
    pub egglog_version: String,
    pub term_encoding_runs: bool,
    pub prove_exists_command_available: bool,
    pub structured_proof_api_available: bool,
    pub note: String,
}

/// Stage-4 proof extraction result for one designated MM0 theorem.
///
/// This is intentionally egglog-neutral: the stable API exposes rendered proof
/// diagnostics and a debug tree, not egglog's `ProofStore` internals.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct TheoremProof {
    pub theorem: String,
    pub goal: EgglogGoal,
    pub egglog_program: String,
    pub root_proposition: String,
    pub proof_debug: String,
    pub proof_summary: ProofSummary,
    pub allowed_fiats: Vec<AllowedFiat>,
    pub certificate: Option<Certificate>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EgglogGoal {
    pub constructor: String,
    pub arguments: Vec<String>,
    pub query: String,
    pub kind: EgglogGoalKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EgglogGoalKind {
    Equality,
    Fact,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct AllowedFiat {
    pub reason: FiatReason,
    pub proposition: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FiatReason {
    TheoremHypothesis,
    InsertedReflexiveInput,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct ProofSummary {
    pub fiat: usize,
    pub rule: usize,
    pub trans: usize,
    pub sym: usize,
    pub congr: usize,
}

#[derive(Clone, Debug)]
struct PreparedTheorem {
    theorem: String,
    goal: EgglogGoal,
    local_constructors: Vec<LocalConstructor>,
    hypotheses: Vec<String>,
    seeds: Vec<String>,
    allowed_fiats: BTreeMap<String, AllowedFiat>,
    hypothesis_fiats: Vec<HypothesisFiat>,
}

#[derive(Clone, Debug)]
struct LocalConstructor {
    name: String,
    source_name: String,
    sort: String,
}

/// Run proof-mode egglog for a designated theorem and extract a proof tree.
pub fn prove_theorem(
    env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &str,
) -> Result<TheoremProof, EggbauError> {
    let theorem_decl = env
        .theorem(theorem)
        .ok_or_else(|| EggbauError::UnsupportedCommand(format!("unknown theorem: {theorem}")))?;
    let prepared = prepare_theorem(export_env, theorem_decl)?;
    let program = render_proof_program(export_env, &prepared);

    let mut egraph = egglog::EGraph::new_with_proofs();
    let outputs = egraph
        .parse_and_run_program(None, &program)
        .map_err(|err| EggbauError::Egglog(format!("{err}\n\negglog program:\n{program}")))?;

    let Some((proof_store, proof_id)) = outputs.iter().rev().find_map(|output| match output {
        egglog::CommandOutput::ProveExists {
            proof_store,
            proof_id,
        } => Some((proof_store, *proof_id)),
        _ => None,
    }) else {
        return Err(EggbauError::Egglog(
            "egglog did not return a ProveExists proof object".to_owned(),
        ));
    };

    let mut walker = ProofWalker::new(proof_store, &prepared.allowed_fiats);
    let proof_debug = walker.walk(proof_id)?;
    let proof = proof_store.get(proof_id);
    let root_proposition = walker.proposition_string(proof.proposition());
    let certificate = if prepared.goal.kind == EgglogGoalKind::Equality {
        let relation = theorem_relation(export_env, &theorem_decl.conclusion)?;
        Some(cert::translate_equality_proof(EqualityTranslationInput {
            proof_store,
            root: proof_id,
            export_env,
            relation,
            target_lhs_egglog: &prepared.goal.arguments[0],
            target_rhs_egglog: &prepared.goal.arguments[1],
            local_vars: prepared
                .local_constructors
                .iter()
                .map(|constructor| LocalProofVar {
                    egglog_constructor: constructor.name.clone(),
                    source_name: constructor.source_name.clone(),
                })
                .collect(),
            hypothesis_fiats: prepared.hypothesis_fiats.clone(),
        })?)
    } else {
        None
    };

    let mut diagnostics = Vec::new();
    diagnostics.push(Diagnostic {
        severity: DiagnosticSeverity::Info,
        message: format!("egglog extracted a proof for theorem {theorem}"),
    });
    if certificate.is_some() {
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Info,
            message: "translated egglog equality proof to certificate IR".to_owned(),
        });
    }

    Ok(TheoremProof {
        theorem: prepared.theorem,
        goal: prepared.goal,
        egglog_program: program,
        root_proposition,
        proof_debug,
        proof_summary: walker.summary,
        allowed_fiats: prepared.allowed_fiats.into_values().collect(),
        certificate,
        diagnostics,
    })
}

fn prepare_theorem(
    export_env: &ExportEnv,
    theorem: &TheoremDecl,
) -> Result<PreparedTheorem, EggbauError> {
    if let Some(reason) = &theorem.unsupported_reason {
        return Err(EggbauError::Egglog(format!(
            "theorem {} is outside eggbau's supported fragment: {reason}",
            theorem.name
        )));
    }

    let mut variables = BTreeMap::new();
    let mut local_constructors = Vec::new();
    for binder in &theorem.binders {
        let sort = export_env
            .sorts
            .iter()
            .find(|sort| sort.source_name == binder.sort)
            .ok_or_else(|| {
                EggbauError::Egglog(format!(
                    "theorem {} binder {} uses undeclared sort {}",
                    theorem.name, binder.name, binder.sort
                ))
            })?;
        let constructor = format!(
            "EggbauVar{}{}",
            pascal_ident(&theorem.name),
            pascal_ident(&binder.name)
        );
        variables.insert(binder.name.clone(), render_call(&constructor, &[]));
        local_constructors.push(LocalConstructor {
            name: constructor,
            source_name: binder.name.clone(),
            sort: sort.egglog_name.clone(),
        });
    }

    let mut allowed_fiats = BTreeMap::new();
    let mut hypotheses = Vec::new();
    let mut hypothesis_fiats = Vec::new();
    for (idx, hypothesis) in theorem.hypotheses.iter().enumerate() {
        let assertion = render_hypothesis(export_env, hypothesis, &variables).map_err(|err| {
            EggbauError::Egglog(format!(
                "cannot lower hypothesis #{} of theorem {}: {err}",
                idx + 1,
                theorem.name
            ))
        })?;
        let formula = cert::formula_from_mm0(hypothesis, export_env);
        for (fiat_idx, proposition) in assertion.allowed_fiats.iter().enumerate() {
            allowed_fiats.insert(
                proposition.clone(),
                AllowedFiat {
                    reason: FiatReason::TheoremHypothesis,
                    proposition: proposition.clone(),
                },
            );
            if let Some(formula) = &formula {
                hypothesis_fiats.push(HypothesisFiat {
                    proposition: proposition.clone(),
                    hyp_index: idx + 1,
                    formula: formula.clone(),
                    needs_symmetry: fiat_idx == 1,
                });
            }
        }
        hypotheses.push(assertion.command);
    }

    let goal = render_goal(export_env, &theorem.conclusion, &variables).map_err(|err| {
        EggbauError::Egglog(format!(
            "cannot lower conclusion of theorem {}: {err}",
            theorem.name
        ))
    })?;
    let mut seen_seeds = BTreeSet::new();
    let seeds = goal
        .arguments
        .iter()
        .filter(|argument| seen_seeds.insert((*argument).clone()))
        .cloned()
        .collect::<Vec<_>>();
    for seed in &seeds {
        allowed_fiats.insert(
            format!("{seed} = {seed}"),
            AllowedFiat {
                reason: FiatReason::InsertedReflexiveInput,
                proposition: format!("{seed} = {seed}"),
            },
        );
    }

    Ok(PreparedTheorem {
        theorem: theorem.name.clone(),
        goal,
        local_constructors,
        hypotheses,
        seeds,
        allowed_fiats,
        hypothesis_fiats,
    })
}

struct HypothesisAssertion {
    command: String,
    allowed_fiats: Vec<String>,
}

fn render_hypothesis(
    export_env: &ExportEnv,
    formula: &Formula,
    variables: &BTreeMap<String, String>,
) -> Result<HypothesisAssertion, String> {
    if let Some((_, lhs, rhs)) = relation_formula(export_env, formula) {
        let lhs = render_expr(export_env, lhs, variables)?;
        let rhs = render_expr(export_env, rhs, variables)?;
        return Ok(HypothesisAssertion {
            command: format!("(union {lhs} {rhs})"),
            allowed_fiats: vec![format!("{lhs} = {rhs}"), format!("{rhs} = {lhs}")],
        });
    }

    let (head, args) = fact_formula(export_env, formula)?;
    let rendered_args = args
        .iter()
        .map(|arg| render_expr(export_env, arg, variables))
        .collect::<Result<Vec<_>, _>>()?;
    let relation = &export_env
        .term(head)
        .expect("fact_formula checked exported term")
        .egglog_name;
    let command = render_call(relation, &rendered_args);
    Ok(HypothesisAssertion {
        allowed_fiats: vec![format!("{command} = {command}")],
        command,
    })
}

fn render_goal(
    export_env: &ExportEnv,
    formula: &Formula,
    variables: &BTreeMap<String, String>,
) -> Result<EgglogGoal, String> {
    if let Some((sort, lhs, rhs)) = relation_formula(export_env, formula) {
        let constructor = export_env
            .proof_goals
            .equality
            .get(sort)
            .ok_or_else(|| format!("no equality goal constructor for sort {sort}"))?
            .clone();
        let arguments = vec![
            render_expr(export_env, lhs, variables)?,
            render_expr(export_env, rhs, variables)?,
        ];
        let query = render_call(&constructor, &arguments);
        return Ok(EgglogGoal {
            constructor,
            arguments,
            query,
            kind: EgglogGoalKind::Equality,
        });
    }

    let (head, args) = fact_formula(export_env, formula)?;
    let constructor = export_env
        .proof_goals
        .facts
        .get(head)
        .ok_or_else(|| format!("no fact goal constructor for predicate {head}"))?
        .clone();
    let arguments = args
        .iter()
        .map(|arg| render_expr(export_env, arg, variables))
        .collect::<Result<Vec<_>, _>>()?;
    let query = render_call(&constructor, &arguments);
    Ok(EgglogGoal {
        constructor,
        arguments,
        query,
        kind: EgglogGoalKind::Fact,
    })
}

fn render_proof_program(export_env: &ExportEnv, prepared: &PreparedTheorem) -> String {
    let mut out = export::render_egglog(export_env);
    if !out.ends_with('\n') {
        out.push('\n');
    }
    writeln!(out).expect("write to string");
    writeln!(out, ";; theorem-local symbolic inputs").expect("write to string");
    for constructor in &prepared.local_constructors {
        writeln!(
            out,
            "(constructor {} () {})",
            constructor.name, constructor.sort
        )
        .expect("write to string");
    }
    for hypothesis in &prepared.hypotheses {
        writeln!(out, "{hypothesis}").expect("write to string");
    }
    for seed in &prepared.seeds {
        writeln!(out, "{seed}").expect("write to string");
    }
    writeln!(out, "(run-schedule (saturate (run saturation)))").expect("write to string");
    writeln!(out, "(run-schedule (run goals))").expect("write to string");
    writeln!(out, "(prove {})", prepared.goal.query).expect("write to string");
    out
}

fn theorem_relation<'a>(
    export_env: &'a ExportEnv,
    formula: &Formula,
) -> Result<&'a str, EggbauError> {
    let Some((sort, _, _)) = relation_formula(export_env, formula) else {
        return Err(EggbauError::Egglog(
            "equality proof target is not a relation formula".to_owned(),
        ));
    };
    export_env
        .relations
        .get(sort)
        .map(|bundle| bundle.relation.as_str())
        .ok_or_else(|| {
            EggbauError::Egglog("equality proof target has no relation bundle".to_owned())
        })
}

fn relation_formula<'a>(
    export_env: &'a ExportEnv,
    formula: &'a Formula,
) -> Option<(&'a str, &'a MathExpr, &'a MathExpr)> {
    let MathExpr::App { head, args } = formula.expr.as_ref()? else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    export_env
        .relations
        .iter()
        .find(|(_, relation)| relation.relation == *head)
        .map(|(sort, _)| (sort.as_str(), &args[0], &args[1]))
}

fn fact_formula<'a>(
    export_env: &ExportEnv,
    formula: &'a Formula,
) -> Result<(&'a str, &'a [MathExpr]), String> {
    let expr = formula
        .expr
        .as_ref()
        .ok_or_else(|| "formula did not parse to a kernel expression".to_owned())?;
    let head = expr.head();
    let term = export_env
        .term(head)
        .ok_or_else(|| format!("formula head is not declared: {head}"))?;
    if term.kind != ExportTermKind::FactRelation {
        return Err(format!("formula head is not an exported fact: {head}"));
    }
    match expr {
        MathExpr::Atom { .. } => Ok((head, &[])),
        MathExpr::App { args, .. } => Ok((head, args.as_slice())),
    }
}

fn render_expr(
    export_env: &ExportEnv,
    expr: &MathExpr,
    variables: &BTreeMap<String, String>,
) -> Result<String, String> {
    match expr {
        MathExpr::Atom { name } => {
            if let Some(variable) = variables.get(name) {
                return Ok(variable.clone());
            }
            let term = export_env
                .term(name)
                .ok_or_else(|| format!("formula references undeclared atom: {name}"))?;
            Ok(render_call(&term.egglog_name, &[]))
        }
        MathExpr::App { head, args } => {
            let term = export_env
                .term(head)
                .ok_or_else(|| format!("formula references undeclared term: {head}"))?;
            let rendered_args = args
                .iter()
                .map(|arg| render_expr(export_env, arg, variables))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(render_call(&term.egglog_name, &rendered_args))
        }
    }
}

struct ProofWalker<'a> {
    store: &'a egglog::proof::ProofStore,
    allowed_fiats: &'a BTreeMap<String, AllowedFiat>,
    visited: HashSet<egglog::proof::ProofId>,
    summary: ProofSummary,
}

impl<'a> ProofWalker<'a> {
    fn new(
        store: &'a egglog::proof::ProofStore,
        allowed_fiats: &'a BTreeMap<String, AllowedFiat>,
    ) -> Self {
        Self {
            store,
            allowed_fiats,
            visited: HashSet::new(),
            summary: ProofSummary::default(),
        }
    }

    fn walk(&mut self, root: egglog::proof::ProofId) -> Result<String, EggbauError> {
        let mut out = String::new();
        self.walk_inner(root, 0, &mut out)?;
        Ok(out)
    }

    fn walk_inner(
        &mut self,
        proof_id: egglog::proof::ProofId,
        indent: usize,
        out: &mut String,
    ) -> Result<(), EggbauError> {
        let proof = self.store.get(proof_id);
        let proposition = self.proposition_string(proof.proposition());
        let pad = "  ".repeat(indent);
        if !self.visited.insert(proof_id) {
            writeln!(out, "{pad}#{proof_id}: shared {proposition}").expect("write");
            return Ok(());
        }

        match proof.justification() {
            egglog::proof::Justification::Fiat => {
                self.summary.fiat += 1;
                if !self.allowed_fiats.contains_key(&proposition)
                    && !is_reflexive_proposition(&proposition)
                {
                    return Err(EggbauError::Egglog(format!(
                        "egglog proof used unapproved Fiat proposition: {proposition}"
                    )));
                }
                writeln!(out, "{pad}#{proof_id}: Fiat {proposition}").expect("write");
            }
            egglog::proof::Justification::Rule {
                name,
                premise_proofs,
                ..
            } => {
                self.summary.rule += 1;
                writeln!(out, "{pad}#{proof_id}: Rule {name} {proposition}").expect("write");
                for premise in premise_proofs {
                    self.walk_inner(*premise, indent + 1, out)?;
                }
            }
            egglog::proof::Justification::Trans(left, right) => {
                self.summary.trans += 1;
                writeln!(out, "{pad}#{proof_id}: Trans {proposition}").expect("write");
                self.walk_inner(*left, indent + 1, out)?;
                self.walk_inner(*right, indent + 1, out)?;
            }
            egglog::proof::Justification::Sym(inner) => {
                self.summary.sym += 1;
                writeln!(out, "{pad}#{proof_id}: Sym {proposition}").expect("write");
                self.walk_inner(*inner, indent + 1, out)?;
            }
            egglog::proof::Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => {
                self.summary.congr += 1;
                writeln!(
                    out,
                    "{pad}#{proof_id}: Congr child {child_index} {proposition}"
                )
                .expect("write");
                self.walk_inner(*proof, indent + 1, out)?;
                self.walk_inner(*child_proof, indent + 1, out)?;
            }
            egglog::proof::Justification::MergeFn { function, .. } => {
                return Err(EggbauError::Egglog(format!(
                    "unsupported egglog proof justification MergeFn for function {function}"
                )));
            }
        }

        Ok(())
    }

    fn proposition_string(&self, proposition: &egglog::proof::Proposition) -> String {
        format!(
            "{} = {}",
            self.store.term_dag().to_string(proposition.lhs()),
            self.store.term_dag().to_string(proposition.rhs())
        )
    }
}

fn is_reflexive_proposition(proposition: &str) -> bool {
    proposition
        .split_once(" = ")
        .is_some_and(|(lhs, rhs)| lhs == rhs)
}

fn render_call(head: &str, args: &[String]) -> String {
    if args.is_empty() {
        format!("({head})")
    } else {
        format!("({head} {})", args.join(" "))
    }
}

fn pascal_ident(name: &str) -> String {
    let mut out = String::new();
    for part in name.split('_').filter(|part| !part.is_empty()) {
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            out.extend(first.to_uppercase());
            out.push_str(chars.as_str());
        }
    }
    if out.is_empty() {
        "Generated".to_owned()
    } else {
        out
    }
}

/// Run a tiny proof-mode egglog program through the Rust API.
///
/// This depends on the vendored egglog patch exposing a read-only proof API.
/// The spike does not translate proofs yet; it only checks that eggbau can
/// receive a structured `ProofStore`, inspect a `Justification`, and resolve
/// proof terms through the proof store's `TermDag`.
pub fn run_proof_api_spike() -> Result<EgglogProofApiSpike, EggbauError> {
    let mut egraph = egglog::EGraph::new_with_proofs();
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
(sort Expr)
(constructor A () Expr)
(constructor B () Expr)
(ruleset demo)
(A)
(rule ((= x (A))) ((union x (B))) :ruleset demo)
(run-schedule (saturate (run demo)))
(prove-exists B)
"#,
        )
        .map_err(|err| EggbauError::Egglog(err.to_string()))?;

    let Some((proof_store, proof_id)) = outputs.iter().find_map(|output| match output {
        egglog::CommandOutput::ProveExists {
            proof_store,
            proof_id,
        } => Some((proof_store, proof_id)),
        _ => None,
    }) else {
        return Ok(EgglogProofApiSpike {
            egglog_version: PINNED_EGGLOG.to_owned(),
            term_encoding_runs: true,
            prove_exists_command_available: false,
            structured_proof_api_available: false,
            note: "vendored egglog did not return CommandOutput::ProveExists".to_owned(),
        });
    };

    let proof = proof_store.get(*proof_id);
    let proposition = proof.proposition();
    let _lhs = proof_store.term_dag().to_string(proposition.lhs());
    let _rhs = proof_store.term_dag().to_string(proposition.rhs());

    match proof.justification() {
        egglog::proof::Justification::Fiat
        | egglog::proof::Justification::Rule { .. }
        | egglog::proof::Justification::Trans(_, _)
        | egglog::proof::Justification::Sym(_)
        | egglog::proof::Justification::Congr { .. }
        | egglog::proof::Justification::MergeFn { .. } => {}
    }

    Ok(EgglogProofApiSpike {
        egglog_version: PINNED_EGGLOG.to_owned(),
        term_encoding_runs: true,
        prove_exists_command_available: true,
        structured_proof_api_available: true,
        note: concat!(
            "vendored egglog exposes CommandOutput::ProveExists and a ",
            "read-only ProofStore/Justification API"
        )
        .to_owned(),
    })
}
