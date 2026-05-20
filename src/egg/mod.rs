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
    pub arguments: Vec<String>,
    /// Fact expression passed straight to `(prove ...)`. For equality goals
    /// this is `(= lhs rhs)`; for atomic-fact goals it's `(P args...)`. We
    /// used to wrap goals in a `ProvenEqS`/`ProvenP` constructor populated
    /// by a `(rule ((= a b)) ((ProvenEqS a b)))` lifting rule, but that
    /// created an entry for every pair of equal e-classes after saturation
    /// and made `(prove ...)` extraction blow up. Direct goals are how
    /// egglog's own examples do goal-directed search.
    pub query: String,
    pub kind: EgglogGoalKind,
    /// Fact expression used as the `:until` condition on the saturation
    /// schedule. Stops saturation the moment the goal e-classes unify,
    /// keeping the e-graph small enough that egglog's `(prove ...)`
    /// extraction stays fast — on a fully-saturated graph with idempotent
    /// rewrites the proof search can take many minutes even though
    /// saturation itself terminates in under a second.
    pub until_fact: String,
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
    source_sort: String,
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
    run_prepared_theorem(env, export_env, theorem_decl, prepared, program, false)
}

/// Run a user-supplied egglog proof-problem script for one theorem.
///
/// The script is untrusted. Eggbau checks that the extracted proof proves the
/// selected theorem goal, translates it to certificate IR, and validates the
/// certificate against the MM0 theorem before returning.
pub fn check_theorem_script(
    env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &str,
    script: &str,
) -> Result<TheoremProof, EggbauError> {
    let theorem_decl = env
        .theorem(theorem)
        .ok_or_else(|| EggbauError::UnsupportedCommand(format!("unknown theorem: {theorem}")))?;
    let prepared = prepare_theorem(export_env, theorem_decl)?;
    run_prepared_theorem(
        env,
        export_env,
        theorem_decl,
        prepared,
        script.to_owned(),
        true,
    )
}

fn run_prepared_theorem(
    env: &Mm0Env,
    export_env: &ExportEnv,
    theorem_decl: &TheoremDecl,
    prepared: PreparedTheorem,
    program: String,
    supplied_script: bool,
) -> Result<TheoremProof, EggbauError> {
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
    let proof = proof_store.get(proof_id);
    let root_proposition = walker.proposition_string(proof.proposition());
    if supplied_script {
        let expected = expected_root_proposition(&prepared.goal);
        if root_proposition != expected {
            return Err(EggbauError::Egglog(format!(
                concat!(
                    "supplied egglog script proves `{}`, ",
                    "expected theorem {} goal `{}`"
                ),
                root_proposition, prepared.theorem, expected
            )));
        }
    }
    let proof_debug = walker.walk(proof_id)?;
    let local_vars = prepared
        .local_constructors
        .iter()
        .map(|constructor| LocalProofVar {
            egglog_constructor: constructor.name.clone(),
            source_name: constructor.source_name.clone(),
            sort: constructor.source_sort.clone(),
        })
        .collect::<Vec<_>>();
    let certificate = if prepared.goal.kind == EgglogGoalKind::Equality {
        let relation = theorem_relation(export_env, &theorem_decl.conclusion)?;
        cert::translate_equality_proof(EqualityTranslationInput {
            proof_store,
            root: proof_id,
            export_env,
            relation,
            target_lhs_egglog: &prepared.goal.arguments[0],
            target_rhs_egglog: &prepared.goal.arguments[1],
            local_vars,
            hypothesis_fiats: prepared.hypothesis_fiats.clone(),
        })?
    } else {
        let (target_pred, _) =
            fact_formula(export_env, &theorem_decl.conclusion).map_err(EggbauError::Egglog)?;
        translate_fact_with_equality_fallback(FactFallbackInput {
            egraph: &mut egraph,
            proof_store,
            root: proof_id,
            export_env,
            target_pred,
            target_args_egglog: prepared.goal.arguments.clone(),
            local_vars,
            hypothesis_fiats: prepared.hypothesis_fiats.clone(),
        })?
    };
    if supplied_script {
        cert::validate_certificate_for_theorem(&certificate, env, export_env, &prepared.theorem)?;
    }

    let mut diagnostics = Vec::new();
    diagnostics.push(Diagnostic {
        severity: DiagnosticSeverity::Info,
        message: format!("egglog extracted a proof for theorem {}", prepared.theorem),
    });
    diagnostics.push(Diagnostic {
        severity: DiagnosticSeverity::Info,
        message: "translated egglog proof to certificate IR".to_owned(),
    });
    if supplied_script {
        diagnostics.push(Diagnostic {
            severity: DiagnosticSeverity::Info,
            message: "validated certificate IR".to_owned(),
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
        certificate: Some(certificate),
        diagnostics,
    })
}

struct FactFallbackInput<'a> {
    egraph: &'a mut egglog::EGraph,
    proof_store: &'a egglog::proof::ProofStore,
    root: egglog::proof::ProofId,
    export_env: &'a ExportEnv,
    target_pred: &'a str,
    target_args_egglog: Vec<String>,
    local_vars: Vec<LocalProofVar>,
    hypothesis_fiats: Vec<HypothesisFiat>,
}

struct ExtraEqualityRequest {
    sort: String,
    relation: String,
    lhs_egglog: String,
    rhs_egglog: String,
}

fn translate_fact_with_equality_fallback(
    mut input: FactFallbackInput<'_>,
) -> Result<Certificate, EggbauError> {
    let mut extra_equalities = Vec::new();
    let mut requested = BTreeSet::new();

    loop {
        let result = cert::translate_fact_proof(cert::FactTranslationInput {
            proof_store: input.proof_store,
            root: input.root,
            export_env: input.export_env,
            target_pred: input.target_pred,
            target_args_egglog: input.target_args_egglog.clone(),
            local_vars: input.local_vars.clone(),
            hypothesis_fiats: input.hypothesis_fiats.clone(),
            extra_equalities: extra_equalities.clone(),
        });

        let Err(error) = result else {
            return result.map_err(EggbauError::from);
        };
        let cert::TranslateError::MissingEqualityProof {
            sort,
            relation,
            lhs_egglog,
            rhs_egglog,
        } = error
        else {
            return Err(EggbauError::from(error));
        };

        let request = ExtraEqualityRequest {
            sort,
            relation,
            lhs_egglog,
            rhs_egglog,
        };
        let key = (
            request.sort.clone(),
            request.lhs_egglog.clone(),
            request.rhs_egglog.clone(),
        );
        if !requested.insert(key) {
            return Err(EggbauError::from(
                cert::TranslateError::MissingEqualityProof {
                    sort: request.sort,
                    relation: request.relation,
                    lhs_egglog: request.lhs_egglog,
                    rhs_egglog: request.rhs_egglog,
                },
            ));
        }

        let certificate = prove_extra_equality(&mut input, &request)?;
        extra_equalities.push(cert::ExtraEqualityCertificate {
            sort: request.sort.clone(),
            relation: request.relation.clone(),
            lhs_egglog: request.lhs_egglog.clone(),
            rhs_egglog: request.rhs_egglog.clone(),
            certificate,
        });
    }
}

fn prove_extra_equality(
    input: &mut FactFallbackInput<'_>,
    request: &ExtraEqualityRequest,
) -> Result<Certificate, EggbauError> {
    let query = format!("(= {} {})", request.lhs_egglog, request.rhs_egglog);
    let program = format!("(prove {query})\n");
    let outputs = input
        .egraph
        .parse_and_run_program(None, &program)
        .map_err(|err| EggbauError::Egglog(err.to_string()))?;
    let Some((proof_store, proof_id)) = outputs.iter().rev().find_map(|output| match output {
        egglog::CommandOutput::ProveExists {
            proof_store,
            proof_id,
        } => Some((proof_store, *proof_id)),
        _ => None,
    }) else {
        return Err(EggbauError::Egglog(format!(
            "egglog did not return a proof for equality fallback {query}"
        )));
    };

    cert::translate_equality_proof(EqualityTranslationInput {
        proof_store,
        root: proof_id,
        export_env: input.export_env,
        relation: &request.relation,
        target_lhs_egglog: &request.lhs_egglog,
        target_rhs_egglog: &request.rhs_egglog,
        local_vars: input.local_vars.clone(),
        hypothesis_fiats: input.hypothesis_fiats.clone(),
    })
    .map_err(EggbauError::from)
}

/// Render the theorem-specific egglog proof problem without running egglog.
///
/// This is the same program text that `prove_theorem` sends to egglog for
/// the selected theorem. The script is untrusted debug/user-editable input;
/// proof reconstruction still decides whether any result is acceptable.
pub fn render_theorem_script(
    env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &str,
) -> Result<String, EggbauError> {
    let theorem_decl = env
        .theorem(theorem)
        .ok_or_else(|| EggbauError::UnsupportedCommand(format!("unknown theorem: {theorem}")))?;
    let prepared = prepare_theorem(export_env, theorem_decl)?;
    Ok(render_proof_program(export_env, &prepared))
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
            source_sort: binder.sort.clone(),
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

fn expected_root_proposition(goal: &EgglogGoal) -> String {
    match goal.kind {
        EgglogGoalKind::Equality => format!("{} = {}", goal.arguments[0], goal.arguments[1]),
        EgglogGoalKind::Fact => format!("{} = {}", goal.query, goal.query),
    }
}

fn render_goal(
    export_env: &ExportEnv,
    formula: &Formula,
    variables: &BTreeMap<String, String>,
) -> Result<EgglogGoal, String> {
    if let Some((_sort, lhs, rhs)) = relation_formula(export_env, formula) {
        let arguments = vec![
            render_expr(export_env, lhs, variables)?,
            render_expr(export_env, rhs, variables)?,
        ];
        let query = format!("(= {} {})", arguments[0], arguments[1]);
        let until_fact = query.clone();
        return Ok(EgglogGoal {
            arguments,
            query,
            kind: EgglogGoalKind::Equality,
            until_fact,
        });
    }

    let (head, args) = fact_formula(export_env, formula)?;
    let arguments = args
        .iter()
        .map(|arg| render_expr(export_env, arg, variables))
        .collect::<Result<Vec<_>, _>>()?;
    let fact_relation = &export_env
        .term(head)
        .expect("fact_formula checked exported term")
        .egglog_name;
    let query = render_call(fact_relation, &arguments);
    let until_fact = query.clone();
    Ok(EgglogGoal {
        arguments,
        query,
        kind: EgglogGoalKind::Fact,
        until_fact,
    })
}

fn render_proof_program(export_env: &ExportEnv, prepared: &PreparedTheorem) -> String {
    let mut out = String::new();
    writeln!(out, ";; generated by eggbau {}", env!("CARGO_PKG_VERSION")).expect("write to string");
    writeln!(out, ";; theorem: {}", prepared.theorem).expect("write to string");
    writeln!(out, ";; script kind: proof-problem").expect("write to string");
    writeln!(
        out,
        ";; rule names are part of the reconstruction interface"
    )
    .expect("write to string");
    writeln!(out).expect("write to string");
    out.push_str(&export::render_egglog(export_env));
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
    writeln!(
        out,
        "(run-schedule (repeat {SATURATION_ITERATION_CAP} \
         (run saturation :until {})))",
        prepared.goal.until_fact,
    )
    .expect("write to string");
    writeln!(out, "(prove {})", prepared.goal.query).expect("write to string");
    out
}

/// Upper bound on saturation iterations per proof attempt.
///
/// The `:until <goal-fact>` clause on the inner `run` is the load-bearing
/// piece: it stops saturation the moment the goal e-classes unify, before
/// the e-graph accumulates the redundant union paths that make egglog's
/// `(prove ...)` extraction blow up. (`(saturate ...)` by itself terminates
/// fine — proof *search*, not saturation, is what scales poorly on a
/// fully-saturated graph with idempotent rewrites.) This `repeat` cap is a
/// belt-and-suspenders safety net for pathological user axioms; well-formed
/// rule sets exit via `:until` long before reaching it.
const SATURATION_ITERATION_CAP: usize = 1024;

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
