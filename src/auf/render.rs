use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::OutputMode;
use crate::cert::{CertStep, Certificate, Formula, Label, Literal, Ref, Term, TermOrFormula};
use crate::export::{ExportEnv, RelationBundle};
use crate::mm0::{BinderKind, MathExpr, Mm0Env, TheoremDecl};

use super::notation::NotationRenderEnv;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub enum AufRenderExplicitness {
    #[default]
    Explicit,
    Implicit,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub enum AufRenderCompaction {
    #[default]
    NoCompact,
    Compact,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub enum AufMathFormat {
    #[default]
    Kernel,
    Notation,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct AufRenderFormat {
    pub explicitness: AufRenderExplicitness,
    pub compaction: AufRenderCompaction,
    pub math: AufMathFormat,
}

impl AufRenderFormat {
    pub fn explicit() -> Self {
        Self {
            explicitness: AufRenderExplicitness::Explicit,
            compaction: AufRenderCompaction::NoCompact,
            math: AufMathFormat::Kernel,
        }
    }

    pub fn implicit() -> Self {
        Self {
            explicitness: AufRenderExplicitness::Implicit,
            compaction: AufRenderCompaction::NoCompact,
            math: AufMathFormat::Kernel,
        }
    }

    pub fn with_compaction(mut self, compaction: AufRenderCompaction) -> Self {
        self.compaction = compaction;
        self
    }

    pub fn compact_enabled(self) -> bool {
        self.compaction == AufRenderCompaction::Compact
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct AufRenderOptions {
    pub output_mode: OutputMode,
    pub format: AufRenderFormat,
}

impl Default for AufRenderOptions {
    fn default() -> Self {
        Self {
            output_mode: OutputMode::Fragment,
            format: AufRenderFormat::explicit(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct AufRenderResult {
    pub text: String,
    pub diagnostics: Vec<String>,
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum AufRenderError {
    #[error("unknown theorem `{theorem}`")]
    UnknownTheorem { theorem: String },

    #[error("certificate for theorem `{theorem}` has no emitted proof lines")]
    EmptyProof { theorem: String },

    #[error("unsupported Aufbau output mode {mode:?}: {reason}")]
    UnsupportedOutputMode { mode: OutputMode, reason: String },

    #[error("unknown relation `{relation}`")]
    UnknownRelation { relation: String },

    #[error("unknown proof label `{label}`")]
    UnknownLabel { label: Label },

    #[error("cannot render literal term `{literal:?}` in MM0 math")]
    UnsupportedLiteral { literal: Literal },

    #[error("unsupported notation for term `{term}` ({kind}): {declaration}")]
    UnsupportedNotation {
        term: String,
        kind: String,
        declaration: String,
    },

    #[error("cannot infer formula for certificate step `{label}`: {reason}")]
    FormulaInference { label: Label, reason: String },

    #[error("rule `{rule}` was not declared in the MM0 environment")]
    UnknownRule { rule: String },

    #[error("cannot infer binding `{binder}` for rule `{rule}`")]
    MissingBinding { rule: String, binder: String },

    #[error("inconsistent inferred binding `{binder}` for rule `{rule}`")]
    InconsistentBinding { rule: String, binder: String },

    #[error("bound binder `{binder}` for rule `{rule}` must instantiate to a variable")]
    BoundBinderNonVariable { rule: String, binder: String },

    #[error(
        "bound binder `{binder}` for rule `{rule}` instantiates to duplicate \
         variable `{variable}`"
    )]
    DuplicateBoundBinderInstantiation {
        rule: String,
        binder: String,
        variable: String,
    },

    #[error("cannot match rule `{rule}` against generated line `{label}`")]
    RuleMismatch { rule: String, label: Label },

    #[error("hypothesis step `{label}` uses invalid hypothesis #{hyp_index}")]
    BadHypothesis { label: Label, hyp_index: usize },

    #[error("certificate final formula does not match theorem `{theorem}`")]
    FinalFormulaMismatch { theorem: String },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RenderRef {
    Hyp(usize),
    Line(String),
}

impl RenderRef {
    fn text(&self) -> String {
        match self {
            Self::Hyp(index) => format!("#{index}"),
            Self::Line(label) => label.clone(),
        }
    }
}

#[derive(Clone, Debug, Eq)]
enum BindingValue {
    Term(Term),
    Formula(Formula),
}

impl PartialEq for BindingValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Term(left), Self::Term(right)) => left == right,
            (Self::Formula(left), Self::Formula(right)) => left == right,
            (Self::Term(left), Self::Formula(right)) => left == &term_from_formula(right),
            (Self::Formula(left), Self::Term(right)) => &term_from_formula(left) == right,
        }
    }
}

fn term_from_formula(formula: &Formula) -> Term {
    match formula {
        Formula::Atom { pred, args } if args.is_empty() => Term::var(pred.clone()),
        Formula::Atom { pred, args } => Term::app(pred.clone(), args.clone()),
        Formula::Rel { rel, lhs, rhs } => Term::app(rel.clone(), vec![lhs.clone(), rhs.clone()]),
    }
}

#[derive(Clone, Debug, Default)]
struct RenderState {
    format: AufRenderFormat,
    notation: Option<NotationRenderEnv>,
    formulas: BTreeMap<Label, Formula>,
    refs: BTreeMap<Label, RenderRef>,
    emitted_labels: BTreeSet<String>,
    label_by_refl: BTreeMap<(String, Term), Label>,
    last_emitted: Option<Label>,
}

pub fn render_certificate(
    mm0_env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &str,
    certificate: &Certificate,
    options: AufRenderOptions,
) -> Result<AufRenderResult, AufRenderError> {
    render_certificate_with_block_header(mm0_env, export_env, theorem, certificate, options, None)
}

pub fn render_certificate_with_block_header(
    mm0_env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &str,
    certificate: &Certificate,
    options: AufRenderOptions,
    block_header: Option<&str>,
) -> Result<AufRenderResult, AufRenderError> {
    let theorem_decl = mm0_env
        .theorem(theorem)
        .ok_or_else(|| AufRenderError::UnknownTheorem {
            theorem: theorem.to_owned(),
        })?;
    if options.output_mode != OutputMode::Fragment {
        return Err(AufRenderError::UnsupportedOutputMode {
            mode: options.output_mode,
            reason: concat!(
                "fragment rendering cannot emit spliced or full-stream output; ",
                "use the top-level pipeline for stream-order proof obligation ",
                "tracking"
            )
            .to_owned(),
        });
    }

    let mut state = RenderState {
        format: options.format,
        notation: (options.format.math == AufMathFormat::Notation)
            .then(|| NotationRenderEnv::from_mm0(mm0_env)),
        ..RenderState::default()
    };
    let mut out = String::new();
    let block_header = block_header.unwrap_or(&theorem_decl.name);
    writeln!(out, "{block_header}").expect("write to string");
    writeln!(out, "{}", "-".repeat(block_header.len().max(3))).expect("write to string");

    for step in &certificate.steps {
        render_step(
            mm0_env,
            export_env,
            theorem_decl,
            step,
            &mut state,
            &mut out,
        )?;
    }

    let Some(last_label) = state.last_emitted.as_ref() else {
        return Err(AufRenderError::EmptyProof {
            theorem: theorem.to_owned(),
        });
    };
    let final_formula =
        state
            .formulas
            .get(last_label)
            .ok_or_else(|| AufRenderError::UnknownLabel {
                label: last_label.clone(),
            })?;
    let target =
        crate::cert::formula_from_mm0(&theorem_decl.conclusion, export_env).ok_or_else(|| {
            AufRenderError::FormulaInference {
                label: last_label.clone(),
                reason: "target theorem conclusion is outside the rendered fragment".to_owned(),
            }
        })?;
    if final_formula != &target {
        return Err(AufRenderError::FinalFormulaMismatch {
            theorem: theorem.to_owned(),
        });
    }

    Ok(AufRenderResult {
        text: out,
        diagnostics: vec!["emitted an Aufbau proof fragment for the target theorem".to_owned()],
    })
}

fn render_step(
    mm0_env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &TheoremDecl,
    step: &CertStep,
    state: &mut RenderState,
    out: &mut String,
) -> Result<(), AufRenderError> {
    match step {
        CertStep::Hyp {
            label,
            hyp_index,
            formula,
        } => {
            if *hyp_index == 0 || *hyp_index > theorem.hypotheses.len() {
                return Err(AufRenderError::BadHypothesis {
                    label: label.clone(),
                    hyp_index: *hyp_index,
                });
            }
            state.formulas.insert(label.clone(), formula.clone());
            state.refs.insert(label.clone(), RenderRef::Hyp(*hyp_index));
            Ok(())
        }
        CertStep::RuleApply {
            label,
            formula,
            mm0_rule,
            bindings,
            refs,
        } => {
            let refs = resolve_refs(refs, state)?;
            let ref_formulas = refs
                .iter()
                .map(|reference| formula_for_render_ref(reference, theorem, export_env, state))
                .collect::<Result<Vec<_>, _>>()?;
            let initial_bindings = render_explicit_bindings(bindings);
            emit_line(
                EmitLineInput {
                    label,
                    formula,
                    rule: mm0_rule,
                    refs: &refs,
                    ref_formulas: &ref_formulas,
                    initial_bindings,
                },
                mm0_env,
                state,
                out,
            )
        }
        CertStep::EqRefl {
            label,
            relation,
            term,
        } => {
            let bundle = relation_bundle(export_env, relation)?;
            let formula = Formula::rel(relation.clone(), term.clone(), term.clone());
            emit_line(
                EmitLineInput::no_refs(label, &formula, &bundle.reflexivity),
                mm0_env,
                state,
                out,
            )
        }
        CertStep::EqSym {
            label,
            relation,
            source,
        } => {
            let bundle = relation_bundle(export_env, relation)?;
            let source_formula = expect_formula(source, state)?.clone();
            let (lhs, rhs) = expect_relation(&source_formula, relation, label)?;
            let formula = Formula::rel(relation.clone(), rhs.clone(), lhs.clone());
            let refs = vec![resolve_label_ref(source, state)?];
            emit_line(
                EmitLineInput::with_refs(
                    label,
                    &formula,
                    &bundle.symmetry,
                    &refs,
                    &[source_formula],
                ),
                mm0_env,
                state,
                out,
            )
        }
        CertStep::EqTrans {
            label,
            relation,
            left,
            right,
        } => {
            let bundle = relation_bundle(export_env, relation)?;
            let left_formula = expect_formula(left, state)?.clone();
            let right_formula = expect_formula(right, state)?.clone();
            let (lhs, _) = expect_relation(&left_formula, relation, label)?;
            let (_, rhs) = expect_relation(&right_formula, relation, label)?;
            let formula = Formula::rel(relation.clone(), lhs.clone(), rhs.clone());
            let refs = vec![
                resolve_label_ref(left, state)?,
                resolve_label_ref(right, state)?,
            ];
            emit_line(
                EmitLineInput::with_refs(
                    label,
                    &formula,
                    &bundle.transitivity,
                    &refs,
                    &[left_formula, right_formula],
                ),
                mm0_env,
                state,
                out,
            )
        }
        CertStep::EqCongr {
            label,
            relation,
            base,
            child_eq,
            mm0_congr_rule,
            ..
        } => render_eq_congr(
            mm0_env,
            export_env,
            theorem,
            label,
            relation,
            base,
            child_eq,
            mm0_congr_rule,
            state,
            out,
        ),
        CertStep::Transport {
            label,
            relation,
            equivalence,
            proof,
            mm0_transport_rule,
        } => {
            let equivalence_formula = expect_formula(equivalence, state)?.clone();
            let proof_formula = expect_formula(proof, state)?.clone();
            let (_, rhs) = expect_relation(&equivalence_formula, relation, label)?;
            let formula = formula_from_term(rhs, export_env).ok_or_else(|| {
                AufRenderError::FormulaInference {
                    label: label.clone(),
                    reason: "transport target is not a renderable formula".to_owned(),
                }
            })?;
            let refs = vec![
                resolve_label_ref(equivalence, state)?,
                resolve_label_ref(proof, state)?,
            ];
            emit_line(
                EmitLineInput::with_refs(
                    label,
                    &formula,
                    mm0_transport_rule,
                    &refs,
                    &[equivalence_formula, proof_formula],
                ),
                mm0_env,
                state,
                out,
            )
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn render_eq_congr(
    mm0_env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &TheoremDecl,
    label: &Label,
    relation: &str,
    base: &Label,
    child_eq: &Label,
    mm0_congr_rule: &str,
    state: &mut RenderState,
    out: &mut String,
) -> Result<(), AufRenderError> {
    let base_formula = expect_formula(base, state)?.clone();
    let child_formula = expect_formula(child_eq, state)?.clone();
    let (base_lhs, base_rhs) = expect_relation(&base_formula, relation, label)?;
    let (_, child_lhs, child_rhs) = expect_any_relation(&child_formula, label)?;
    let mut congr_source = base_rhs.clone();
    let congr_target = replace_child(&mut congr_source, child_lhs, child_rhs).ok_or_else(|| {
        AufRenderError::FormulaInference {
            label: label.clone(),
            reason: "child equality does not occur in congruence base".to_owned(),
        }
    })?;
    let aux_formula = Formula::rel(relation.to_owned(), base_rhs.clone(), congr_target.clone());
    let final_formula = Formula::rel(relation.to_owned(), base_lhs.clone(), congr_target.clone());
    let child_ref = resolve_label_ref(child_eq, state)?;
    let (congr_refs, congr_ref_formulas) = congruence_application_refs(
        CongruenceRefInput {
            label,
            old_term: base_rhs,
            new_term: &congr_target,
            child_ref,
            child_formula,
            theorem,
        },
        mm0_env,
        export_env,
        state,
        out,
    )?;

    if base_lhs == base_rhs {
        emit_line(
            EmitLineInput::with_refs(
                label,
                &aux_formula,
                mm0_congr_rule,
                &congr_refs,
                &congr_ref_formulas,
            ),
            mm0_env,
            state,
            out,
        )?;
        return Ok(());
    }

    let aux_label = fresh_aux_label(label.as_str(), "congr", state);
    emit_line(
        EmitLineInput::with_refs(
            &aux_label,
            &aux_formula,
            mm0_congr_rule,
            &congr_refs,
            &congr_ref_formulas,
        ),
        mm0_env,
        state,
        out,
    )?;

    let bundle = relation_bundle(export_env, relation)?;
    let refs = vec![
        resolve_label_ref(base, state)?,
        resolve_label_ref(&aux_label, state)?,
    ];
    emit_line(
        EmitLineInput::with_refs(
            label,
            &final_formula,
            &bundle.transitivity,
            &refs,
            &[base_formula, aux_formula],
        ),
        mm0_env,
        state,
        out,
    )
}

struct CongruenceRefInput<'a> {
    label: &'a Label,
    old_term: &'a Term,
    new_term: &'a Term,
    child_ref: RenderRef,
    child_formula: Formula,
    theorem: &'a TheoremDecl,
}

fn congruence_application_refs(
    input: CongruenceRefInput<'_>,
    mm0_env: &Mm0Env,
    export_env: &ExportEnv,
    state: &mut RenderState,
    out: &mut String,
) -> Result<(Vec<RenderRef>, Vec<Formula>), AufRenderError> {
    let (old_args, new_args) = congruent_application_args(input.old_term, input.new_term)
        .ok_or_else(|| AufRenderError::FormulaInference {
            label: input.label.clone(),
            reason: "congruence theorem target is not a matching application".to_owned(),
        })?;
    let Formula::Rel {
        rel: child_rel,
        lhs: child_lhs,
        rhs: child_rhs,
    } = &input.child_formula
    else {
        return Err(AufRenderError::FormulaInference {
            label: input.label.clone(),
            reason: "congruence child proof is not a relation".to_owned(),
        });
    };

    let mut refs = Vec::new();
    let mut formulas = Vec::new();
    for (idx, (old_arg, new_arg)) in old_args.iter().zip(new_args).enumerate() {
        if old_arg == new_arg {
            let Some(relation) = relation_for_render_term(old_arg, input.theorem, export_env)
            else {
                continue;
            };
            let formula = Formula::rel(relation.clone(), old_arg.clone(), old_arg.clone());
            let label = render_reflexivity_helper(
                input.label.as_str(),
                idx,
                &relation,
                old_arg,
                &formula,
                mm0_env,
                export_env,
                state,
                out,
            )?;
            refs.push(resolve_label_ref(&label, state)?);
            formulas.push(formula);
        } else if child_lhs == old_arg && child_rhs == new_arg {
            relation_bundle(export_env, child_rel)?;
            refs.push(input.child_ref.clone());
            formulas.push(input.child_formula.clone());
        } else {
            return Err(AufRenderError::FormulaInference {
                label: input.label.clone(),
                reason: "congruence changed an argument without a proof".to_owned(),
            });
        }
    }
    Ok((refs, formulas))
}

#[allow(clippy::too_many_arguments)]
fn render_reflexivity_helper(
    base_label: &str,
    child_index: usize,
    relation: &str,
    term: &Term,
    formula: &Formula,
    mm0_env: &Mm0Env,
    export_env: &ExportEnv,
    state: &mut RenderState,
    out: &mut String,
) -> Result<Label, AufRenderError> {
    let key = (relation.to_owned(), term.clone());
    if let Some(label) = state.label_by_refl.get(&key) {
        return Ok(label.clone());
    }
    let label = fresh_aux_label(base_label, &format!("refl_{child_index}"), state);
    let bundle = relation_bundle(export_env, relation)?;
    emit_line(
        EmitLineInput::no_refs(&label, formula, &bundle.reflexivity),
        mm0_env,
        state,
        out,
    )?;
    state.label_by_refl.insert(key, label.clone());
    Ok(label)
}

fn congruent_application_args<'a>(
    old: &'a Term,
    new: &'a Term,
) -> Option<(&'a [Term], &'a [Term])> {
    let Term::App {
        head: old_head,
        args: old_args,
    } = old
    else {
        return None;
    };
    let Term::App {
        head: new_head,
        args: new_args,
    } = new
    else {
        return None;
    };
    if old_head == new_head && old_args.len() == new_args.len() {
        Some((old_args, new_args))
    } else {
        None
    }
}

struct EmitLineInput<'a> {
    label: &'a Label,
    formula: &'a Formula,
    rule: &'a str,
    refs: &'a [RenderRef],
    ref_formulas: &'a [Formula],
    initial_bindings: BTreeMap<String, BindingValue>,
}

impl<'a> EmitLineInput<'a> {
    fn no_refs(label: &'a Label, formula: &'a Formula, rule: &'a str) -> Self {
        Self {
            label,
            formula,
            rule,
            refs: &[],
            ref_formulas: &[],
            initial_bindings: BTreeMap::new(),
        }
    }

    fn with_refs(
        label: &'a Label,
        formula: &'a Formula,
        rule: &'a str,
        refs: &'a [RenderRef],
        ref_formulas: &'a [Formula],
    ) -> Self {
        Self {
            label,
            formula,
            rule,
            refs,
            ref_formulas,
            initial_bindings: BTreeMap::new(),
        }
    }
}

fn emit_line(
    input: EmitLineInput<'_>,
    mm0_env: &Mm0Env,
    state: &mut RenderState,
    out: &mut String,
) -> Result<(), AufRenderError> {
    let theorem = mm0_env
        .theorem(input.rule)
        .ok_or_else(|| AufRenderError::UnknownRule {
            rule: input.rule.to_owned(),
        })?;
    let bindings = infer_bindings(
        theorem,
        input.formula,
        input.ref_formulas,
        input.initial_bindings,
        input.label,
    )?;

    write!(
        out,
        "{}: {} by {}",
        input.label.as_str(),
        render_math_formula(input.formula, state)?,
        input.rule
    )
    .expect("write to string");
    if state.format.explicitness == AufRenderExplicitness::Explicit && !bindings.is_empty() {
        let rendered = bindings
            .iter()
            .map(|(name, value)| {
                render_binding_value(value, state)
                    .map(|rendered| format!("{name} := $ {rendered} $"))
            })
            .collect::<Result<Vec<_>, _>>()?
            .join(", ");
        write!(out, " ({rendered})").expect("write to string");
    }
    let refs = input
        .refs
        .iter()
        .map(RenderRef::text)
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(out, " [{refs}]").expect("write to string");

    state.emitted_labels.insert(input.label.as_str().to_owned());
    state
        .formulas
        .insert(input.label.clone(), input.formula.clone());
    state.refs.insert(
        input.label.clone(),
        RenderRef::Line(input.label.as_str().to_owned()),
    );
    state.last_emitted = Some(input.label.clone());
    Ok(())
}

fn infer_bindings(
    theorem: &TheoremDecl,
    formula: &Formula,
    ref_formulas: &[Formula],
    mut bindings: BTreeMap<String, BindingValue>,
    label: &Label,
) -> Result<BTreeMap<String, BindingValue>, AufRenderError> {
    let binder_names = theorem
        .binders
        .iter()
        .map(|binder| binder.name.as_str())
        .collect::<BTreeSet<_>>();
    if !unify_formula(
        &theorem.conclusion,
        formula,
        &binder_names,
        theorem,
        &mut bindings,
    )? {
        return Err(AufRenderError::RuleMismatch {
            rule: theorem.name.clone(),
            label: label.clone(),
        });
    }
    if theorem.hypotheses.len() != ref_formulas.len() {
        return Err(AufRenderError::RuleMismatch {
            rule: theorem.name.clone(),
            label: label.clone(),
        });
    }
    for (pattern, actual) in theorem.hypotheses.iter().zip(ref_formulas) {
        if !unify_formula(pattern, actual, &binder_names, theorem, &mut bindings)? {
            return Err(AufRenderError::RuleMismatch {
                rule: theorem.name.clone(),
                label: label.clone(),
            });
        }
    }

    let mut ordered = BTreeMap::new();
    for binder in &theorem.binders {
        let Some(value) = bindings.get(&binder.name) else {
            return Err(AufRenderError::MissingBinding {
                rule: theorem.name.clone(),
                binder: binder.name.clone(),
            });
        };
        ordered.insert(binder.name.clone(), value.clone());
    }
    validate_bound_binder_instantiations(theorem, &ordered)?;
    Ok(ordered)
}

fn validate_bound_binder_instantiations(
    theorem: &TheoremDecl,
    bindings: &BTreeMap<String, BindingValue>,
) -> Result<(), AufRenderError> {
    let mut seen = BTreeSet::new();
    for binder in theorem
        .binders
        .iter()
        .filter(|binder| binder.kind == BinderKind::Bound)
    {
        let Some(BindingValue::Term(Term::Var { name })) = bindings.get(&binder.name) else {
            return Err(AufRenderError::BoundBinderNonVariable {
                rule: theorem.name.clone(),
                binder: binder.name.clone(),
            });
        };
        if !seen.insert(name.clone()) {
            return Err(AufRenderError::DuplicateBoundBinderInstantiation {
                rule: theorem.name.clone(),
                binder: binder.name.clone(),
                variable: name.clone(),
            });
        }
    }
    Ok(())
}

fn unify_formula(
    pattern: &crate::mm0::Formula,
    actual: &Formula,
    binder_names: &BTreeSet<&str>,
    theorem: &TheoremDecl,
    bindings: &mut BTreeMap<String, BindingValue>,
) -> Result<bool, AufRenderError> {
    let Some(expr) = pattern.expr.as_ref() else {
        return Ok(false);
    };
    unify_formula_expr(expr, actual, binder_names, theorem, bindings)
}

fn unify_formula_expr(
    pattern: &MathExpr,
    actual: &Formula,
    binder_names: &BTreeSet<&str>,
    theorem: &TheoremDecl,
    bindings: &mut BTreeMap<String, BindingValue>,
) -> Result<bool, AufRenderError> {
    match pattern {
        MathExpr::Atom { name } if binder_names.contains(name.as_str()) => {
            insert_binding(
                theorem,
                bindings,
                name,
                BindingValue::Formula(actual.clone()),
            )?;
            Ok(true)
        }
        MathExpr::Atom { name } => Ok(matches!(actual, Formula::Atom { pred, args }
            if pred == name && args.is_empty())),
        MathExpr::App { head, args } => match actual {
            Formula::Rel { rel, lhs, rhs } if head == rel && args.len() == 2 => {
                Ok(unify_term(&args[0], lhs, binder_names, theorem, bindings)?
                    && unify_term(&args[1], rhs, binder_names, theorem, bindings)?)
            }
            Formula::Atom {
                pred,
                args: actual_args,
            } if head == pred && args.len() == actual_args.len() => {
                for (pattern_arg, actual_arg) in args.iter().zip(actual_args) {
                    if !unify_term(pattern_arg, actual_arg, binder_names, theorem, bindings)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        },
    }
}

fn unify_term(
    pattern: &MathExpr,
    actual: &Term,
    binder_names: &BTreeSet<&str>,
    theorem: &TheoremDecl,
    bindings: &mut BTreeMap<String, BindingValue>,
) -> Result<bool, AufRenderError> {
    match pattern {
        MathExpr::Atom { name } if binder_names.contains(name.as_str()) => {
            insert_binding(theorem, bindings, name, BindingValue::Term(actual.clone()))?;
            Ok(true)
        }
        MathExpr::Atom { name } => Ok(matches!(actual, Term::Var { name: found } if found == name)),
        MathExpr::App { head, args } => {
            let Term::App {
                head: actual_head,
                args: actual_args,
            } = actual
            else {
                return Ok(false);
            };
            if head != actual_head || args.len() != actual_args.len() {
                return Ok(false);
            }
            for (pattern_arg, actual_arg) in args.iter().zip(actual_args) {
                if !unify_term(pattern_arg, actual_arg, binder_names, theorem, bindings)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
    }
}

fn insert_binding(
    theorem: &TheoremDecl,
    bindings: &mut BTreeMap<String, BindingValue>,
    name: &str,
    value: BindingValue,
) -> Result<(), AufRenderError> {
    match bindings.get(name) {
        Some(existing) if existing != &value => Err(AufRenderError::InconsistentBinding {
            rule: theorem.name.clone(),
            binder: name.to_owned(),
        }),
        Some(_) => Ok(()),
        None => {
            bindings.insert(name.to_owned(), value);
            Ok(())
        }
    }
}

fn render_explicit_bindings(
    bindings: &[(String, TermOrFormula)],
) -> BTreeMap<String, BindingValue> {
    let mut rendered = BTreeMap::new();
    for (name, value) in bindings {
        let value = match value {
            TermOrFormula::Term { term } => BindingValue::Term(term.clone()),
            TermOrFormula::Formula { formula } => BindingValue::Formula(formula.clone()),
        };
        rendered.insert(name.clone(), value);
    }
    rendered
}

fn resolve_refs(refs: &[Ref], state: &RenderState) -> Result<Vec<RenderRef>, AufRenderError> {
    refs.iter()
        .map(|reference| match reference {
            Ref::Label { label } => resolve_label_ref(label, state),
            Ref::Hyp { hyp_index } => Ok(RenderRef::Hyp(*hyp_index)),
        })
        .collect()
}

fn resolve_label_ref(label: &Label, state: &RenderState) -> Result<RenderRef, AufRenderError> {
    state
        .refs
        .get(label)
        .cloned()
        .ok_or_else(|| AufRenderError::UnknownLabel {
            label: label.clone(),
        })
}

fn formula_for_render_ref(
    reference: &RenderRef,
    theorem: &TheoremDecl,
    export_env: &ExportEnv,
    state: &RenderState,
) -> Result<Formula, AufRenderError> {
    match reference {
        RenderRef::Hyp(index) => theorem
            .hypotheses
            .get(index.saturating_sub(1))
            .and_then(|formula| crate::cert::formula_from_mm0(formula, export_env))
            .ok_or_else(|| AufRenderError::BadHypothesis {
                label: Label::new(format!("#{index}")),
                hyp_index: *index,
            }),
        RenderRef::Line(label) => state
            .formulas
            .get(&Label::new(label.clone()))
            .cloned()
            .ok_or_else(|| AufRenderError::UnknownLabel {
                label: Label::new(label.clone()),
            }),
    }
}

fn expect_formula<'a>(
    label: &Label,
    state: &'a RenderState,
) -> Result<&'a Formula, AufRenderError> {
    state
        .formulas
        .get(label)
        .ok_or_else(|| AufRenderError::UnknownLabel {
            label: label.clone(),
        })
}

fn expect_relation<'a>(
    formula: &'a Formula,
    relation: &str,
    label: &Label,
) -> Result<(&'a Term, &'a Term), AufRenderError> {
    match formula {
        Formula::Rel { rel, lhs, rhs } if rel == relation => Ok((lhs, rhs)),
        _ => Err(AufRenderError::FormulaInference {
            label: label.clone(),
            reason: format!("expected relation `{relation}`"),
        }),
    }
}

fn expect_any_relation<'a>(
    formula: &'a Formula,
    label: &Label,
) -> Result<(&'a str, &'a Term, &'a Term), AufRenderError> {
    match formula {
        Formula::Rel { rel, lhs, rhs } => Ok((rel, lhs, rhs)),
        _ => Err(AufRenderError::FormulaInference {
            label: label.clone(),
            reason: "expected a relation proof".to_owned(),
        }),
    }
}

fn relation_bundle<'a>(
    export_env: &'a ExportEnv,
    relation: &str,
) -> Result<&'a RelationBundle, AufRenderError> {
    export_env
        .relations
        .values()
        .find(|bundle| bundle.relation == relation)
        .ok_or_else(|| AufRenderError::UnknownRelation {
            relation: relation.to_owned(),
        })
}

fn formula_from_term(term: &Term, export_env: &ExportEnv) -> Option<Formula> {
    match term {
        Term::Var { name } => Some(Formula::atom(name.clone(), Vec::new())),
        Term::App { head, args } if args.len() == 2 && is_relation(export_env, head) => {
            Some(Formula::rel(head.clone(), args[0].clone(), args[1].clone()))
        }
        Term::App { head, args } => Some(Formula::atom(head.clone(), args.clone())),
        Term::Lit { .. } => None,
    }
}

fn is_relation(export_env: &ExportEnv, head: &str) -> bool {
    export_env
        .relations
        .values()
        .any(|bundle| bundle.relation == head)
}

fn relation_for_render_term(
    term: &Term,
    theorem: &TheoremDecl,
    export_env: &ExportEnv,
) -> Option<String> {
    let sort = match term {
        Term::Var { name } => theorem
            .binders
            .iter()
            .find(|binder| binder.name == *name)
            .map(|binder| binder.sort.as_str())
            .or_else(|| export_env.term(name).map(|term| term.result_sort.as_str()))?,
        Term::App { head, .. } => export_env.term(head)?.result_sort.as_str(),
        Term::Lit { .. } => return None,
    };
    export_env
        .relations
        .get(sort)
        .map(|bundle| bundle.relation.clone())
}

fn replace_child(term: &mut Term, old: &Term, new: &Term) -> Option<Term> {
    if term == old {
        *term = new.clone();
        return Some(term.clone());
    }
    let Term::App { args, .. } = term else {
        return None;
    };
    for arg in args {
        if replace_child(arg, old, new).is_some() {
            return Some(term.clone());
        }
    }
    None
}

fn fresh_aux_label(base: &str, suffix: &str, state: &RenderState) -> Label {
    let mut idx = 0;
    loop {
        let candidate = if idx == 0 {
            format!("{base}__{suffix}")
        } else {
            format!("{base}__{suffix}_{idx}")
        };
        if !state.emitted_labels.contains(&candidate) {
            return Label::new(candidate);
        }
        idx += 1;
    }
}

fn render_math_formula(formula: &Formula, state: &RenderState) -> Result<String, AufRenderError> {
    Ok(format!(
        "$ {} $",
        render_formula_body_with_state(formula, state)?
    ))
}

fn render_formula_body_with_state(
    formula: &Formula,
    state: &RenderState,
) -> Result<String, AufRenderError> {
    if let Some(notation) = &state.notation {
        return notation.render_formula(formula);
    }
    render_formula_body(formula)
}

fn render_binding_value(
    value: &BindingValue,
    state: &RenderState,
) -> Result<String, AufRenderError> {
    match value {
        BindingValue::Term(term) => {
            if let Some(notation) = &state.notation {
                notation.render_term(term)
            } else {
                render_term_binding_body(term)
            }
        }
        BindingValue::Formula(formula) => render_formula_body_with_state(formula, state),
    }
}

fn render_formula_body(formula: &Formula) -> Result<String, AufRenderError> {
    match formula {
        Formula::Atom { pred, args } => render_head_args(pred, args),
        Formula::Rel { rel, lhs, rhs } => Ok(format!(
            "{} {} {}",
            rel,
            render_term_body(lhs)?,
            render_term_body(rhs)?
        )),
    }
}

fn render_head_args(head: &str, args: &[Term]) -> Result<String, AufRenderError> {
    if args.is_empty() {
        return Ok(head.to_owned());
    }
    let args = args
        .iter()
        .map(render_term_body)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!("{} {}", head, args.join(" ")))
}

fn render_term_binding_body(term: &Term) -> Result<String, AufRenderError> {
    match term {
        Term::App { head, args } if !args.is_empty() => {
            let args = args
                .iter()
                .map(render_term_body)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!("{} {}", head, args.join(" ")))
        }
        _ => render_term_body(term),
    }
}

fn render_term_body(term: &Term) -> Result<String, AufRenderError> {
    match term {
        Term::Var { name } => Ok(name.clone()),
        Term::App { head, args } => {
            if args.is_empty() {
                return Ok(head.clone());
            }
            let args = args
                .iter()
                .map(render_term_body)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!("({} {})", head, args.join(" ")))
        }
        Term::Lit { literal } => Err(AufRenderError::UnsupportedLiteral {
            literal: literal.clone(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::{AufRenderFormat, AufRenderOptions, render_certificate};
    use crate::cert::{CertStep, Certificate, Formula, Label, Term};
    use crate::export::ExportEnv;
    use crate::mm0::parse_env;

    #[test]
    fn renders_explicit_rule_bindings() {
        let env = parse_env(
            r#"
sort s;
provable sort wff;
term f (x: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
theorem target (x: s): $ eq (f x) x $;
"#,
        )
        .unwrap();
        let export = ExportEnv::from_mm0(&env).unwrap();
        let cert = Certificate::new(vec![CertStep::RuleApply {
            label: Label::from("l1"),
            formula: Formula::rel("eq", Term::app("f", vec![Term::var("x")]), Term::var("x")),
            mm0_rule: "f_id".to_owned(),
            bindings: Vec::new(),
            refs: Vec::new(),
        }]);

        let rendered =
            render_certificate(&env, &export, "target", &cert, AufRenderOptions::default())
                .unwrap();

        assert!(rendered.text.contains("l1: $ eq (f x) x $ by f_id"));
        assert!(rendered.text.contains("(x := $ x $) []"));
    }

    #[test]
    fn renders_implicit_rule_bindings() {
        let env = parse_env(
            r#"
sort s;
provable sort wff;
term f (x: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
theorem target (x: s): $ eq (f x) x $;
"#,
        )
        .unwrap();
        let export = ExportEnv::from_mm0(&env).unwrap();
        let cert = Certificate::new(vec![CertStep::RuleApply {
            label: Label::from("l1"),
            formula: Formula::rel("eq", Term::app("f", vec![Term::var("x")]), Term::var("x")),
            mm0_rule: "f_id".to_owned(),
            bindings: Vec::new(),
            refs: Vec::new(),
        }]);
        let options = AufRenderOptions {
            output_mode: crate::OutputMode::Fragment,
            format: AufRenderFormat::implicit(),
        };

        let rendered = render_certificate(&env, &export, "target", &cert, options).unwrap();

        assert!(rendered.text.contains("l1: $ eq (f x) x $ by f_id []"));
        assert!(!rendered.text.contains(":="));
    }
}
