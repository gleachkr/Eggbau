use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::export::{
    ConversionRule, ExportEnv, ExportTermKind, ExportUse, HornPremise, SaturationHornLaw,
};
use crate::mm0::{Formula as Mm0Formula, MathExpr, Mm0Env};

pub const CERT_FORMAT_VERSION: u32 = 1;

/// Stable eggbau certificate IR between egglog proofs and Aufbau rendering.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Certificate {
    pub format_version: u32,
    pub steps: Vec<CertStep>,
}

impl Certificate {
    pub fn empty() -> Self {
        Self {
            format_version: CERT_FORMAT_VERSION,
            steps: Vec::new(),
        }
    }

    pub fn new(steps: Vec<CertStep>) -> Self {
        Self {
            format_version: CERT_FORMAT_VERSION,
            steps,
        }
    }

    pub fn to_pretty_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("certificate JSON should render")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Label(pub String);

impl Label {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for Label {
    fn from(value: &str) -> Self {
        Self::new(value)
    }
}

impl From<String> for Label {
    fn from(value: String) -> Self {
        Self::new(value)
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Literal {
    String { value: String },
    Integer { value: String },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Term {
    Var { name: String },
    App { head: String, args: Vec<Term> },
    Lit { literal: Literal },
}

impl Term {
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var { name: name.into() }
    }

    pub fn app(head: impl Into<String>, args: Vec<Term>) -> Self {
        Self::App {
            head: head.into(),
            args,
        }
    }

    pub fn head(&self) -> Option<&str> {
        match self {
            Self::Var { name } => Some(name),
            Self::App { head, .. } => Some(head),
            Self::Lit { .. } => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Formula {
    Atom { pred: String, args: Vec<Term> },
    Rel { rel: String, lhs: Term, rhs: Term },
}

impl Formula {
    pub fn atom(pred: impl Into<String>, args: Vec<Term>) -> Self {
        Self::Atom {
            pred: pred.into(),
            args,
        }
    }

    pub fn rel(rel: impl Into<String>, lhs: Term, rhs: Term) -> Self {
        Self::Rel {
            rel: rel.into(),
            lhs,
            rhs,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TermOrFormula {
    Term { term: Term },
    Formula { formula: Formula },
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Ref {
    Label { label: Label },
    Hyp { hyp_index: usize },
}

impl Ref {
    pub fn label(label: impl Into<Label>) -> Self {
        Self::Label {
            label: label.into(),
        }
    }

    pub fn hyp(hyp_index: usize) -> Self {
        Self::Hyp { hyp_index }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum CertStep {
    Hyp {
        label: Label,
        hyp_index: usize,
        formula: Formula,
    },
    RuleApply {
        label: Label,
        formula: Formula,
        mm0_rule: String,
        bindings: Vec<(String, TermOrFormula)>,
        refs: Vec<Ref>,
    },
    EqRefl {
        label: Label,
        relation: String,
        term: Term,
    },
    EqSym {
        label: Label,
        relation: String,
        source: Label,
    },
    EqTrans {
        label: Label,
        relation: String,
        left: Label,
        right: Label,
    },
    EqCongr {
        label: Label,
        relation: String,
        head: String,
        child_index: usize,
        base: Label,
        child_eq: Label,
        mm0_congr_rule: String,
    },
    Transport {
        label: Label,
        relation: String,
        equivalence: Label,
        proof: Label,
        mm0_transport_rule: String,
    },
}

impl CertStep {
    pub fn label(&self) -> &Label {
        match self {
            Self::Hyp { label, .. }
            | Self::RuleApply { label, .. }
            | Self::EqRefl { label, .. }
            | Self::EqSym { label, .. }
            | Self::EqTrans { label, .. }
            | Self::EqCongr { label, .. }
            | Self::Transport { label, .. } => label,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidationOptions<'a> {
    pub theorem_hypotheses: Option<&'a [Formula]>,
    pub target: &'a Formula,
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum CertValidationError {
    #[error("unsupported certificate format version {found}; expected {expected}")]
    UnsupportedVersion { found: u32, expected: u32 },

    #[error("certificate has no proof steps")]
    EmptyCertificate,

    #[error("empty certificate label at step {step}")]
    EmptyLabel { step: usize },

    #[error("duplicate certificate label `{label}` at step {step}")]
    DuplicateLabel { label: Label, step: usize },

    #[error("reference to unknown or future label `{label}` at step {step}")]
    BadLabelRef { label: Label, step: usize },

    #[error("reference to unknown hypothesis #{hyp_index} at step {step}")]
    BadHypRef { hyp_index: usize, step: usize },

    #[error("hypothesis step {step} uses invalid hypothesis index {hyp_index}")]
    BadHypStep { hyp_index: usize, step: usize },

    #[error("hypothesis #{hyp_index} formula does not match theorem")]
    HypMismatch { hyp_index: usize },

    #[error("unknown relation `{relation}` at step {step}")]
    UnknownRelation { relation: String, step: usize },

    #[error("rule `{rule}` at step {step} is not authorized for export")]
    UnauthorizedRule { rule: String, step: usize },

    #[error("transitivity step {step} does not have matching middle terms")]
    TransitivityMismatch { step: usize },

    #[error("step {step} expected a relation proof in `{relation}`")]
    ExpectedRelation { relation: String, step: usize },

    #[error("congruence rule `{rule}` at step {step} is not known")]
    UnknownCongruence { rule: String, step: usize },

    #[error("congruence step {step} has child index {child_index} out of range")]
    BadCongruenceChild { child_index: usize, step: usize },

    #[error("congruence step {step} uses head `{found}`, expected `{expected}`")]
    CongruenceHeadMismatch {
        expected: String,
        found: String,
        step: usize,
    },

    #[error("congruence step {step} child equality does not match the base term")]
    CongruenceChildMismatch { step: usize },

    #[error("transport theorem `{rule}` at step {step} is not in relation bundle")]
    BadTransportRule { rule: String, step: usize },

    #[error("transport step {step} cannot turn the equivalence side into a formula")]
    BadTransportFormula { step: usize },

    #[error("transport step {step} proof does not match equivalence left side")]
    TransportProofMismatch { step: usize },

    #[error("final certificate formula does not match the target theorem")]
    FinalGoalMismatch,
}

pub fn validate_certificate(
    certificate: &Certificate,
    export_env: &ExportEnv,
    target: &Formula,
) -> Result<(), CertValidationError> {
    validate_certificate_with_options(
        certificate,
        export_env,
        ValidationOptions {
            theorem_hypotheses: None,
            target,
        },
    )
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CompactCertificateStats {
    pub before_steps: usize,
    pub after_steps: usize,
}

impl CompactCertificateStats {
    pub fn removed_steps(&self) -> usize {
        self.before_steps.saturating_sub(self.after_steps)
    }
}

pub fn compact_certificate_for_theorem(
    certificate: &Certificate,
    mm0_env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &str,
) -> Result<(Certificate, CompactCertificateStats), CertValidationError> {
    let theorem = mm0_env
        .theorem(theorem)
        .ok_or(CertValidationError::FinalGoalMismatch)?;
    let hypotheses = theorem
        .hypotheses
        .iter()
        .map(|formula| formula_from_mm0(formula, export_env))
        .collect::<Option<Vec<_>>>()
        .ok_or(CertValidationError::FinalGoalMismatch)?;
    let target = formula_from_mm0(&theorem.conclusion, export_env)
        .ok_or(CertValidationError::FinalGoalMismatch)?;
    compact_certificate_with_options(
        certificate,
        export_env,
        ValidationOptions {
            theorem_hypotheses: Some(&hypotheses),
            target: &target,
        },
    )
}

pub fn compact_certificate(
    certificate: &Certificate,
    export_env: &ExportEnv,
    target: &Formula,
) -> Result<(Certificate, CompactCertificateStats), CertValidationError> {
    compact_certificate_with_options(
        certificate,
        export_env,
        ValidationOptions {
            theorem_hypotheses: None,
            target,
        },
    )
}

pub fn validate_certificate_for_theorem(
    certificate: &Certificate,
    mm0_env: &Mm0Env,
    export_env: &ExportEnv,
    theorem: &str,
) -> Result<(), CertValidationError> {
    let theorem = mm0_env
        .theorem(theorem)
        .ok_or(CertValidationError::FinalGoalMismatch)?;
    let hypotheses = theorem
        .hypotheses
        .iter()
        .map(|formula| formula_from_mm0(formula, export_env))
        .collect::<Option<Vec<_>>>()
        .ok_or(CertValidationError::FinalGoalMismatch)?;
    let target = formula_from_mm0(&theorem.conclusion, export_env)
        .ok_or(CertValidationError::FinalGoalMismatch)?;

    validate_certificate_with_options(
        certificate,
        export_env,
        ValidationOptions {
            theorem_hypotheses: Some(&hypotheses),
            target: &target,
        },
    )
}

pub fn validate_certificate_with_options(
    certificate: &Certificate,
    export_env: &ExportEnv,
    options: ValidationOptions<'_>,
) -> Result<(), CertValidationError> {
    let final_formula = infer_certificate_formulas(certificate, export_env, options.clone())?.1;
    if final_formula.as_ref() == Some(options.target) {
        Ok(())
    } else {
        Err(CertValidationError::FinalGoalMismatch)
    }
}

fn compact_certificate_with_options(
    certificate: &Certificate,
    export_env: &ExportEnv,
    options: ValidationOptions<'_>,
) -> Result<(Certificate, CompactCertificateStats), CertValidationError> {
    validate_certificate_with_options(certificate, export_env, options.clone())?;

    let context = ValidationContext::new(export_env);
    let mut formulas = BTreeMap::<Label, Formula>::new();
    let mut first_by_formula = BTreeMap::<Formula, Label>::new();
    let mut aliases = BTreeMap::<Label, Label>::new();
    let mut steps = Vec::new();

    for (idx, step) in certificate.steps.iter().enumerate() {
        let step_no = idx + 1;
        let is_final = idx + 1 == certificate.steps.len();
        let original_label = step.label().clone();
        let step = remap_step_refs_only(step, &aliases);
        let formula = infer_step_formula(
            &step,
            &formulas,
            &context,
            options.theorem_hypotheses,
            step_no,
        )?;

        if !is_final && let Some(first_label) = first_by_formula.get(&formula) {
            aliases.insert(original_label, first_label.clone());
            continue;
        }

        first_by_formula
            .entry(formula.clone())
            .or_insert_with(|| original_label.clone());
        formulas.insert(original_label, formula);
        steps.push(step);
    }

    let compact = Certificate::new(steps);
    validate_certificate_with_options(&compact, export_env, options)?;
    let after_steps = compact.steps.len();
    Ok((
        compact,
        CompactCertificateStats {
            before_steps: certificate.steps.len(),
            after_steps,
        },
    ))
}

fn infer_certificate_formulas(
    certificate: &Certificate,
    export_env: &ExportEnv,
    options: ValidationOptions<'_>,
) -> Result<(BTreeMap<Label, Formula>, Option<Formula>), CertValidationError> {
    if certificate.format_version != CERT_FORMAT_VERSION {
        return Err(CertValidationError::UnsupportedVersion {
            found: certificate.format_version,
            expected: CERT_FORMAT_VERSION,
        });
    }
    if certificate.steps.is_empty() {
        return Err(CertValidationError::EmptyCertificate);
    }

    let context = ValidationContext::new(export_env);
    let mut formulas = BTreeMap::<Label, Formula>::new();
    let mut last_formula = None;

    for (idx, step) in certificate.steps.iter().enumerate() {
        let step_no = idx + 1;
        let label = step.label();
        if label.as_str().is_empty() {
            return Err(CertValidationError::EmptyLabel { step: step_no });
        }
        if formulas.contains_key(label) {
            return Err(CertValidationError::DuplicateLabel {
                label: label.clone(),
                step: step_no,
            });
        }

        let formula = infer_step_formula(
            step,
            &formulas,
            &context,
            options.theorem_hypotheses,
            step_no,
        )?;
        formulas.insert(label.clone(), formula.clone());
        last_formula = Some(formula);
    }

    Ok((formulas, last_formula))
}

struct ValidationContext<'a> {
    export_env: &'a ExportEnv,
    relation_by_name: BTreeMap<&'a str, &'a str>,
    authorized_rules: BTreeSet<&'a str>,
    congruence_by_rule: BTreeMap<&'a str, (&'a str, &'a str)>,
}

impl<'a> ValidationContext<'a> {
    fn new(export_env: &'a ExportEnv) -> Self {
        let relation_by_name = export_env
            .relations
            .iter()
            .map(|(sort, bundle)| (bundle.relation.as_str(), sort.as_str()))
            .collect();
        let authorized_rules = export_env
            .assertions
            .iter()
            .filter(|assertion| {
                matches!(
                    assertion.use_kind,
                    ExportUse::Relation | ExportUse::Congruence | ExportUse::Saturation
                )
            })
            .map(|assertion| assertion.theorem.as_str())
            .collect();
        let congruence_by_rule = export_env
            .congruences
            .values()
            .map(|law| {
                (
                    law.theorem.as_str(),
                    (law.term.as_str(), law.relation.as_str()),
                )
            })
            .collect();
        Self {
            export_env,
            relation_by_name,
            authorized_rules,
            congruence_by_rule,
        }
    }

    fn relation_known(&self, relation: &str) -> bool {
        self.relation_by_name.contains_key(relation)
    }

    fn relation_has_transport(&self, relation: &str, rule: &str) -> bool {
        self.export_env
            .relations
            .values()
            .any(|bundle| bundle.relation == relation && bundle.transport.as_deref() == Some(rule))
    }
}

fn infer_step_formula(
    step: &CertStep,
    formulas: &BTreeMap<Label, Formula>,
    context: &ValidationContext<'_>,
    theorem_hypotheses: Option<&[Formula]>,
    step_no: usize,
) -> Result<Formula, CertValidationError> {
    match step {
        CertStep::Hyp {
            hyp_index, formula, ..
        } => {
            if *hyp_index == 0 {
                return Err(CertValidationError::BadHypStep {
                    hyp_index: *hyp_index,
                    step: step_no,
                });
            }
            if let Some(hypotheses) = theorem_hypotheses {
                let expected = hypotheses.get(*hyp_index - 1).ok_or({
                    CertValidationError::BadHypStep {
                        hyp_index: *hyp_index,
                        step: step_no,
                    }
                })?;
                if expected != formula {
                    return Err(CertValidationError::HypMismatch {
                        hyp_index: *hyp_index,
                    });
                }
            }
            Ok(formula.clone())
        }
        CertStep::RuleApply {
            formula,
            mm0_rule,
            refs,
            ..
        } => {
            if !context.authorized_rules.contains(mm0_rule.as_str()) {
                return Err(CertValidationError::UnauthorizedRule {
                    rule: mm0_rule.clone(),
                    step: step_no,
                });
            }
            for proof_ref in refs {
                validate_ref(proof_ref, formulas, theorem_hypotheses, step_no)?;
            }
            Ok(formula.clone())
        }
        CertStep::EqRefl { relation, term, .. } => {
            ensure_relation(context, relation, step_no)?;
            Ok(Formula::Rel {
                rel: relation.clone(),
                lhs: term.clone(),
                rhs: term.clone(),
            })
        }
        CertStep::EqSym {
            relation, source, ..
        } => {
            ensure_relation(context, relation, step_no)?;
            let source = expect_label(source, formulas, step_no)?;
            let (lhs, rhs) = expect_relation_formula(source, relation, step_no)?;
            Ok(Formula::Rel {
                rel: relation.clone(),
                lhs: rhs.clone(),
                rhs: lhs.clone(),
            })
        }
        CertStep::EqTrans {
            relation,
            left,
            right,
            ..
        } => {
            ensure_relation(context, relation, step_no)?;
            let left = expect_label(left, formulas, step_no)?;
            let right = expect_label(right, formulas, step_no)?;
            let (left_lhs, left_rhs) = expect_relation_formula(left, relation, step_no)?;
            let (right_lhs, right_rhs) = expect_relation_formula(right, relation, step_no)?;
            if left_rhs != right_lhs {
                return Err(CertValidationError::TransitivityMismatch { step: step_no });
            }
            Ok(Formula::Rel {
                rel: relation.clone(),
                lhs: left_lhs.clone(),
                rhs: right_rhs.clone(),
            })
        }
        CertStep::EqCongr {
            relation,
            head,
            child_index,
            base,
            child_eq,
            mm0_congr_rule,
            ..
        } => infer_congruence_formula(
            CongruenceStepView {
                relation,
                head,
                child_index: *child_index,
                base,
                child_eq,
                mm0_congr_rule,
            },
            formulas,
            context,
            step_no,
        ),
        CertStep::Transport {
            relation,
            equivalence,
            proof,
            mm0_transport_rule,
            ..
        } => infer_transport_formula(
            relation,
            equivalence,
            proof,
            mm0_transport_rule,
            formulas,
            context,
            step_no,
        ),
    }
}

struct CongruenceStepView<'a> {
    relation: &'a str,
    head: &'a str,
    child_index: usize,
    base: &'a Label,
    child_eq: &'a Label,
    mm0_congr_rule: &'a str,
}

fn infer_congruence_formula(
    input: CongruenceStepView<'_>,
    formulas: &BTreeMap<Label, Formula>,
    context: &ValidationContext<'_>,
    step_no: usize,
) -> Result<Formula, CertValidationError> {
    ensure_relation(context, input.relation, step_no)?;
    let Some((congr_head, congr_relation)) = context.congruence_by_rule.get(input.mm0_congr_rule)
    else {
        return Err(CertValidationError::UnknownCongruence {
            rule: input.mm0_congr_rule.to_owned(),
            step: step_no,
        });
    };
    if *congr_head != input.head || *congr_relation != input.relation {
        return Err(CertValidationError::CongruenceHeadMismatch {
            expected: (*congr_head).to_owned(),
            found: input.head.to_owned(),
            step: step_no,
        });
    }

    let base = expect_label(input.base, formulas, step_no)?;
    let child_eq = expect_label(input.child_eq, formulas, step_no)?;
    let (base_lhs, base_rhs) = expect_relation_formula(base, input.relation, step_no)?;
    let (child_relation, child_lhs, child_rhs) = expect_any_relation_formula(child_eq, step_no)?;
    ensure_relation(context, child_relation, step_no)?;

    let Term::App {
        head: right_head,
        args: right_args,
    } = base_rhs
    else {
        return Err(CertValidationError::CongruenceHeadMismatch {
            expected: input.head.to_owned(),
            found: base_rhs.head().unwrap_or("<literal>").to_owned(),
            step: step_no,
        });
    };
    if right_head != input.head {
        return Err(CertValidationError::CongruenceHeadMismatch {
            expected: input.head.to_owned(),
            found: right_head.clone(),
            step: step_no,
        });
    }
    if input.child_index >= right_args.len() {
        return Err(CertValidationError::BadCongruenceChild {
            child_index: input.child_index,
            step: step_no,
        });
    }
    if &right_args[input.child_index] != child_lhs {
        return Err(CertValidationError::CongruenceChildMismatch { step: step_no });
    }

    let mut rhs_args = right_args.clone();
    rhs_args[input.child_index] = child_rhs.clone();
    Ok(Formula::Rel {
        rel: input.relation.to_owned(),
        lhs: base_lhs.clone(),
        rhs: Term::App {
            head: right_head.clone(),
            args: rhs_args,
        },
    })
}

fn infer_transport_formula(
    relation: &str,
    equivalence: &Label,
    proof: &Label,
    mm0_transport_rule: &str,
    formulas: &BTreeMap<Label, Formula>,
    context: &ValidationContext<'_>,
    step_no: usize,
) -> Result<Formula, CertValidationError> {
    ensure_relation(context, relation, step_no)?;
    if !context.relation_has_transport(relation, mm0_transport_rule) {
        return Err(CertValidationError::BadTransportRule {
            rule: mm0_transport_rule.to_owned(),
            step: step_no,
        });
    }

    let equivalence = expect_label(equivalence, formulas, step_no)?;
    let proof = expect_label(proof, formulas, step_no)?;
    let (lhs, rhs) = expect_relation_formula(equivalence, relation, step_no)?;
    let source = formula_from_term(lhs, context)
        .ok_or(CertValidationError::BadTransportFormula { step: step_no })?;
    if &source != proof {
        return Err(CertValidationError::TransportProofMismatch { step: step_no });
    }
    formula_from_term(rhs, context)
        .ok_or(CertValidationError::BadTransportFormula { step: step_no })
}

fn validate_ref(
    proof_ref: &Ref,
    formulas: &BTreeMap<Label, Formula>,
    theorem_hypotheses: Option<&[Formula]>,
    step_no: usize,
) -> Result<(), CertValidationError> {
    match proof_ref {
        Ref::Label { label } => {
            expect_label(label, formulas, step_no)?;
            Ok(())
        }
        Ref::Hyp { hyp_index } => {
            if *hyp_index == 0
                || theorem_hypotheses.is_some_and(|hypotheses| *hyp_index > hypotheses.len())
            {
                return Err(CertValidationError::BadHypRef {
                    hyp_index: *hyp_index,
                    step: step_no,
                });
            }
            Ok(())
        }
    }
}

fn ensure_relation(
    context: &ValidationContext<'_>,
    relation: &str,
    step_no: usize,
) -> Result<(), CertValidationError> {
    if context.relation_known(relation) {
        Ok(())
    } else {
        Err(CertValidationError::UnknownRelation {
            relation: relation.to_owned(),
            step: step_no,
        })
    }
}

fn expect_label<'a>(
    label: &Label,
    formulas: &'a BTreeMap<Label, Formula>,
    step_no: usize,
) -> Result<&'a Formula, CertValidationError> {
    formulas
        .get(label)
        .ok_or_else(|| CertValidationError::BadLabelRef {
            label: label.clone(),
            step: step_no,
        })
}

fn expect_relation_formula<'a>(
    formula: &'a Formula,
    relation: &str,
    step_no: usize,
) -> Result<(&'a Term, &'a Term), CertValidationError> {
    match formula {
        Formula::Rel { rel, lhs, rhs } if rel == relation => Ok((lhs, rhs)),
        _ => Err(CertValidationError::ExpectedRelation {
            relation: relation.to_owned(),
            step: step_no,
        }),
    }
}

fn expect_any_relation_formula(
    formula: &Formula,
    step_no: usize,
) -> Result<(&str, &Term, &Term), CertValidationError> {
    match formula {
        Formula::Rel { rel, lhs, rhs } => Ok((rel, lhs, rhs)),
        _ => Err(CertValidationError::ExpectedRelation {
            relation: "<any>".to_owned(),
            step: step_no,
        }),
    }
}

pub fn formula_from_mm0(formula: &Mm0Formula, export_env: &ExportEnv) -> Option<Formula> {
    let expr = formula.expr.as_ref()?;
    match expr {
        MathExpr::Atom { name } => Some(Formula::Atom {
            pred: name.clone(),
            args: Vec::new(),
        }),
        MathExpr::App { head, args } if args.len() == 2 && is_relation(export_env, head) => {
            Some(Formula::Rel {
                rel: head.clone(),
                lhs: term_from_mm0(&args[0]),
                rhs: term_from_mm0(&args[1]),
            })
        }
        MathExpr::App { head, args } => Some(Formula::Atom {
            pred: head.clone(),
            args: args.iter().map(term_from_mm0).collect(),
        }),
    }
}

pub fn term_from_mm0(expr: &MathExpr) -> Term {
    match expr {
        MathExpr::Atom { name } => Term::Var { name: name.clone() },
        MathExpr::App { head, args } => Term::App {
            head: head.clone(),
            args: args.iter().map(term_from_mm0).collect(),
        },
    }
}

fn formula_from_term(term: &Term, context: &ValidationContext<'_>) -> Option<Formula> {
    match term {
        Term::Var { name } => Some(Formula::Atom {
            pred: name.clone(),
            args: Vec::new(),
        }),
        Term::App { head, args } if args.len() == 2 && context.relation_known(head) => {
            Some(Formula::Rel {
                rel: head.clone(),
                lhs: args[0].clone(),
                rhs: args[1].clone(),
            })
        }
        Term::App { head, args } => Some(Formula::Atom {
            pred: head.clone(),
            args: args.clone(),
        }),
        Term::Lit { .. } => None,
    }
}

fn is_relation(export_env: &ExportEnv, head: &str) -> bool {
    export_env
        .relations
        .values()
        .any(|bundle| bundle.relation == head)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LocalProofVar {
    pub egglog_constructor: String,
    pub source_name: String,
    pub sort: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HypothesisFiat {
    pub proposition: String,
    pub hyp_index: usize,
    pub formula: Formula,
    pub needs_symmetry: bool,
}

#[derive(Clone, Debug)]
pub struct EqualityTranslationInput<'a> {
    pub proof_store: &'a egglog::proof::ProofStore,
    pub root: egglog::proof::ProofId,
    pub export_env: &'a ExportEnv,
    pub relation: &'a str,
    pub target_lhs_egglog: &'a str,
    pub target_rhs_egglog: &'a str,
    pub local_vars: Vec<LocalProofVar>,
    pub hypothesis_fiats: Vec<HypothesisFiat>,
}

#[derive(Clone, Debug)]
pub struct FactTranslationInput<'a> {
    pub proof_store: &'a egglog::proof::ProofStore,
    pub root: egglog::proof::ProofId,
    pub export_env: &'a ExportEnv,
    pub target_pred: &'a str,
    pub target_args_egglog: Vec<String>,
    pub local_vars: Vec<LocalProofVar>,
    pub hypothesis_fiats: Vec<HypothesisFiat>,
    pub extra_equalities: Vec<ExtraEqualityCertificate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExtraEqualityCertificate {
    pub sort: String,
    pub relation: String,
    pub lhs_egglog: String,
    pub rhs_egglog: String,
    pub certificate: Certificate,
}

#[derive(Debug, Error, Eq, PartialEq)]
pub enum TranslateError {
    #[error("egglog proof does not contain equality target {lhs} = {rhs}")]
    TargetEqualityNotFound { lhs: String, rhs: String },

    #[error("unsupported egglog proof justification MergeFn for function {function}")]
    UnsupportedMergeFn { function: String },

    #[error("egglog proof used unapproved Fiat proposition: {proposition}")]
    UnapprovedFiat { proposition: String },

    #[error("egglog rule `{rule}` is not exported as a saturation conversion")]
    UnknownRule { rule: String },

    #[error("no MM0 congruence theorem is known for head `{head}`")]
    MissingCongruence { head: String },

    #[error("egglog term `{term}` has no MM0 rendering")]
    UnknownTerm { term: String },

    #[error("egglog term `{term}` is not a first-order application")]
    NotApplication { term: String },

    #[error("cannot parse generated egglog term pattern `{pattern}`")]
    PatternParse { pattern: String },

    #[error("cannot align egglog rule `{rule}` with its MM0 conversion law")]
    RuleReconstructionMismatch { rule: String },

    #[error("egglog rule `{rule}` is not exported as a saturation Horn rule")]
    UnknownHornRule { rule: String },

    #[error("Horn rule `{rule}` has {expected} premises, but egglog supplied {actual}")]
    HornPremiseCount {
        rule: String,
        expected: usize,
        actual: usize,
    },

    #[error("fact proof step {label} did not match expected Horn premise")]
    HornPremiseMismatch { label: Label },

    #[error("proof step {label} did not produce a usable formula")]
    MissingFormula { label: Label },

    #[error("fact congruence for `{pred}` needs relation `{relation}` to have transport")]
    MissingFactTransport { pred: String, relation: String },

    #[error("cannot infer an MM0 relation for egglog equality `{proposition}`")]
    CannotInferRelation { proposition: String },

    #[error("need an equality proof for `{lhs_egglog}` = `{rhs_egglog}`")]
    MissingEqualityProof {
        sort: String,
        relation: String,
        lhs_egglog: String,
        rhs_egglog: String,
    },
}

pub fn translate_equality_proof(
    input: EqualityTranslationInput<'_>,
) -> Result<Certificate, TranslateError> {
    let indexes = TranslateIndexes::new(input.export_env, &input.local_vars);
    let mut ctx = TranslateCtx {
        input,
        indexes,
        labels: HashMap::new(),
        label_by_refl: BTreeMap::new(),
        label_by_hyp: BTreeMap::new(),
        steps: Vec::new(),
        next_label: 1,
    };
    let target = ctx
        .find_target_proof(ctx.input.root, false)?
        .or(ctx.find_target_proof(ctx.input.root, true)?)
        .ok_or_else(|| TranslateError::TargetEqualityNotFound {
            lhs: ctx.input.target_lhs_egglog.to_owned(),
            rhs: ctx.input.target_rhs_egglog.to_owned(),
        })?;
    let mut final_label = ctx.translate_proof(target.proof_id)?;
    if target.needs_symmetry {
        let label = ctx.fresh_label("eq_sym");
        ctx.steps.push(CertStep::EqSym {
            label: label.clone(),
            relation: ctx.input.relation.to_owned(),
            source: final_label,
        });
        final_label = label;
    }
    let _ = final_label;
    Ok(Certificate::new(ctx.steps))
}

#[derive(Clone, Copy, Debug)]
struct TargetProof {
    proof_id: egglog::proof::ProofId,
    needs_symmetry: bool,
}

struct TranslateCtx<'a> {
    input: EqualityTranslationInput<'a>,
    indexes: TranslateIndexes,
    labels: HashMap<egglog::proof::ProofId, Label>,
    label_by_refl: BTreeMap<(String, Term), Label>,
    label_by_hyp: BTreeMap<(usize, Formula, bool), Label>,
    steps: Vec<CertStep>,
    next_label: usize,
}

impl<'a> TranslateCtx<'a> {
    fn find_target_proof(
        &self,
        proof_id: egglog::proof::ProofId,
        allow_reverse: bool,
    ) -> Result<Option<TargetProof>, TranslateError> {
        let mut visited = HashSet::new();
        self.find_target_inner(proof_id, allow_reverse, &mut visited)
    }

    fn find_target_inner(
        &self,
        proof_id: egglog::proof::ProofId,
        allow_reverse: bool,
        visited: &mut HashSet<egglog::proof::ProofId>,
    ) -> Result<Option<TargetProof>, TranslateError> {
        if !visited.insert(proof_id) {
            return Ok(None);
        }
        let proof = self.input.proof_store.get(proof_id);
        let proposition = proof.proposition();
        let lhs = self.term_string(proposition.lhs());
        let rhs = self.term_string(proposition.rhs());
        if lhs == self.input.target_lhs_egglog && rhs == self.input.target_rhs_egglog {
            return Ok(Some(TargetProof {
                proof_id,
                needs_symmetry: false,
            }));
        }
        if allow_reverse
            && lhs == self.input.target_rhs_egglog
            && rhs == self.input.target_lhs_egglog
        {
            return Ok(Some(TargetProof {
                proof_id,
                needs_symmetry: true,
            }));
        }

        for child in proof_children(proof.justification()) {
            if let Some(found) = self.find_target_inner(child, allow_reverse, visited)? {
                return Ok(Some(found));
            }
        }
        Ok(None)
    }

    fn translate_proof(
        &mut self,
        proof_id: egglog::proof::ProofId,
    ) -> Result<Label, TranslateError> {
        if let Some(label) = self.labels.get(&proof_id) {
            return Ok(label.clone());
        }

        let proof = self.input.proof_store.get(proof_id);
        let label = match proof.justification() {
            egglog::proof::Justification::Fiat => self.translate_fiat(proof_id)?,
            egglog::proof::Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                let substitution = substitution
                    .iter()
                    .map(|(name, term)| (name.clone(), *term))
                    .collect::<Vec<_>>();
                self.translate_rule(proof_id, name, premise_proofs, &substitution)?
            }
            egglog::proof::Justification::Trans(left, right) => {
                let relation = self.relation_for_proof(proof_id)?;
                let left = self.translate_proof(*left)?;
                let right = self.translate_proof(*right)?;
                let label = self.fresh_label("eq_trans");
                self.steps.push(CertStep::EqTrans {
                    label: label.clone(),
                    relation,
                    left,
                    right,
                });
                label
            }
            egglog::proof::Justification::Sym(inner) => {
                let relation = self.relation_for_proof(proof_id)?;
                let source = self.translate_proof(*inner)?;
                let label = self.fresh_label("eq_sym");
                self.steps.push(CertStep::EqSym {
                    label: label.clone(),
                    relation,
                    source,
                });
                label
            }
            egglog::proof::Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => self.translate_congruence(*proof, *child_index, *child_proof)?,
            egglog::proof::Justification::MergeFn { function, .. } => {
                return Err(TranslateError::UnsupportedMergeFn {
                    function: function.clone(),
                });
            }
        };

        self.labels.insert(proof_id, label.clone());
        Ok(label)
    }

    fn translate_fiat(
        &mut self,
        proof_id: egglog::proof::ProofId,
    ) -> Result<Label, TranslateError> {
        let proof = self.input.proof_store.get(proof_id);
        let proposition = self.proposition_string(proof.proposition());
        if let Some(hypothesis) = self
            .input
            .hypothesis_fiats
            .iter()
            .find(|hypothesis| hypothesis.proposition == proposition)
            .cloned()
        {
            return self.emit_hypothesis(hypothesis);
        }

        let lhs = proof.proposition().lhs();
        let rhs = proof.proposition().rhs();
        if self.term_string(lhs) != self.term_string(rhs) {
            return Err(TranslateError::UnapprovedFiat { proposition });
        }
        let term = self.term_from_egg(lhs)?;
        let relation =
            self.relation_for_term(&term)
                .ok_or_else(|| TranslateError::CannotInferRelation {
                    proposition: term_debug(&term),
                })?;
        self.emit_reflexivity(relation, term)
    }

    fn translate_rule(
        &mut self,
        proof_id: egglog::proof::ProofId,
        name: &str,
        premise_proofs: &[egglog::proof::ProofId],
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Label, TranslateError> {
        if let Some(label) = self.translate_reflexive_rule_proof(proof_id)? {
            return Ok(label);
        }

        let Some(rule) = self.indexes.conversion_rules.get(name).cloned() else {
            return Err(TranslateError::UnknownRule {
                rule: name.to_owned(),
            });
        };
        let source = self.instantiate_pattern(&rule.source_egglog, substitution)?;
        let target = self.instantiate_pattern(&rule.target_egglog, substitution)?;
        let relation = self.indexes.rule_to_relation[name].clone();
        let mut rule_label =
            self.emit_rule_source_to_target(name, &rule, &relation, &source, &target);

        let actual = if let Some(first_premise) = premise_proofs.first() {
            let premise = self.input.proof_store.get(*first_premise);
            let (premise_lhs, premise_rhs) = self.proposition_terms(premise.proposition())?;
            if premise_lhs == source && premise_rhs == source {
                source.clone()
            } else if premise_rhs == source {
                let premise_label = self.translate_proof(*first_premise)?;
                let trans_label = self.fresh_label("eq_trans");
                self.steps.push(CertStep::EqTrans {
                    label: trans_label.clone(),
                    relation: relation.clone(),
                    left: premise_label,
                    right: rule_label,
                });
                rule_label = trans_label;
                premise_lhs
            } else if premise_lhs == source {
                let premise_label = self.translate_proof(*first_premise)?;
                let sym_label = self.fresh_label("eq_sym");
                self.steps.push(CertStep::EqSym {
                    label: sym_label.clone(),
                    relation: relation.clone(),
                    source: premise_label,
                });
                let trans_label = self.fresh_label("eq_trans");
                self.steps.push(CertStep::EqTrans {
                    label: trans_label.clone(),
                    relation: relation.clone(),
                    left: sym_label,
                    right: rule_label,
                });
                rule_label = trans_label;
                premise_rhs
            } else {
                return Err(TranslateError::RuleReconstructionMismatch {
                    rule: name.to_owned(),
                });
            }
        } else {
            source.clone()
        };

        let proof = self.input.proof_store.get(proof_id);
        let (proof_lhs, proof_rhs) = self.proposition_terms(proof.proposition())?;
        if proof_lhs == actual && proof_rhs == target {
            Ok(rule_label)
        } else if proof_lhs == target && proof_rhs == actual {
            let sym_label = self.fresh_label("eq_sym");
            self.steps.push(CertStep::EqSym {
                label: sym_label.clone(),
                relation: relation.clone(),
                source: rule_label,
            });
            Ok(sym_label)
        } else {
            Err(TranslateError::RuleReconstructionMismatch {
                rule: name.to_owned(),
            })
        }
    }

    fn translate_reflexive_rule_proof(
        &mut self,
        proof_id: egglog::proof::ProofId,
    ) -> Result<Option<Label>, TranslateError> {
        let proof = self.input.proof_store.get(proof_id);
        let (lhs, rhs) = self.proposition_terms(proof.proposition())?;
        if lhs != rhs {
            return Ok(None);
        }
        let Some(relation) = self.relation_for_term(&lhs) else {
            return Ok(None);
        };
        self.emit_reflexivity(relation, lhs).map(Some)
    }

    fn emit_rule_source_to_target(
        &mut self,
        name: &str,
        rule: &ConversionRule,
        relation: &str,
        source: &Term,
        target: &Term,
    ) -> Label {
        let label = self.fresh_label("rule");
        if rule.needs_symmetry_for_mm0 {
            self.steps.push(CertStep::RuleApply {
                label: label.clone(),
                formula: Formula::rel(relation, target.clone(), source.clone()),
                mm0_rule: self.indexes.rule_to_theorem[name].clone(),
                bindings: Vec::new(),
                refs: Vec::new(),
            });
            let sym_label = self.fresh_label("eq_sym");
            self.steps.push(CertStep::EqSym {
                label: sym_label.clone(),
                relation: relation.to_owned(),
                source: label,
            });
            sym_label
        } else {
            self.steps.push(CertStep::RuleApply {
                label: label.clone(),
                formula: Formula::rel(relation, source.clone(), target.clone()),
                mm0_rule: self.indexes.rule_to_theorem[name].clone(),
                bindings: Vec::new(),
                refs: Vec::new(),
            });
            label
        }
    }

    fn instantiate_pattern(
        &self,
        pattern: &str,
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Term, TranslateError> {
        let template =
            EggPatternParser::new(pattern)
                .parse()
                .map_err(|()| TranslateError::PatternParse {
                    pattern: pattern.to_owned(),
                })?;
        self.instantiate_template(&template, substitution)
    }

    fn instantiate_template(
        &self,
        template: &EggTemplate,
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Term, TranslateError> {
        match template {
            EggTemplate::Atom(name) => {
                if let Some((_, term_id)) = substitution.iter().find(|(key, _)| key == name) {
                    return self.term_from_egg(*term_id);
                }
                let rendered = self
                    .indexes
                    .head_name(name)
                    .ok_or_else(|| TranslateError::UnknownTerm { term: name.clone() })?;
                Ok(Term::Var {
                    name: rendered.to_owned(),
                })
            }
            EggTemplate::App { head, args } => {
                let rendered = self
                    .indexes
                    .head_name(head)
                    .ok_or_else(|| TranslateError::UnknownTerm { term: head.clone() })?;
                let args = args
                    .iter()
                    .map(|arg| self.instantiate_template(arg, substitution))
                    .collect::<Result<Vec<_>, _>>()?;
                if args.is_empty() {
                    Ok(Term::Var {
                        name: rendered.to_owned(),
                    })
                } else {
                    Ok(Term::App {
                        head: rendered.to_owned(),
                        args,
                    })
                }
            }
        }
    }

    fn translate_congruence(
        &mut self,
        base: egglog::proof::ProofId,
        child_index: usize,
        child_proof: egglog::proof::ProofId,
    ) -> Result<Label, TranslateError> {
        let base_label = self.translate_proof(base)?;
        let child_label = self.translate_proof(child_proof)?;
        let base_proof = self.input.proof_store.get(base);
        let (_, rhs) = self.proposition_terms(base_proof.proposition())?;
        let Term::App { head, args: _ } = rhs else {
            return Err(TranslateError::NotApplication {
                term: self.term_string(base_proof.proposition().rhs()),
            });
        };
        let Some(congruence) = self.input.export_env.congruences.get(&head) else {
            return Err(TranslateError::MissingCongruence { head });
        };
        let label = self.fresh_label("eq_congr");
        self.steps.push(CertStep::EqCongr {
            label: label.clone(),
            relation: congruence.relation.clone(),
            head,
            child_index,
            base: base_label,
            child_eq: child_label,
            mm0_congr_rule: congruence.theorem.clone(),
        });
        Ok(label)
    }

    fn relation_for_proof(
        &self,
        proof_id: egglog::proof::ProofId,
    ) -> Result<String, TranslateError> {
        let proof = self.input.proof_store.get(proof_id);
        let lhs = self.term_from_egg(proof.proposition().lhs())?;
        self.relation_for_term(&lhs)
            .ok_or_else(|| TranslateError::CannotInferRelation {
                proposition: self.proposition_string(proof.proposition()),
            })
    }

    fn relation_for_term(&self, term: &Term) -> Option<String> {
        let sort = self.indexes.term_sort(term)?;
        self.input
            .export_env
            .relations
            .get(sort)
            .map(|bundle| bundle.relation.clone())
    }

    fn proposition_terms(
        &self,
        proposition: &egglog::proof::Proposition,
    ) -> Result<(Term, Term), TranslateError> {
        Ok((
            self.term_from_egg(proposition.lhs())?,
            self.term_from_egg(proposition.rhs())?,
        ))
    }

    fn term_from_egg(&self, term_id: egglog::TermId) -> Result<Term, TranslateError> {
        match self.input.proof_store.term_dag().get(term_id) {
            egglog::Term::Var(name) => Ok(Term::Var { name: name.clone() }),
            egglog::Term::Lit(literal) => Ok(Term::Lit {
                literal: Literal::String {
                    value: literal.to_string(),
                },
            }),
            egglog::Term::App(head, args) => {
                let rendered_head = self
                    .indexes
                    .head_name(head)
                    .ok_or_else(|| TranslateError::UnknownTerm { term: head.clone() })?;
                if args.is_empty() {
                    return Ok(Term::Var {
                        name: rendered_head.to_owned(),
                    });
                }
                let args = args
                    .iter()
                    .map(|arg| self.term_from_egg(*arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Term::App {
                    head: rendered_head.to_owned(),
                    args,
                })
            }
        }
    }

    fn emit_hypothesis(&mut self, hypothesis: HypothesisFiat) -> Result<Label, TranslateError> {
        let key = (
            hypothesis.hyp_index,
            hypothesis.formula.clone(),
            hypothesis.needs_symmetry,
        );
        if let Some(label) = self.label_by_hyp.get(&key) {
            return Ok(label.clone());
        }

        let direct_key = (hypothesis.hyp_index, hypothesis.formula.clone(), false);
        let hyp_label = if let Some(label) = self.label_by_hyp.get(&direct_key) {
            label.clone()
        } else {
            let label = self.fresh_label("hyp");
            self.steps.push(CertStep::Hyp {
                label: label.clone(),
                hyp_index: hypothesis.hyp_index,
                formula: hypothesis.formula.clone(),
            });
            self.label_by_hyp.insert(direct_key, label.clone());
            label
        };

        if hypothesis.needs_symmetry {
            let Formula::Rel { rel, .. } = hypothesis.formula else {
                return Err(TranslateError::MissingFormula { label: hyp_label });
            };
            let sym_label = self.fresh_label("eq_sym");
            self.steps.push(CertStep::EqSym {
                label: sym_label.clone(),
                relation: rel,
                source: hyp_label,
            });
            self.label_by_hyp.insert(key, sym_label.clone());
            Ok(sym_label)
        } else {
            Ok(hyp_label)
        }
    }

    fn emit_reflexivity(&mut self, relation: String, term: Term) -> Result<Label, TranslateError> {
        let key = (relation.clone(), term.clone());
        if let Some(label) = self.label_by_refl.get(&key) {
            return Ok(label.clone());
        }
        let label = self.fresh_label("eq_refl");
        self.steps.push(CertStep::EqRefl {
            label: label.clone(),
            relation,
            term,
        });
        self.label_by_refl.insert(key, label.clone());
        Ok(label)
    }

    fn fresh_label(&mut self, prefix: &str) -> Label {
        let label = Label::new(format!("{prefix}_{}", self.next_label));
        self.next_label += 1;
        label
    }

    fn term_string(&self, term_id: egglog::TermId) -> String {
        self.input.proof_store.term_dag().to_string(term_id)
    }

    fn proposition_string(&self, proposition: &egglog::proof::Proposition) -> String {
        format!(
            "{} = {}",
            self.term_string(proposition.lhs()),
            self.term_string(proposition.rhs())
        )
    }
}

pub fn translate_fact_proof(
    input: FactTranslationInput<'_>,
) -> Result<Certificate, TranslateError> {
    let indexes = TranslateIndexes::new(input.export_env, &input.local_vars);
    let mut ctx = FactTranslateCtx {
        input,
        indexes,
        labels: HashMap::new(),
        formulas: BTreeMap::new(),
        label_by_refl: BTreeMap::new(),
        label_by_hyp: BTreeMap::new(),
        label_by_transport: BTreeMap::new(),
        steps: Vec::new(),
        next_label: 1,
    };
    let final_label = ctx.translate_proof(ctx.input.root)?;
    let target = ctx.target_formula()?;
    let final_label = ctx.align_formula(final_label, &target)?;
    let final_formula = ctx.formula_for(&final_label)?.clone();
    if final_formula != target {
        return Err(TranslateError::HornPremiseMismatch { label: final_label });
    }
    Ok(Certificate::new(ctx.steps))
}

struct FactTranslateCtx<'a> {
    input: FactTranslationInput<'a>,
    indexes: TranslateIndexes,
    labels: HashMap<egglog::proof::ProofId, Label>,
    formulas: BTreeMap<Label, Formula>,
    label_by_refl: BTreeMap<(String, Term), Label>,
    label_by_hyp: BTreeMap<(usize, Formula, bool), Label>,
    label_by_transport: BTreeMap<(String, Label, Label, String), Label>,
    steps: Vec<CertStep>,
    next_label: usize,
}

impl<'a> FactTranslateCtx<'a> {
    fn translate_proof(
        &mut self,
        proof_id: egglog::proof::ProofId,
    ) -> Result<Label, TranslateError> {
        if let Some(label) = self.labels.get(&proof_id) {
            return Ok(label.clone());
        }

        let proof = self.input.proof_store.get(proof_id);
        let label = match proof.justification() {
            egglog::proof::Justification::Fiat => self.translate_fiat(proof_id)?,
            egglog::proof::Justification::Rule {
                name,
                premise_proofs,
                substitution,
            } => {
                let substitution = substitution
                    .iter()
                    .map(|(name, term)| (name.clone(), *term))
                    .collect::<Vec<_>>();
                self.translate_rule(name, premise_proofs, &substitution)?
            }
            egglog::proof::Justification::Trans(left, right) => {
                let left_label = self.translate_proof(*left)?;
                let right_label = self.translate_proof(*right)?;
                let left_formula = self.formula_for(&left_label)?.clone();
                let right_formula = self.formula_for(&right_label)?.clone();
                let Formula::Rel { rel, lhs, rhs } = left_formula else {
                    return Err(TranslateError::MissingFormula { label: left_label });
                };
                let Formula::Rel {
                    rel: right_rel,
                    lhs: right_lhs,
                    rhs: right_rhs,
                } = right_formula
                else {
                    return Err(TranslateError::MissingFormula { label: right_label });
                };
                if rel != right_rel || rhs != right_lhs {
                    return Err(TranslateError::RuleReconstructionMismatch {
                        rule: "Trans".to_owned(),
                    });
                }
                let label = self.fresh_label("eq_trans");
                let formula = Formula::rel(rel.clone(), lhs, right_rhs);
                self.push_step(
                    label.clone(),
                    formula.clone(),
                    CertStep::EqTrans {
                        label: label.clone(),
                        relation: rel,
                        left: left_label,
                        right: right_label,
                    },
                );
                label
            }
            egglog::proof::Justification::Sym(inner) => {
                let source = self.translate_proof(*inner)?;
                let source_formula = self.formula_for(&source)?.clone();
                let Formula::Rel { rel, lhs, rhs } = source_formula else {
                    return Err(TranslateError::MissingFormula { label: source });
                };
                let label = self.fresh_label("eq_sym");
                let formula = Formula::rel(rel.clone(), rhs, lhs);
                self.push_step(
                    label.clone(),
                    formula,
                    CertStep::EqSym {
                        label: label.clone(),
                        relation: rel,
                        source,
                    },
                );
                label
            }
            egglog::proof::Justification::Congr {
                proof,
                child_index,
                child_proof,
            } => self.translate_congruence(*proof, *child_index, *child_proof)?,
            egglog::proof::Justification::MergeFn { function, .. } => {
                return Err(TranslateError::UnsupportedMergeFn {
                    function: function.clone(),
                });
            }
        };

        self.labels.insert(proof_id, label.clone());
        Ok(label)
    }

    fn translate_fiat(
        &mut self,
        proof_id: egglog::proof::ProofId,
    ) -> Result<Label, TranslateError> {
        let proof = self.input.proof_store.get(proof_id);
        let proposition = self.proposition_string(proof.proposition());
        if let Some(hypothesis) = self
            .input
            .hypothesis_fiats
            .iter()
            .find(|hypothesis| hypothesis.proposition == proposition)
            .cloned()
        {
            return self.emit_hypothesis(hypothesis);
        }

        let lhs = proof.proposition().lhs();
        let rhs = proof.proposition().rhs();
        if self.term_string(lhs) != self.term_string(rhs) {
            return Err(TranslateError::UnapprovedFiat { proposition });
        }
        let term = self.term_from_egg(lhs)?;
        if self.fact_formula_from_term(&term).is_some() {
            return Err(TranslateError::UnapprovedFiat { proposition });
        }
        let relation = self
            .relation_for_term(&term)
            .ok_or(TranslateError::CannotInferRelation { proposition })?;
        self.emit_reflexivity(relation, term)
    }

    fn translate_rule(
        &mut self,
        name: &str,
        premise_proofs: &[egglog::proof::ProofId],
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Label, TranslateError> {
        if self.indexes.conversion_rules.contains_key(name) {
            return self.translate_conversion_rule(name, premise_proofs, substitution);
        }

        let Some(law) = self.indexes.horn_rules.get(name).cloned() else {
            return Err(TranslateError::UnknownHornRule {
                rule: name.to_owned(),
            });
        };
        let expected_count = law.hypotheses.len();
        if expected_count != premise_proofs.len() {
            return Err(TranslateError::HornPremiseCount {
                rule: name.to_owned(),
                expected: expected_count,
                actual: premise_proofs.len(),
            });
        }

        let mut refs = Vec::new();
        for (premise, proof_id) in law.hypotheses.iter().zip(premise_proofs.iter()) {
            let label = self.translate_proof(*proof_id)?;
            let expected = self.instantiate_horn_premise(premise, substitution)?;
            let label = self.align_formula(label, &expected)?;
            let actual = self.formula_for(&label)?.clone();
            if actual != expected {
                return Err(TranslateError::HornPremiseMismatch { label });
            }
            refs.push(Ref::label(label));
        }

        let formula = self.instantiate_fact_pattern(&law.conclusion, substitution)?;
        let label = self.fresh_label("horn");
        self.push_step(
            label.clone(),
            formula.clone(),
            CertStep::RuleApply {
                label: label.clone(),
                formula,
                mm0_rule: law.theorem,
                bindings: Vec::new(),
                refs,
            },
        );
        Ok(label)
    }

    fn align_formula(&mut self, label: Label, expected: &Formula) -> Result<Label, TranslateError> {
        let actual = self.formula_for(&label)?.clone();
        if &actual == expected {
            return Ok(label);
        }
        let Formula::Atom { pred, args } = actual else {
            return Err(TranslateError::HornPremiseMismatch { label });
        };
        let Formula::Atom {
            pred: expected_pred,
            args: expected_args,
        } = expected
        else {
            return Err(TranslateError::HornPremiseMismatch { label });
        };
        if pred != *expected_pred || args.len() != expected_args.len() {
            return Err(TranslateError::HornPremiseMismatch { label });
        }
        self.align_fact(label, pred, args, expected_args)
    }

    fn align_fact(
        &mut self,
        mut label: Label,
        pred: String,
        mut args: Vec<Term>,
        expected_args: &[Term],
    ) -> Result<Label, TranslateError> {
        for (idx, expected) in expected_args.iter().enumerate() {
            if args[idx] == *expected {
                continue;
            }
            let eq = self.equality_label_for_terms(&args[idx], expected)?;
            label = self.translate_fact_congruence(pred.clone(), args.clone(), idx, label, eq)?;
            args[idx] = expected.clone();
        }
        Ok(label)
    }

    fn equality_label_for_terms(
        &mut self,
        lhs: &Term,
        rhs: &Term,
    ) -> Result<Label, TranslateError> {
        let relation =
            self.relation_for_term(lhs)
                .ok_or_else(|| TranslateError::CannotInferRelation {
                    proposition: format!("{} = {}", term_debug(lhs), term_debug(rhs)),
                })?;
        let sort = self.sort_for_relation(&relation).ok_or_else(|| {
            TranslateError::CannotInferRelation {
                proposition: format!("{} = {}", term_debug(lhs), term_debug(rhs)),
            }
        })?;
        if self.relation_for_term(rhs).as_deref() != Some(relation.as_str()) {
            return Err(TranslateError::CannotInferRelation {
                proposition: format!("{} = {}", term_debug(lhs), term_debug(rhs)),
            });
        }
        if let Some(label) = self.find_existing_equality(&relation, lhs, rhs)? {
            return Ok(label);
        }
        self.import_extra_equality(&sort, &relation, lhs, rhs)
    }

    fn find_existing_equality(
        &mut self,
        relation: &str,
        lhs: &Term,
        rhs: &Term,
    ) -> Result<Option<Label>, TranslateError> {
        let formulas = self.formulas.clone();
        for (label, formula) in formulas {
            let Formula::Rel {
                rel,
                lhs: found_lhs,
                rhs: found_rhs,
            } = formula
            else {
                continue;
            };
            if rel != relation {
                continue;
            }
            if found_lhs == *lhs && found_rhs == *rhs {
                return Ok(Some(label));
            }
            if found_lhs == *rhs && found_rhs == *lhs {
                let sym = self.fresh_label("eq_sym");
                self.push_step(
                    sym.clone(),
                    Formula::rel(relation.to_owned(), lhs.clone(), rhs.clone()),
                    CertStep::EqSym {
                        label: sym.clone(),
                        relation: relation.to_owned(),
                        source: label,
                    },
                );
                return Ok(Some(sym));
            }
        }
        Ok(None)
    }

    fn import_extra_equality(
        &mut self,
        sort: &str,
        relation: &str,
        lhs: &Term,
        rhs: &Term,
    ) -> Result<Label, TranslateError> {
        let lhs_egglog = self.render_egglog_term(lhs)?;
        let rhs_egglog = self.render_egglog_term(rhs)?;
        let extra = self
            .input
            .extra_equalities
            .iter()
            .find(|extra| {
                extra.sort == sort
                    && extra.relation == relation
                    && extra.lhs_egglog == lhs_egglog
                    && extra.rhs_egglog == rhs_egglog
            })
            .cloned();
        if let Some(extra) = extra {
            return self.import_equality_certificate(extra, lhs, rhs, false);
        }
        let extra = self
            .input
            .extra_equalities
            .iter()
            .find(|extra| {
                extra.sort == sort
                    && extra.relation == relation
                    && extra.lhs_egglog == rhs_egglog
                    && extra.rhs_egglog == lhs_egglog
            })
            .cloned();
        if let Some(extra) = extra {
            return self.import_equality_certificate(extra, lhs, rhs, true);
        }
        Err(TranslateError::MissingEqualityProof {
            sort: sort.to_owned(),
            relation: relation.to_owned(),
            lhs_egglog,
            rhs_egglog,
        })
    }

    fn import_equality_certificate(
        &mut self,
        extra: ExtraEqualityCertificate,
        lhs: &Term,
        rhs: &Term,
        needs_symmetry: bool,
    ) -> Result<Label, TranslateError> {
        let mut labels = BTreeMap::new();
        let context = ValidationContext::new(self.input.export_env);
        let mut final_label = None;
        for step in extra.certificate.steps {
            let old_label = step.label().clone();
            labels.insert(old_label, self.fresh_label("eq_fallback"));
            let step = remap_step(&step, &labels)?;
            let step_no = self.steps.len() + 1;
            let formula = infer_step_formula(&step, &self.formulas, &context, None, step_no)
                .map_err(|_| TranslateError::RuleReconstructionMismatch {
                    rule: "equality fallback".to_owned(),
                })?;
            let label = step.label().clone();
            self.push_step(label.clone(), formula, step);
            final_label = Some(label);
        }
        let Some(mut label) = final_label else {
            return Err(TranslateError::TargetEqualityNotFound {
                lhs: extra.lhs_egglog,
                rhs: extra.rhs_egglog,
            });
        };
        let expected = Formula::rel(extra.relation.clone(), lhs.clone(), rhs.clone());
        let actual = self.formula_for(&label)?.clone();
        if needs_symmetry {
            let sym = self.fresh_label("eq_sym");
            self.push_step(
                sym.clone(),
                expected.clone(),
                CertStep::EqSym {
                    label: sym.clone(),
                    relation: extra.relation.clone(),
                    source: label,
                },
            );
            label = sym;
        } else if actual != expected {
            return Err(TranslateError::RuleReconstructionMismatch {
                rule: "equality fallback".to_owned(),
            });
        }
        Ok(label)
    }

    fn translate_conversion_rule(
        &mut self,
        name: &str,
        premise_proofs: &[egglog::proof::ProofId],
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Label, TranslateError> {
        let rule = self.indexes.conversion_rules[name].clone();
        let relation = self.indexes.rule_to_relation[name].clone();
        let source = self.instantiate_pattern(&rule.source_egglog, substitution)?;
        let target = self.instantiate_pattern(&rule.target_egglog, substitution)?;
        let mut label = self.fresh_label("rule");
        let direct_formula = if rule.needs_symmetry_for_mm0 {
            Formula::rel(relation.clone(), target.clone(), source.clone())
        } else {
            Formula::rel(relation.clone(), source.clone(), target.clone())
        };
        self.push_step(
            label.clone(),
            direct_formula,
            CertStep::RuleApply {
                label: label.clone(),
                formula: if rule.needs_symmetry_for_mm0 {
                    Formula::rel(relation.clone(), target.clone(), source.clone())
                } else {
                    Formula::rel(relation.clone(), source.clone(), target.clone())
                },
                mm0_rule: self.indexes.rule_to_theorem[name].clone(),
                bindings: Vec::new(),
                refs: Vec::new(),
            },
        );
        if rule.needs_symmetry_for_mm0 {
            let sym = self.fresh_label("eq_sym");
            self.push_step(
                sym.clone(),
                Formula::rel(relation.clone(), source.clone(), target.clone()),
                CertStep::EqSym {
                    label: sym.clone(),
                    relation: relation.clone(),
                    source: label,
                },
            );
            label = sym;
        }
        if let Some(first) = premise_proofs.first() {
            let premise = self.translate_proof(*first)?;
            let premise_formula = self.formula_for(&premise)?.clone();
            let Formula::Rel { lhs, rhs, .. } = premise_formula else {
                return Err(TranslateError::MissingFormula { label: premise });
            };
            if rhs == source {
                let trans = self.fresh_label("eq_trans");
                self.push_step(
                    trans.clone(),
                    Formula::rel(relation.clone(), lhs, target),
                    CertStep::EqTrans {
                        label: trans.clone(),
                        relation,
                        left: premise,
                        right: label,
                    },
                );
                return Ok(trans);
            }
        }
        Ok(label)
    }

    fn translate_congruence(
        &mut self,
        base: egglog::proof::ProofId,
        child_index: usize,
        child_proof: egglog::proof::ProofId,
    ) -> Result<Label, TranslateError> {
        let base_label = self.translate_proof(base)?;
        let child_label = self.translate_proof(child_proof)?;
        let base_formula = self.formula_for(&base_label)?.clone();
        let child_formula = self.formula_for(&child_label)?.clone();

        match base_formula {
            Formula::Atom { pred, args } => {
                self.translate_fact_congruence(pred, args, child_index, base_label, child_label)
            }
            Formula::Rel { rel, rhs, .. } => {
                let Term::App { head, .. } = rhs else {
                    return Err(TranslateError::NotApplication {
                        term: format!("{child_index}"),
                    });
                };
                let Some(congruence) = self.input.export_env.congruences.get(&head) else {
                    return Err(TranslateError::MissingCongruence { head });
                };
                let label = self.fresh_label("eq_congr");
                let formula =
                    self.eq_congr_formula(&rel, &base_label, &child_formula, child_index)?;
                self.push_step(
                    label.clone(),
                    formula,
                    CertStep::EqCongr {
                        label: label.clone(),
                        relation: rel,
                        head,
                        child_index,
                        base: base_label,
                        child_eq: child_label,
                        mm0_congr_rule: congruence.theorem.clone(),
                    },
                );
                Ok(label)
            }
        }
    }

    fn translate_fact_congruence(
        &mut self,
        pred: String,
        args: Vec<Term>,
        child_index: usize,
        base_label: Label,
        child_label: Label,
    ) -> Result<Label, TranslateError> {
        let child_formula = self.formula_for(&child_label)?.clone();
        let Formula::Rel {
            rel: child_relation,
            lhs: child_lhs,
            rhs: child_rhs,
        } = child_formula
        else {
            return Err(TranslateError::MissingFormula { label: child_label });
        };
        if child_index >= args.len() || args[child_index] != child_lhs {
            return Err(TranslateError::HornPremiseMismatch { label: child_label });
        }
        let Some(congruence) = self.input.export_env.congruences.get(&pred) else {
            return Err(TranslateError::MissingCongruence { head: pred });
        };
        let Some(transport) = self.transport_for_relation(&congruence.relation) else {
            return Err(TranslateError::MissingFactTransport {
                pred,
                relation: congruence.relation.clone(),
            });
        };

        let mut new_args = args.clone();
        new_args[child_index] = child_rhs.clone();
        let refs = self.fact_congruence_refs(
            &args,
            &new_args,
            child_index,
            &child_label,
            &child_relation,
        )?;
        let lhs_term = Term::app(pred.clone(), args);
        let rhs_term = Term::app(pred.clone(), new_args.clone());
        let equiv = Formula::rel(congruence.relation.clone(), lhs_term, rhs_term);
        let congr_label = self.fresh_label("fact_congr");
        self.push_step(
            congr_label.clone(),
            equiv.clone(),
            CertStep::RuleApply {
                label: congr_label.clone(),
                formula: equiv,
                mm0_rule: congruence.theorem.clone(),
                bindings: Vec::new(),
                refs,
            },
        );

        let key = (
            congruence.relation.clone(),
            congr_label.clone(),
            base_label.clone(),
            transport.clone(),
        );
        if let Some(label) = self.label_by_transport.get(&key) {
            return Ok(label.clone());
        }
        let label = self.fresh_label("transport");
        let transported = Formula::atom(pred, new_args);
        self.push_step(
            label.clone(),
            transported,
            CertStep::Transport {
                label: label.clone(),
                relation: congruence.relation.clone(),
                equivalence: congr_label,
                proof: base_label,
                mm0_transport_rule: transport,
            },
        );
        self.label_by_transport.insert(key, label.clone());
        Ok(label)
    }

    fn fact_congruence_refs(
        &mut self,
        old_args: &[Term],
        new_args: &[Term],
        child_index: usize,
        child_label: &Label,
        child_relation: &str,
    ) -> Result<Vec<Ref>, TranslateError> {
        let mut refs = Vec::new();
        for (idx, (old_arg, new_arg)) in old_args.iter().zip(new_args).enumerate() {
            if idx == child_index {
                let expected = self.relation_for_term(old_arg).ok_or_else(|| {
                    TranslateError::CannotInferRelation {
                        proposition: term_debug(old_arg),
                    }
                })?;
                if expected != child_relation {
                    return Err(TranslateError::CannotInferRelation {
                        proposition: format!(
                            "{} uses {}, expected {}",
                            term_debug(old_arg),
                            child_relation,
                            expected
                        ),
                    });
                }
                refs.push(Ref::label(child_label.clone()));
            } else if old_arg == new_arg {
                let relation = self.relation_for_term(old_arg).ok_or_else(|| {
                    TranslateError::CannotInferRelation {
                        proposition: term_debug(old_arg),
                    }
                })?;
                let label = self.emit_reflexivity(relation, old_arg.clone())?;
                refs.push(Ref::label(label));
            } else {
                return Err(TranslateError::MissingEqualityProof {
                    sort: "<unknown>".to_owned(),
                    relation: "<unknown>".to_owned(),
                    lhs_egglog: term_debug(old_arg),
                    rhs_egglog: term_debug(new_arg),
                });
            }
        }
        Ok(refs)
    }

    fn eq_congr_formula(
        &self,
        relation: &str,
        base_label: &Label,
        child_formula: &Formula,
        child_index: usize,
    ) -> Result<Formula, TranslateError> {
        let Formula::Rel { lhs, rhs, .. } = self.formula_for(base_label)?.clone() else {
            return Err(TranslateError::MissingFormula {
                label: base_label.clone(),
            });
        };
        let Formula::Rel {
            lhs: child_lhs,
            rhs: child_rhs,
            ..
        } = child_formula.clone()
        else {
            return Err(TranslateError::MissingFormula {
                label: base_label.clone(),
            });
        };
        let Term::App {
            head: lhs_head,
            args: lhs_args,
        } = lhs
        else {
            return Err(TranslateError::NotApplication {
                term: relation.to_owned(),
            });
        };
        let Term::App {
            head: rhs_head,
            mut args,
        } = rhs
        else {
            return Err(TranslateError::NotApplication {
                term: relation.to_owned(),
            });
        };
        if child_index >= args.len() || args[child_index] != child_lhs {
            return Err(TranslateError::HornPremiseMismatch {
                label: base_label.clone(),
            });
        }
        args[child_index] = child_rhs;
        Ok(Formula::rel(
            relation.to_owned(),
            Term::app(lhs_head, lhs_args),
            Term::app(rhs_head, args),
        ))
    }

    fn instantiate_horn_premise(
        &self,
        premise: &HornPremise,
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Formula, TranslateError> {
        match premise {
            HornPremise::Fact(pattern) => self.instantiate_fact_pattern(pattern, substitution),
            HornPremise::Equality(pattern) => Ok(Formula::rel(
                pattern.relation.clone(),
                self.instantiate_pattern(&pattern.lhs_egglog, substitution)?,
                self.instantiate_pattern(&pattern.rhs_egglog, substitution)?,
            )),
        }
    }

    fn instantiate_fact_pattern(
        &self,
        pattern: &crate::export::FactPattern,
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Formula, TranslateError> {
        let args = pattern
            .egglog_arguments
            .iter()
            .map(|arg| self.instantiate_pattern(arg, substitution))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Formula::atom(pattern.relation.clone(), args))
    }

    fn instantiate_pattern(
        &self,
        pattern: &str,
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Term, TranslateError> {
        let template =
            EggPatternParser::new(pattern)
                .parse()
                .map_err(|()| TranslateError::PatternParse {
                    pattern: pattern.to_owned(),
                })?;
        self.instantiate_template(&template, substitution)
    }

    fn instantiate_template(
        &self,
        template: &EggTemplate,
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Term, TranslateError> {
        match template {
            EggTemplate::Atom(name) => {
                if let Some((_, term_id)) = substitution.iter().find(|(key, _)| key == name) {
                    return self.term_from_egg(*term_id);
                }
                let rendered = self
                    .indexes
                    .head_name(name)
                    .ok_or_else(|| TranslateError::UnknownTerm { term: name.clone() })?;
                Ok(Term::var(rendered))
            }
            EggTemplate::App { head, args } => {
                let rendered = self
                    .indexes
                    .head_name(head)
                    .ok_or_else(|| TranslateError::UnknownTerm { term: head.clone() })?;
                let args = args
                    .iter()
                    .map(|arg| self.instantiate_template(arg, substitution))
                    .collect::<Result<Vec<_>, _>>()?;
                if args.is_empty() {
                    Ok(Term::var(rendered))
                } else {
                    Ok(Term::app(rendered, args))
                }
            }
        }
    }

    fn target_formula(&self) -> Result<Formula, TranslateError> {
        let args = self
            .input
            .target_args_egglog
            .iter()
            .map(|arg| self.instantiate_pattern(arg, &[]))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Formula::atom(self.input.target_pred, args))
    }

    fn fact_formula_from_term(&self, term: &Term) -> Option<Formula> {
        match term {
            Term::Var { name } => self
                .input
                .export_env
                .term(name)
                .filter(|term| term.kind == ExportTermKind::FactRelation)
                .map(|_| Formula::atom(name.clone(), Vec::new())),
            Term::App { head, args } => self
                .input
                .export_env
                .term(head)
                .filter(|term| term.kind == ExportTermKind::FactRelation)
                .map(|_| Formula::atom(head.clone(), args.clone())),
            Term::Lit { .. } => None,
        }
    }

    fn relation_for_term(&self, term: &Term) -> Option<String> {
        let sort = self.indexes.term_sort(term)?;
        self.input
            .export_env
            .relations
            .get(sort)
            .map(|bundle| bundle.relation.clone())
    }

    fn sort_for_relation(&self, relation: &str) -> Option<String> {
        self.input
            .export_env
            .relations
            .iter()
            .find(|(_, bundle)| bundle.relation == relation)
            .map(|(sort, _)| sort.clone())
    }

    fn render_egglog_term(&self, term: &Term) -> Result<String, TranslateError> {
        match term {
            Term::Var { name } => self
                .indexes
                .egglog_atom(name)
                .map(ToOwned::to_owned)
                .ok_or_else(|| TranslateError::UnknownTerm { term: name.clone() }),
            Term::App { head, args } => {
                let head = self
                    .indexes
                    .egglog_head(head)
                    .ok_or_else(|| TranslateError::UnknownTerm { term: head.clone() })?;
                let args = args
                    .iter()
                    .map(|arg| self.render_egglog_term(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(render_call(head, &args))
            }
            Term::Lit { .. } => Err(TranslateError::UnknownTerm {
                term: term_debug(term),
            }),
        }
    }

    fn transport_for_relation(&self, relation: &str) -> Option<String> {
        self.input
            .export_env
            .relations
            .values()
            .find(|bundle| bundle.relation == relation)
            .and_then(|bundle| bundle.transport.clone())
    }

    fn term_from_egg(&self, term_id: egglog::TermId) -> Result<Term, TranslateError> {
        match self.input.proof_store.term_dag().get(term_id) {
            egglog::Term::Var(name) => Ok(Term::var(name.clone())),
            egglog::Term::Lit(literal) => Ok(Term::Lit {
                literal: Literal::String {
                    value: literal.to_string(),
                },
            }),
            egglog::Term::App(head, args) => {
                let rendered_head = self
                    .indexes
                    .head_name(head)
                    .ok_or_else(|| TranslateError::UnknownTerm { term: head.clone() })?;
                if args.is_empty() {
                    return Ok(Term::var(rendered_head));
                }
                let args = args
                    .iter()
                    .map(|arg| self.term_from_egg(*arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Term::app(rendered_head, args))
            }
        }
    }

    fn formula_for(&self, label: &Label) -> Result<&Formula, TranslateError> {
        self.formulas
            .get(label)
            .ok_or_else(|| TranslateError::MissingFormula {
                label: label.clone(),
            })
    }

    fn emit_hypothesis(&mut self, hypothesis: HypothesisFiat) -> Result<Label, TranslateError> {
        let key = (
            hypothesis.hyp_index,
            hypothesis.formula.clone(),
            hypothesis.needs_symmetry,
        );
        if let Some(label) = self.label_by_hyp.get(&key) {
            return Ok(label.clone());
        }

        let direct_key = (hypothesis.hyp_index, hypothesis.formula.clone(), false);
        let hyp_label = if let Some(label) = self.label_by_hyp.get(&direct_key) {
            label.clone()
        } else {
            let label = self.fresh_label("hyp");
            self.push_step(
                label.clone(),
                hypothesis.formula.clone(),
                CertStep::Hyp {
                    label: label.clone(),
                    hyp_index: hypothesis.hyp_index,
                    formula: hypothesis.formula.clone(),
                },
            );
            self.label_by_hyp.insert(direct_key, label.clone());
            label
        };

        if hypothesis.needs_symmetry {
            let Formula::Rel { rel, lhs, rhs } = hypothesis.formula else {
                return Err(TranslateError::MissingFormula { label: hyp_label });
            };
            let sym_label = self.fresh_label("eq_sym");
            self.push_step(
                sym_label.clone(),
                Formula::rel(rel.clone(), rhs, lhs),
                CertStep::EqSym {
                    label: sym_label.clone(),
                    relation: rel,
                    source: hyp_label,
                },
            );
            self.label_by_hyp.insert(key, sym_label.clone());
            Ok(sym_label)
        } else {
            Ok(hyp_label)
        }
    }

    fn emit_reflexivity(&mut self, relation: String, term: Term) -> Result<Label, TranslateError> {
        let key = (relation.clone(), term.clone());
        if let Some(label) = self.label_by_refl.get(&key) {
            return Ok(label.clone());
        }
        let label = self.fresh_label("eq_refl");
        let formula = Formula::rel(relation.clone(), term.clone(), term.clone());
        self.push_step(
            label.clone(),
            formula,
            CertStep::EqRefl {
                label: label.clone(),
                relation,
                term,
            },
        );
        self.label_by_refl.insert(key, label.clone());
        Ok(label)
    }

    fn push_step(&mut self, label: Label, formula: Formula, step: CertStep) {
        self.formulas.insert(label, formula);
        self.steps.push(step);
    }

    fn fresh_label(&mut self, prefix: &str) -> Label {
        let label = Label::new(format!("{prefix}_{}", self.next_label));
        self.next_label += 1;
        label
    }

    fn term_string(&self, term_id: egglog::TermId) -> String {
        self.input.proof_store.term_dag().to_string(term_id)
    }

    fn proposition_string(&self, proposition: &egglog::proof::Proposition) -> String {
        format!(
            "{} = {}",
            self.term_string(proposition.lhs()),
            self.term_string(proposition.rhs())
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum EggTemplate {
    Atom(String),
    App {
        head: String,
        args: Vec<EggTemplate>,
    },
}

struct EggPatternParser<'a> {
    chars: Vec<char>,
    pos: usize,
    source: &'a str,
}

impl<'a> EggPatternParser<'a> {
    fn new(source: &'a str) -> Self {
        Self {
            chars: source.chars().collect(),
            pos: 0,
            source,
        }
    }

    fn parse(mut self) -> Result<EggTemplate, ()> {
        let term = self.parse_term()?;
        self.skip_ws();
        if self.pos == self.chars.len() {
            Ok(term)
        } else {
            Err(())
        }
    }

    fn parse_term(&mut self) -> Result<EggTemplate, ()> {
        self.skip_ws();
        if self.peek() == Some('(') {
            self.pos += 1;
            self.skip_ws();
            let head = self.parse_atom()?;
            let mut args = Vec::new();
            loop {
                self.skip_ws();
                match self.peek() {
                    Some(')') => {
                        self.pos += 1;
                        break;
                    }
                    Some(_) => args.push(self.parse_term()?),
                    None => return Err(()),
                }
            }
            Ok(EggTemplate::App { head, args })
        } else {
            self.parse_atom().map(EggTemplate::Atom)
        }
    }

    fn parse_atom(&mut self) -> Result<String, ()> {
        self.skip_ws();
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() || ch == '(' || ch == ')' {
                break;
            }
            self.pos += 1;
        }
        if self.pos == start {
            Err(())
        } else {
            Ok(self.source[start..self.pos].to_owned())
        }
    }

    fn skip_ws(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.pos += 1;
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }
}

fn remap_step_refs_only(step: &CertStep, aliases: &BTreeMap<Label, Label>) -> CertStep {
    match step {
        CertStep::Hyp {
            label,
            hyp_index,
            formula,
        } => CertStep::Hyp {
            label: label.clone(),
            hyp_index: *hyp_index,
            formula: formula.clone(),
        },
        CertStep::RuleApply {
            label,
            formula,
            mm0_rule,
            bindings,
            refs,
        } => CertStep::RuleApply {
            label: label.clone(),
            formula: formula.clone(),
            mm0_rule: mm0_rule.clone(),
            bindings: bindings.clone(),
            refs: refs
                .iter()
                .map(|proof_ref| remap_ref_alias(proof_ref, aliases))
                .collect(),
        },
        CertStep::EqRefl {
            label,
            relation,
            term,
        } => CertStep::EqRefl {
            label: label.clone(),
            relation: relation.clone(),
            term: term.clone(),
        },
        CertStep::EqSym {
            label,
            relation,
            source,
        } => CertStep::EqSym {
            label: label.clone(),
            relation: relation.clone(),
            source: aliases
                .get(source)
                .cloned()
                .unwrap_or_else(|| source.clone()),
        },
        CertStep::EqTrans {
            label,
            relation,
            left,
            right,
        } => CertStep::EqTrans {
            label: label.clone(),
            relation: relation.clone(),
            left: aliases.get(left).cloned().unwrap_or_else(|| left.clone()),
            right: aliases.get(right).cloned().unwrap_or_else(|| right.clone()),
        },
        CertStep::EqCongr {
            label,
            relation,
            head,
            child_index,
            base,
            child_eq,
            mm0_congr_rule,
        } => CertStep::EqCongr {
            label: label.clone(),
            relation: relation.clone(),
            head: head.clone(),
            child_index: *child_index,
            base: aliases.get(base).cloned().unwrap_or_else(|| base.clone()),
            child_eq: aliases
                .get(child_eq)
                .cloned()
                .unwrap_or_else(|| child_eq.clone()),
            mm0_congr_rule: mm0_congr_rule.clone(),
        },
        CertStep::Transport {
            label,
            relation,
            equivalence,
            proof,
            mm0_transport_rule,
        } => CertStep::Transport {
            label: label.clone(),
            relation: relation.clone(),
            equivalence: aliases
                .get(equivalence)
                .cloned()
                .unwrap_or_else(|| equivalence.clone()),
            proof: aliases.get(proof).cloned().unwrap_or_else(|| proof.clone()),
            mm0_transport_rule: mm0_transport_rule.clone(),
        },
    }
}

fn remap_ref_alias(proof_ref: &Ref, aliases: &BTreeMap<Label, Label>) -> Ref {
    match proof_ref {
        Ref::Label { label } => {
            Ref::label(aliases.get(label).cloned().unwrap_or_else(|| label.clone()))
        }
        Ref::Hyp { hyp_index } => Ref::hyp(*hyp_index),
    }
}

fn remap_step(
    step: &CertStep,
    labels: &BTreeMap<Label, Label>,
) -> Result<CertStep, TranslateError> {
    match step {
        CertStep::Hyp {
            label,
            hyp_index,
            formula,
        } => Ok(CertStep::Hyp {
            label: remap_label(label, labels)?,
            hyp_index: *hyp_index,
            formula: formula.clone(),
        }),
        CertStep::RuleApply {
            label,
            formula,
            mm0_rule,
            bindings,
            refs,
        } => Ok(CertStep::RuleApply {
            label: remap_label(label, labels)?,
            formula: formula.clone(),
            mm0_rule: mm0_rule.clone(),
            bindings: bindings.clone(),
            refs: refs
                .iter()
                .map(|proof_ref| remap_ref(proof_ref, labels))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        CertStep::EqRefl {
            label,
            relation,
            term,
        } => Ok(CertStep::EqRefl {
            label: remap_label(label, labels)?,
            relation: relation.clone(),
            term: term.clone(),
        }),
        CertStep::EqSym {
            label,
            relation,
            source,
        } => Ok(CertStep::EqSym {
            label: remap_label(label, labels)?,
            relation: relation.clone(),
            source: remap_label(source, labels)?,
        }),
        CertStep::EqTrans {
            label,
            relation,
            left,
            right,
        } => Ok(CertStep::EqTrans {
            label: remap_label(label, labels)?,
            relation: relation.clone(),
            left: remap_label(left, labels)?,
            right: remap_label(right, labels)?,
        }),
        CertStep::EqCongr {
            label,
            relation,
            head,
            child_index,
            base,
            child_eq,
            mm0_congr_rule,
        } => Ok(CertStep::EqCongr {
            label: remap_label(label, labels)?,
            relation: relation.clone(),
            head: head.clone(),
            child_index: *child_index,
            base: remap_label(base, labels)?,
            child_eq: remap_label(child_eq, labels)?,
            mm0_congr_rule: mm0_congr_rule.clone(),
        }),
        CertStep::Transport {
            label,
            relation,
            equivalence,
            proof,
            mm0_transport_rule,
        } => Ok(CertStep::Transport {
            label: remap_label(label, labels)?,
            relation: relation.clone(),
            equivalence: remap_label(equivalence, labels)?,
            proof: remap_label(proof, labels)?,
            mm0_transport_rule: mm0_transport_rule.clone(),
        }),
    }
}

fn remap_ref(proof_ref: &Ref, labels: &BTreeMap<Label, Label>) -> Result<Ref, TranslateError> {
    match proof_ref {
        Ref::Label { label } => Ok(Ref::label(remap_label(label, labels)?)),
        Ref::Hyp { hyp_index } => Ok(Ref::hyp(*hyp_index)),
    }
}

fn remap_label(label: &Label, labels: &BTreeMap<Label, Label>) -> Result<Label, TranslateError> {
    labels
        .get(label)
        .cloned()
        .ok_or_else(|| TranslateError::MissingFormula {
            label: label.clone(),
        })
}

fn term_debug(term: &Term) -> String {
    match term {
        Term::Var { name } => name.clone(),
        Term::App { head, args } => {
            let args = args.iter().map(term_debug).collect::<Vec<_>>();
            format!("{}({})", head, args.join(", "))
        }
        Term::Lit { literal } => format!("{literal:?}"),
    }
}

fn render_call(head: &str, args: &[String]) -> String {
    if args.is_empty() {
        format!("({head})")
    } else {
        format!("({head} {})", args.join(" "))
    }
}

#[derive(Clone, Debug)]
struct TranslateIndexes {
    heads: HashMap<String, String>,
    source_heads: HashMap<String, String>,
    source_atoms: HashMap<String, String>,
    term_sorts: HashMap<String, String>,
    conversion_rules: HashMap<String, ConversionRule>,
    rule_to_theorem: HashMap<String, String>,
    rule_to_relation: HashMap<String, String>,
    horn_rules: HashMap<String, SaturationHornLaw>,
}

impl TranslateIndexes {
    fn new(export_env: &ExportEnv, local_vars: &[LocalProofVar]) -> Self {
        let mut heads = HashMap::new();
        let mut source_heads = HashMap::new();
        let mut source_atoms = HashMap::new();
        let mut term_sorts = HashMap::new();
        for local in local_vars {
            let atom = render_call(&local.egglog_constructor, &[]);
            heads.insert(local.egglog_constructor.clone(), local.source_name.clone());
            source_atoms.insert(local.source_name.clone(), atom);
            term_sorts.insert(local.source_name.clone(), local.sort.clone());
        }
        for term in &export_env.terms {
            if term.kind != ExportTermKind::RelationSymbol {
                heads.insert(term.egglog_name.clone(), term.source_name.clone());
                source_heads.insert(term.source_name.clone(), term.egglog_name.clone());
                source_atoms.insert(
                    term.source_name.clone(),
                    render_call(&term.egglog_name, &[]),
                );
            }
            term_sorts.insert(term.source_name.clone(), term.result_sort.clone());
        }
        let mut conversion_rules = HashMap::new();
        let mut rule_to_theorem = HashMap::new();
        let mut rule_to_relation = HashMap::new();
        for law in &export_env.saturation_conversions {
            for rule in &law.rules {
                conversion_rules.insert(rule.rule_name.clone(), rule.clone());
                rule_to_theorem.insert(rule.rule_name.clone(), law.theorem.clone());
                rule_to_relation.insert(rule.rule_name.clone(), law.relation.clone());
            }
        }
        let horn_rules = export_env
            .saturation_horn_rules
            .iter()
            .map(|law| (law.rule_name.clone(), law.clone()))
            .collect::<HashMap<_, _>>();

        Self {
            heads,
            source_heads,
            source_atoms,
            term_sorts,
            conversion_rules,
            rule_to_theorem,
            rule_to_relation,
            horn_rules,
        }
    }

    fn head_name(&self, head: &str) -> Option<&str> {
        self.heads.get(head).map(String::as_str)
    }

    fn egglog_head(&self, source: &str) -> Option<&str> {
        self.source_heads.get(source).map(String::as_str)
    }

    fn egglog_atom(&self, source: &str) -> Option<&str> {
        self.source_atoms.get(source).map(String::as_str)
    }

    fn term_sort(&self, term: &Term) -> Option<&str> {
        match term {
            Term::Var { name } => self.term_sorts.get(name).map(String::as_str),
            Term::App { head, .. } => self.term_sorts.get(head).map(String::as_str),
            Term::Lit { .. } => None,
        }
    }
}

fn proof_children(justification: &egglog::proof::Justification) -> Vec<egglog::proof::ProofId> {
    match justification {
        egglog::proof::Justification::Fiat => Vec::new(),
        egglog::proof::Justification::Rule { premise_proofs, .. } => premise_proofs.clone(),
        egglog::proof::Justification::MergeFn {
            old_proof,
            new_proof,
            ..
        } => vec![*old_proof, *new_proof],
        egglog::proof::Justification::Trans(left, right) => vec![*left, *right],
        egglog::proof::Justification::Sym(inner) => vec![*inner],
        egglog::proof::Justification::Congr {
            proof, child_proof, ..
        } => vec![*proof, *child_proof],
    }
}

#[cfg(test)]
mod tests {
    use super::{
        CertStep, Certificate, ExtraEqualityCertificate, FactTranslateCtx, FactTranslationInput,
        Formula, Label, LocalProofVar, Ref, Term, TranslateIndexes, validate_certificate,
        validate_certificate_for_theorem,
    };
    use crate::export::ExportEnv;
    use crate::mm0::parse_env;

    const INPUT: &str = r#"
sort s;
provable sort wff;
term z: s;
term f (x: s): s;
term eq (x y: s): wff;
term bi (x y: wff): wff;
term p (x: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @relation wff bi bi_refl bi_trans bi_sym bi_mp
axiom bi_refl (x: wff): $ bi x x $;
axiom bi_trans (x y z: wff): $ bi x y $ > $ bi y z $ > $ bi x z $;
axiom bi_sym (x y: wff): $ bi x y $ > $ bi y x $;
axiom bi_mp (x y: wff): $ bi x y $ > $ x $ > $ y $;
--| @congr
axiom f_congr (x y: s): $ eq x y $ > $ eq (f x) (f y) $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
theorem target (x y z: s):
  $ eq x y $ > $ eq y z $ > $ eq x z $;
"#;

    fn export() -> (crate::mm0::Mm0Env, ExportEnv) {
        let env = parse_env(INPUT).unwrap();
        let export = ExportEnv::from_mm0(&env).unwrap();
        (env, export)
    }

    #[test]
    fn validates_transitivity_chain() {
        let (env, export) = export();
        let cert = Certificate::new(vec![
            CertStep::Hyp {
                label: Label::from("h1"),
                hyp_index: 1,
                formula: Formula::rel("eq", Term::var("x"), Term::var("y")),
            },
            CertStep::Hyp {
                label: Label::from("h2"),
                hyp_index: 2,
                formula: Formula::rel("eq", Term::var("y"), Term::var("z")),
            },
            CertStep::EqTrans {
                label: Label::from("goal"),
                relation: "eq".to_owned(),
                left: Label::from("h1"),
                right: Label::from("h2"),
            },
        ]);

        validate_certificate_for_theorem(&cert, &env, &export, "target").unwrap();
    }

    #[test]
    fn rejects_bad_transitivity_middle_term() {
        let (_, export) = export();
        let target = Formula::rel("eq", Term::var("x"), Term::var("z"));
        let cert = Certificate::new(vec![
            CertStep::Hyp {
                label: Label::from("h1"),
                hyp_index: 1,
                formula: Formula::rel("eq", Term::var("x"), Term::var("y")),
            },
            CertStep::Hyp {
                label: Label::from("h2"),
                hyp_index: 2,
                formula: Formula::rel("eq", Term::var("w"), Term::var("z")),
            },
            CertStep::EqTrans {
                label: Label::from("goal"),
                relation: "eq".to_owned(),
                left: Label::from("h1"),
                right: Label::from("h2"),
            },
        ]);

        let err = validate_certificate(&cert, &export, &target).unwrap_err();
        assert!(err.to_string().contains("matching middle terms"));
    }

    #[test]
    fn validates_congruence_child_replacement() {
        let (_, export) = export();
        let target = Formula::rel(
            "eq",
            Term::app("f", vec![Term::var("x")]),
            Term::app("f", vec![Term::var("y")]),
        );
        let cert = Certificate::new(vec![
            CertStep::EqRefl {
                label: Label::from("base"),
                relation: "eq".to_owned(),
                term: Term::app("f", vec![Term::var("x")]),
            },
            CertStep::Hyp {
                label: Label::from("h"),
                hyp_index: 1,
                formula: Formula::rel("eq", Term::var("x"), Term::var("y")),
            },
            CertStep::EqCongr {
                label: Label::from("goal"),
                relation: "eq".to_owned(),
                head: "f".to_owned(),
                child_index: 0,
                base: Label::from("base"),
                child_eq: Label::from("h"),
                mm0_congr_rule: "f_congr".to_owned(),
            },
        ]);

        validate_certificate(&cert, &export, &target).unwrap();
    }

    #[test]
    fn rejects_congruence_child_index_out_of_range() {
        let (_, export) = export();
        let target = Formula::rel(
            "eq",
            Term::app("f", vec![Term::var("x")]),
            Term::app("f", vec![Term::var("y")]),
        );
        let cert = Certificate::new(vec![
            CertStep::EqRefl {
                label: Label::from("base"),
                relation: "eq".to_owned(),
                term: Term::app("f", vec![Term::var("x")]),
            },
            CertStep::Hyp {
                label: Label::from("h"),
                hyp_index: 1,
                formula: Formula::rel("eq", Term::var("x"), Term::var("y")),
            },
            CertStep::EqCongr {
                label: Label::from("goal"),
                relation: "eq".to_owned(),
                head: "f".to_owned(),
                child_index: 1,
                base: Label::from("base"),
                child_eq: Label::from("h"),
                mm0_congr_rule: "f_congr".to_owned(),
            },
        ]);

        let err = validate_certificate(&cert, &export, &target).unwrap_err();
        assert!(err.to_string().contains("out of range"));
    }

    #[test]
    fn validates_wff_transport() {
        let (_, export) = export();
        let p_x = Formula::atom("p", vec![Term::var("x")]);
        let p_y = Formula::atom("p", vec![Term::var("y")]);
        let equiv = Formula::rel(
            "bi",
            Term::app("p", vec![Term::var("x")]),
            Term::app("p", vec![Term::var("y")]),
        );
        let cert = Certificate::new(vec![
            CertStep::RuleApply {
                label: Label::from("equiv"),
                formula: equiv,
                mm0_rule: "bi_refl".to_owned(),
                bindings: Vec::new(),
                refs: Vec::new(),
            },
            CertStep::Hyp {
                label: Label::from("proof"),
                hyp_index: 1,
                formula: p_x,
            },
            CertStep::Transport {
                label: Label::from("goal"),
                relation: "bi".to_owned(),
                equivalence: Label::from("equiv"),
                proof: Label::from("proof"),
                mm0_transport_rule: "bi_mp".to_owned(),
            },
        ]);

        validate_certificate(&cert, &export, &p_y).unwrap();
    }

    #[test]
    fn rejects_missing_transport_theorem() {
        let (_, export) = export();
        let p_x = Formula::atom("p", vec![Term::var("x")]);
        let p_y = Formula::atom("p", vec![Term::var("y")]);
        let cert = Certificate::new(vec![
            CertStep::RuleApply {
                label: Label::from("equiv"),
                formula: Formula::rel(
                    "bi",
                    Term::app("p", vec![Term::var("x")]),
                    Term::app("p", vec![Term::var("y")]),
                ),
                mm0_rule: "bi_refl".to_owned(),
                bindings: Vec::new(),
                refs: Vec::new(),
            },
            CertStep::Hyp {
                label: Label::from("proof"),
                hyp_index: 1,
                formula: p_x,
            },
            CertStep::Transport {
                label: Label::from("goal"),
                relation: "bi".to_owned(),
                equivalence: Label::from("equiv"),
                proof: Label::from("proof"),
                mm0_transport_rule: "wrong".to_owned(),
            },
        ]);

        let err = validate_certificate(&cert, &export, &p_y).unwrap_err();
        assert!(err.to_string().contains("not in relation bundle"));
    }

    #[test]
    fn rejects_final_goal_mismatch() {
        let (_, export) = export();
        let cert = Certificate::new(vec![CertStep::EqRefl {
            label: Label::from("r"),
            relation: "eq".to_owned(),
            term: Term::var("x"),
        }]);

        let target = Formula::rel("eq", Term::var("x"), Term::var("y"));
        let err = validate_certificate(&cert, &export, &target).unwrap_err();
        assert!(err.to_string().contains("target theorem"));
    }

    #[test]
    fn rule_apply_refs_must_point_backward() {
        let (_, export) = export();
        let target = Formula::rel("eq", Term::var("x"), Term::var("x"));
        let cert = Certificate::new(vec![CertStep::RuleApply {
            label: Label::from("goal"),
            formula: target.clone(),
            mm0_rule: "f_id".to_owned(),
            bindings: Vec::new(),
            refs: vec![Ref::label("later")],
        }]);

        let err = validate_certificate(&cert, &export, &target).unwrap_err();
        assert!(err.to_string().contains("unknown or future label"));
    }

    #[test]
    fn fact_alignment_can_import_extra_equality_certificate() {
        let env = parse_env(
            r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
term bi (x y: wff): wff;
term p (x: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @relation wff bi bi_refl bi_trans bi_sym bi_mp
axiom bi_refl (x: wff): $ bi x x $;
axiom bi_trans (x y z: wff): $ bi x y $ > $ bi y z $ > $ bi x z $;
axiom bi_sym (x y: wff): $ bi x y $ > $ bi y x $;
axiom bi_mp (x y: wff): $ bi x y $ > $ x $ > $ y $;
--| @congr
axiom p_congr (x y: s): $ eq x y $ > $ bi (p x) (p y) $;
"#,
        )
        .unwrap();
        let export = ExportEnv::from_mm0(&env).unwrap();
        let mut egraph = egglog::EGraph::new_with_proofs();
        let outputs = egraph
            .parse_and_run_program(
                None,
                concat!(
                    "(sort S)\n",
                    "(constructor A () S)\n",
                    "(constructor B () S)\n",
                    "(ruleset demo)\n",
                    "(A)\n",
                    "(rule ((= x (A))) ((union x (B))) :ruleset demo)\n",
                    "(run-schedule (saturate (run demo)))\n",
                    "(prove-exists B)\n",
                ),
            )
            .unwrap();
        let (proof_store, root) = outputs
            .iter()
            .find_map(|output| match output {
                egglog::CommandOutput::ProveExists {
                    proof_store,
                    proof_id,
                } => Some((proof_store, *proof_id)),
                _ => None,
            })
            .unwrap();
        let local_vars = vec![
            LocalProofVar {
                egglog_constructor: "EggbauVarTargetX".to_owned(),
                source_name: "x".to_owned(),
                sort: "s".to_owned(),
            },
            LocalProofVar {
                egglog_constructor: "EggbauVarTargetY".to_owned(),
                source_name: "y".to_owned(),
                sort: "s".to_owned(),
            },
        ];
        let extra = ExtraEqualityCertificate {
            sort: "s".to_owned(),
            relation: "eq".to_owned(),
            lhs_egglog: "(EggbauVarTargetX)".to_owned(),
            rhs_egglog: "(EggbauVarTargetY)".to_owned(),
            certificate: Certificate::new(vec![CertStep::Hyp {
                label: Label::from("eq_xy"),
                hyp_index: 1,
                formula: Formula::rel("eq", Term::var("x"), Term::var("y")),
            }]),
        };
        let indexes = TranslateIndexes::new(&export, &local_vars);
        let mut ctx = FactTranslateCtx {
            input: FactTranslationInput {
                proof_store,
                root,
                export_env: &export,
                target_pred: "p",
                target_args_egglog: vec!["(EggbauVarTargetY)".to_owned()],
                local_vars,
                hypothesis_fiats: Vec::new(),
                extra_equalities: vec![extra],
            },
            indexes,
            labels: std::collections::HashMap::new(),
            formulas: std::collections::BTreeMap::new(),
            label_by_refl: std::collections::BTreeMap::new(),
            label_by_hyp: std::collections::BTreeMap::new(),
            label_by_transport: std::collections::BTreeMap::new(),
            steps: Vec::new(),
            next_label: 1,
        };
        let base = Label::from("base");
        let p_x = Formula::atom("p", vec![Term::var("x")]);
        ctx.push_step(
            base.clone(),
            p_x.clone(),
            CertStep::Hyp {
                label: base.clone(),
                hyp_index: 2,
                formula: p_x,
            },
        );

        let target = Formula::atom("p", vec![Term::var("y")]);
        let label = ctx.align_formula(base, &target).unwrap();

        assert_eq!(ctx.formula_for(&label).unwrap(), &target);
        let cert = Certificate::new(ctx.steps);
        validate_certificate(&cert, &export, &target).unwrap();
    }
}
