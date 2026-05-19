use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::export::{ConversionRule, ExportEnv, ExportTermKind, ExportUse};
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

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Literal {
    String { value: String },
    Integer { value: String },
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
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

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
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

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TermOrFormula {
    Term { term: Term },
    Formula { formula: Formula },
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
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

    if last_formula.as_ref() == Some(options.target) {
        Ok(())
    } else {
        Err(CertValidationError::FinalGoalMismatch)
    }
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
    let (child_lhs, child_rhs) = expect_relation_formula(child_eq, input.relation, step_no)?;

    let Term::App {
        head: left_head,
        args: left_args,
    } = base_lhs
    else {
        return Err(CertValidationError::CongruenceHeadMismatch {
            expected: input.head.to_owned(),
            found: base_lhs.head().unwrap_or("<literal>").to_owned(),
            step: step_no,
        });
    };
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
    if left_head != input.head || right_head != input.head {
        let found = if left_head != input.head {
            left_head
        } else {
            right_head
        };
        return Err(CertValidationError::CongruenceHeadMismatch {
            expected: input.head.to_owned(),
            found: found.clone(),
            step: step_no,
        });
    }
    if input.child_index >= right_args.len() || input.child_index >= left_args.len() {
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
        lhs: Term::App {
            head: left_head.clone(),
            args: left_args.clone(),
        },
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

#[derive(Debug, Error, Eq, PartialEq)]
pub enum TranslateError {
    #[error("egglog proof does not contain equality target {lhs} = {rhs}")]
    TargetEqualityNotFound { lhs: String, rhs: String },

    #[error("unsupported egglog proof justification MergeFn for function {function}")]
    UnsupportedMergeFn { function: String },

    #[error("egglog proof used unapproved Fiat proposition: {proposition}")]
    UnapprovedFiat { proposition: String },

    #[error("cannot reconstruct proof-goal bridge rule `{rule}` without a premise")]
    EmptyGoalBridge { rule: String },

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
}

pub fn translate_equality_proof(
    input: EqualityTranslationInput<'_>,
) -> Result<Certificate, TranslateError> {
    let indexes = TranslateIndexes::new(input.export_env, &input.local_vars);
    let mut ctx = TranslateCtx {
        input,
        indexes,
        labels: HashMap::new(),
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
                let left = self.translate_proof(*left)?;
                let right = self.translate_proof(*right)?;
                let label = self.fresh_label("eq_trans");
                self.steps.push(CertStep::EqTrans {
                    label: label.clone(),
                    relation: self.input.relation.to_owned(),
                    left,
                    right,
                });
                label
            }
            egglog::proof::Justification::Sym(inner) => {
                let source = self.translate_proof(*inner)?;
                let label = self.fresh_label("eq_sym");
                self.steps.push(CertStep::EqSym {
                    label: label.clone(),
                    relation: self.input.relation.to_owned(),
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
            let hyp_label = self.fresh_label("hyp");
            self.steps.push(CertStep::Hyp {
                label: hyp_label.clone(),
                hyp_index: hypothesis.hyp_index,
                formula: hypothesis.formula,
            });
            if hypothesis.needs_symmetry {
                let sym_label = self.fresh_label("eq_sym");
                self.steps.push(CertStep::EqSym {
                    label: sym_label.clone(),
                    relation: self.input.relation.to_owned(),
                    source: hyp_label,
                });
                return Ok(sym_label);
            }
            return Ok(hyp_label);
        }

        let lhs = proof.proposition().lhs();
        let rhs = proof.proposition().rhs();
        if self.term_string(lhs) != self.term_string(rhs) {
            return Err(TranslateError::UnapprovedFiat { proposition });
        }
        let term = self.term_from_egg(lhs)?;
        let label = self.fresh_label("eq_refl");
        self.steps.push(CertStep::EqRefl {
            label: label.clone(),
            relation: self.input.relation.to_owned(),
            term,
        });
        Ok(label)
    }

    fn translate_rule(
        &mut self,
        proof_id: egglog::proof::ProofId,
        name: &str,
        premise_proofs: &[egglog::proof::ProofId],
        substitution: &[(String, egglog::TermId)],
    ) -> Result<Label, TranslateError> {
        if self.indexes.goal_bridge_rules.contains(name) {
            let Some(first) = premise_proofs.first() else {
                return Err(TranslateError::EmptyGoalBridge {
                    rule: name.to_owned(),
                });
            };
            return self.translate_proof(*first);
        }

        let Some(rule) = self.indexes.conversion_rules.get(name).cloned() else {
            return Err(TranslateError::UnknownRule {
                rule: name.to_owned(),
            });
        };
        let source = self.instantiate_pattern(&rule.source_egglog, substitution)?;
        let target = self.instantiate_pattern(&rule.target_egglog, substitution)?;
        let mut rule_label = self.emit_rule_source_to_target(name, &rule, &source, &target);

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
                    relation: self.input.relation.to_owned(),
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
                    relation: self.input.relation.to_owned(),
                    source: premise_label,
                });
                let trans_label = self.fresh_label("eq_trans");
                self.steps.push(CertStep::EqTrans {
                    label: trans_label.clone(),
                    relation: self.input.relation.to_owned(),
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
                relation: self.input.relation.to_owned(),
                source: rule_label,
            });
            Ok(sym_label)
        } else {
            Err(TranslateError::RuleReconstructionMismatch {
                rule: name.to_owned(),
            })
        }
    }

    fn emit_rule_source_to_target(
        &mut self,
        name: &str,
        rule: &ConversionRule,
        source: &Term,
        target: &Term,
    ) -> Label {
        let label = self.fresh_label("rule");
        if rule.needs_symmetry_for_mm0 {
            self.steps.push(CertStep::RuleApply {
                label: label.clone(),
                formula: Formula::rel(self.input.relation, target.clone(), source.clone()),
                mm0_rule: self.indexes.rule_to_theorem[name].clone(),
                bindings: Vec::new(),
                refs: Vec::new(),
            });
            let sym_label = self.fresh_label("eq_sym");
            self.steps.push(CertStep::EqSym {
                label: sym_label.clone(),
                relation: self.input.relation.to_owned(),
                source: label,
            });
            sym_label
        } else {
            self.steps.push(CertStep::RuleApply {
                label: label.clone(),
                formula: Formula::rel(self.input.relation, source.clone(), target.clone()),
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
            relation: self.input.relation.to_owned(),
            head,
            child_index,
            base: base_label,
            child_eq: child_label,
            mm0_congr_rule: congruence.theorem.clone(),
        });
        Ok(label)
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

#[derive(Clone, Debug)]
struct TranslateIndexes {
    heads: HashMap<String, String>,
    conversion_rules: HashMap<String, ConversionRule>,
    rule_to_theorem: HashMap<String, String>,
    goal_bridge_rules: HashSet<String>,
}

impl TranslateIndexes {
    fn new(export_env: &ExportEnv, local_vars: &[LocalProofVar]) -> Self {
        let mut heads = HashMap::new();
        for local in local_vars {
            heads.insert(local.egglog_constructor.clone(), local.source_name.clone());
        }
        for term in &export_env.terms {
            if term.kind != ExportTermKind::RelationSymbol {
                heads.insert(term.egglog_name.clone(), term.source_name.clone());
            }
        }

        let mut conversion_rules = HashMap::new();
        let mut rule_to_theorem = HashMap::new();
        for law in &export_env.saturation_conversions {
            for rule in &law.rules {
                conversion_rules.insert(rule.rule_name.clone(), rule.clone());
                rule_to_theorem.insert(rule.rule_name.clone(), law.theorem.clone());
            }
        }

        let goal_bridge_rules = export_env
            .proof_goals
            .equality
            .keys()
            .map(|sort| format!("prove_eq_{}", snake_ident(sort)))
            .collect::<HashSet<_>>();

        Self {
            heads,
            conversion_rules,
            rule_to_theorem,
            goal_bridge_rules,
        }
    }

    fn head_name(&self, head: &str) -> Option<&str> {
        self.heads.get(head).map(String::as_str)
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

fn snake_ident(name: &str) -> String {
    let mut out = String::new();
    for (idx, ch) in name.chars().enumerate() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            if idx == 0 && ch.is_ascii_digit() {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
    if out.is_empty() { "_".to_owned() } else { out }
}

#[cfg(test)]
mod tests {
    use super::{
        CertStep, Certificate, Formula, Label, Ref, Term, validate_certificate,
        validate_certificate_for_theorem,
    };
    use crate::export::ExportEnv;
    use crate::mm0::parse_env;

    const INPUT: &str = r#"
sort s;
sort wff;
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
}
