use std::collections::HashSet;
use std::fmt::Write as _;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::mm0::{Formula, MathExpr, Mm0Env, SaturationMode, TheoremDecl};
use crate::{EggbauError, mm0};

/// Stage-0 discovery deliberately authorizes nothing.
///
/// Later stages will parse MM0 and suggest `@saturation` annotations.  For now
/// this deterministic output gives the snapshot harness something meaningful to
/// compare without implying any theorem has been exported to egglog.
pub fn render_empty_discovery(path: &Path, _mm0: &str) -> String {
    format!(
        "discovery report\ninput: {}\n\npossible saturation conversions:\n\
         possible saturation horn rules:\npossible congruences:\n",
        path.display()
    )
}

/// Parse MM0 text, run syntactic discovery, and render a stable report.
pub fn render_discovery(
    path: &Path,
    mm0_text: &str,
    suggest_annotations: bool,
) -> Result<String, EggbauError> {
    let env = mm0::parse_env(mm0_text)?;
    let report = DiscoveryReport::from_env(&env);
    Ok(report.render(path, suggest_annotations))
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct DiscoveryReport {
    pub possible_conversions: Vec<ConversionCandidate>,
    pub possible_horn_rules: Vec<HornCandidate>,
    pub possible_congruences: Vec<CongruenceCandidate>,
    pub metadata_errors: Vec<MetadataValidationError>,
}

impl DiscoveryReport {
    pub fn from_env(env: &Mm0Env) -> Self {
        Self {
            possible_conversions: discover_conversions(env),
            possible_horn_rules: discover_horn_rules(env),
            possible_congruences: discover_congruences(env),
            metadata_errors: validate_metadata(env),
        }
    }

    pub fn render(&self, path: &Path, suggest_annotations: bool) -> String {
        let mut out = String::new();
        writeln!(out, "discovery report").expect("write to string");
        writeln!(out, "input: {}", path.display()).expect("write to string");
        writeln!(out).expect("write to string");

        render_conversion_candidates(&mut out, &self.possible_conversions);
        writeln!(out).expect("write to string");
        render_horn_candidates(&mut out, &self.possible_horn_rules);
        writeln!(out).expect("write to string");
        render_congruence_candidates(&mut out, &self.possible_congruences);

        if !self.metadata_errors.is_empty() {
            writeln!(out).expect("write to string");
            writeln!(out, "metadata validation errors:").expect("write to string");
            for error in &self.metadata_errors {
                writeln!(
                    out,
                    "  {} ({}): {}",
                    error.theorem, error.metadata_kind, error.message
                )
                .expect("write to string");
            }
        }

        if suggest_annotations {
            writeln!(out).expect("write to string");
            render_annotation_suggestions(&mut out, self);
        }

        out
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ConversionCandidate {
    pub theorem: String,
    pub formula: String,
    pub suggested_mode: SaturationMode,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct HornCandidate {
    pub theorem: String,
    pub rule: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CongruenceCandidate {
    pub theorem: String,
    pub rule: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct MetadataValidationError {
    pub theorem: String,
    pub metadata_kind: MetadataKind,
    pub message: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MetadataKind {
    Relation,
    Congruence,
    Saturation,
}

impl std::fmt::Display for MetadataKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Relation => f.write_str("@relation"),
            Self::Congruence => f.write_str("@congr"),
            Self::Saturation => f.write_str("@saturation"),
        }
    }
}

pub fn validate_metadata(env: &Mm0Env) -> Vec<MetadataValidationError> {
    let mut errors = Vec::new();
    let declared_sorts = env
        .sorts
        .iter()
        .map(|sort| sort.name.as_str())
        .collect::<HashSet<_>>();
    let declared_terms = env
        .terms
        .iter()
        .map(|term| term.name.as_str())
        .collect::<HashSet<_>>();

    for relation in &env.metadata.relations {
        if !declared_sorts.contains(relation.sort.as_str()) {
            errors.push(MetadataValidationError {
                theorem: relation.relation.clone(),
                metadata_kind: MetadataKind::Relation,
                message: format!("relation sort is not declared: {}", relation.sort),
            });
        }
        if !declared_terms.contains(relation.relation.as_str()) {
            errors.push(MetadataValidationError {
                theorem: relation.relation.clone(),
                metadata_kind: MetadataKind::Relation,
                message: "relation term is not declared".to_owned(),
            });
        }
        validate_relation_theorem(
            env,
            &relation.reflexivity,
            MetadataKind::Relation,
            |theorem| validate_reflexivity_shape(theorem, &relation.relation),
            &mut errors,
        );
        validate_relation_theorem(
            env,
            &relation.transitivity,
            MetadataKind::Relation,
            |theorem| validate_transitivity_shape(theorem, &relation.relation),
            &mut errors,
        );
        validate_relation_theorem(
            env,
            &relation.symmetry,
            MetadataKind::Relation,
            |theorem| validate_symmetry_shape(theorem, &relation.relation),
            &mut errors,
        );
        if let Some(transport) = &relation.transport {
            validate_relation_theorem(
                env,
                transport,
                MetadataKind::Relation,
                |theorem| validate_transport_shape(theorem, &relation.relation),
                &mut errors,
            );
        }
    }

    for congruence in &env.metadata.congruences {
        match env.theorem(&congruence.theorem) {
            Some(theorem) => push_shape_error(
                &mut errors,
                MetadataKind::Congruence,
                &theorem.name,
                validate_supported_theorem(theorem)
                    .and_then(|_| validate_congruence_shape(env, theorem)),
            ),
            None => errors.push(MetadataValidationError {
                theorem: congruence.theorem.clone(),
                metadata_kind: MetadataKind::Congruence,
                message: "referenced theorem was not declared".to_owned(),
            }),
        }
    }

    for saturation in &env.metadata.saturations {
        match env.theorem(&saturation.theorem) {
            Some(theorem) => push_shape_error(
                &mut errors,
                MetadataKind::Saturation,
                &theorem.name,
                validate_supported_theorem(theorem)
                    .and_then(|_| validate_saturation_shape(env, theorem, saturation.mode)),
            ),
            None => errors.push(MetadataValidationError {
                theorem: saturation.theorem.clone(),
                metadata_kind: MetadataKind::Saturation,
                message: "referenced theorem was not declared".to_owned(),
            }),
        }
    }

    errors
}

fn render_conversion_candidates(out: &mut String, candidates: &[ConversionCandidate]) {
    writeln!(out, "possible saturation conversions:").expect("write to string");
    if candidates.is_empty() {
        writeln!(out, "  (none)").expect("write to string");
        return;
    }
    for candidate in candidates {
        writeln!(out, "  {}: {}", candidate.theorem, candidate.formula).expect("write to string");
        writeln!(
            out,
            "    suggested annotation: --| @saturation {}",
            candidate.suggested_mode
        )
        .expect("write to string");
    }
}

fn render_horn_candidates(out: &mut String, candidates: &[HornCandidate]) {
    writeln!(out, "possible saturation horn rules:").expect("write to string");
    if candidates.is_empty() {
        writeln!(out, "  (none)").expect("write to string");
        return;
    }
    for candidate in candidates {
        writeln!(out, "  {}: {}", candidate.theorem, candidate.rule).expect("write to string");
        writeln!(out, "    suggested annotation: --| @saturation horn").expect("write to string");
    }
}

fn render_congruence_candidates(out: &mut String, candidates: &[CongruenceCandidate]) {
    writeln!(out, "possible congruences:").expect("write to string");
    if candidates.is_empty() {
        writeln!(out, "  (none)").expect("write to string");
        return;
    }
    for candidate in candidates {
        writeln!(out, "  {}: {}", candidate.theorem, candidate.rule).expect("write to string");
        writeln!(out, "    existing annotation needed: --| @congr").expect("write to string");
    }
}

fn render_annotation_suggestions(out: &mut String, report: &DiscoveryReport) {
    writeln!(out, "suggested annotation patch:").expect("write to string");
    let mut wrote = false;
    for candidate in &report.possible_conversions {
        wrote = true;
        writeln!(out, "  before theorem {}:", candidate.theorem).expect("write");
        writeln!(out, "    + --| @saturation {}", candidate.suggested_mode)
            .expect("write to string");
    }
    for candidate in &report.possible_horn_rules {
        wrote = true;
        writeln!(out, "  before theorem {}:", candidate.theorem).expect("write");
        writeln!(out, "    + --| @saturation horn").expect("write to string");
    }
    if !wrote {
        writeln!(out, "  (none)").expect("write to string");
    }
}

fn discover_conversions(env: &Mm0Env) -> Vec<ConversionCandidate> {
    env.theorems
        .iter()
        .filter(|theorem| !is_already_saturation(env, &theorem.name))
        .filter(|theorem| !is_relation_helper(env, &theorem.name))
        .filter(|theorem| theorem.unsupported_reason.is_none())
        .filter(|theorem| theorem.hypotheses.is_empty())
        .filter_map(|theorem| {
            let relation = relation_formula(env, &theorem.conclusion)?;
            if relation.lhs == relation.rhs {
                return None;
            }
            Some(ConversionCandidate {
                theorem: theorem.name.clone(),
                formula: theorem.conclusion.source.clone(),
                suggested_mode: SaturationMode::Ltr,
            })
        })
        .collect()
}

fn discover_horn_rules(env: &Mm0Env) -> Vec<HornCandidate> {
    env.theorems
        .iter()
        .filter(|theorem| !is_already_saturation(env, &theorem.name))
        .filter(|theorem| theorem.unsupported_reason.is_none())
        .filter(|theorem| !theorem.hypotheses.is_empty())
        .filter(|theorem| is_atomic_fact(env, &theorem.conclusion))
        .filter(|theorem| theorem.hypotheses.iter().all(is_atomic))
        .map(|theorem| HornCandidate {
            theorem: theorem.name.clone(),
            rule: format_rule(theorem),
        })
        .collect()
}

fn discover_congruences(env: &Mm0Env) -> Vec<CongruenceCandidate> {
    env.theorems
        .iter()
        .filter(|theorem| !is_already_congruence(env, &theorem.name))
        .filter(|theorem| theorem.unsupported_reason.is_none())
        .filter(|theorem| validate_congruence_shape(env, theorem).is_ok())
        .map(|theorem| CongruenceCandidate {
            theorem: theorem.name.clone(),
            rule: format_rule(theorem),
        })
        .collect()
}

fn format_rule(theorem: &TheoremDecl) -> String {
    theorem
        .hypotheses
        .iter()
        .map(|hypothesis| hypothesis.source.clone())
        .chain(std::iter::once(theorem.conclusion.source.clone()))
        .collect::<Vec<_>>()
        .join(" -> ")
}

fn is_already_saturation(env: &Mm0Env, theorem: &str) -> bool {
    env.metadata
        .saturations
        .iter()
        .any(|annotation| annotation.theorem == theorem)
}

fn is_already_congruence(env: &Mm0Env, theorem: &str) -> bool {
    env.metadata
        .congruences
        .iter()
        .any(|annotation| annotation.theorem == theorem)
}

fn is_relation_helper(env: &Mm0Env, theorem: &str) -> bool {
    env.metadata.relations.iter().any(|relation| {
        relation.reflexivity == theorem
            || relation.transitivity == theorem
            || relation.symmetry == theorem
            || relation.transport.as_deref() == Some(theorem)
    })
}

fn validate_relation_theorem(
    env: &Mm0Env,
    theorem_name: &str,
    metadata_kind: MetadataKind,
    validate: impl FnOnce(&TheoremDecl) -> Result<(), String>,
    errors: &mut Vec<MetadataValidationError>,
) {
    match env.theorem(theorem_name) {
        Some(theorem) => push_shape_error(
            errors,
            metadata_kind,
            theorem_name,
            validate_supported_theorem(theorem).and_then(|_| validate(theorem)),
        ),
        None => errors.push(MetadataValidationError {
            theorem: theorem_name.to_owned(),
            metadata_kind,
            message: "referenced theorem was not declared".to_owned(),
        }),
    }
}

fn push_shape_error(
    errors: &mut Vec<MetadataValidationError>,
    metadata_kind: MetadataKind,
    theorem: &str,
    result: Result<(), String>,
) {
    if let Err(message) = result {
        errors.push(MetadataValidationError {
            theorem: theorem.to_owned(),
            metadata_kind,
            message,
        });
    }
}

fn validate_supported_theorem(theorem: &TheoremDecl) -> Result<(), String> {
    if let Some(reason) = &theorem.unsupported_reason {
        return Err(reason.clone());
    }
    for formula in theorem
        .hypotheses
        .iter()
        .chain(std::iter::once(&theorem.conclusion))
    {
        if let Some(reason) = &formula.unsupported_reason {
            return Err(reason.clone());
        }
        if formula.expr.is_none() {
            return Err("formula did not parse to a kernel expression".to_owned());
        }
    }
    Ok(())
}

fn validate_saturation_shape(
    env: &Mm0Env,
    theorem: &TheoremDecl,
    mode: SaturationMode,
) -> Result<(), String> {
    match mode {
        SaturationMode::Ltr | SaturationMode::Rtl | SaturationMode::Both => {
            if !theorem.hypotheses.is_empty() {
                return Err("conversion saturation rules may not have hypotheses yet".to_owned());
            }
            relation_formula(env, &theorem.conclusion)
                .map(|_| ())
                .ok_or_else(|| "conversion conclusion is not a declared relation".to_owned())
        }
        SaturationMode::Horn => {
            if theorem.hypotheses.is_empty() {
                return Err("horn saturation rules require hypotheses".to_owned());
            }
            if !is_atomic_fact(env, &theorem.conclusion) {
                return Err("horn conclusion is not an atomic fact".to_owned());
            }
            if !theorem.hypotheses.iter().all(is_atomic) {
                return Err("horn hypotheses must be atomic formulas".to_owned());
            }
            Ok(())
        }
    }
}

fn validate_congruence_shape(env: &Mm0Env, theorem: &TheoremDecl) -> Result<(), String> {
    if theorem.hypotheses.is_empty() {
        return Err("congruence theorem should have relation hypotheses".to_owned());
    }
    if !theorem
        .hypotheses
        .iter()
        .all(|formula| relation_formula(env, formula).is_some())
    {
        return Err("congruence hypotheses must be declared relations".to_owned());
    }

    let relation = relation_formula(env, &theorem.conclusion)
        .ok_or_else(|| "congruence conclusion is not a declared relation".to_owned())?;
    let lhs_head = application_head(relation.lhs)
        .ok_or_else(|| "congruence left side is not a term application".to_owned())?;
    let rhs_head = application_head(relation.rhs)
        .ok_or_else(|| "congruence right side is not a term application".to_owned())?;
    if lhs_head != rhs_head {
        return Err("congruence conclusion sides have different heads".to_owned());
    }
    Ok(())
}

fn validate_reflexivity_shape(theorem: &TheoremDecl, relation: &str) -> Result<(), String> {
    if !theorem.hypotheses.is_empty() {
        return Err("relation reflexivity theorem must have no hypotheses".to_owned());
    }
    let Some(shape) = relation_formula_by_name(&theorem.conclusion, relation) else {
        return Err("relation reflexivity conclusion uses the wrong relation".to_owned());
    };
    if shape.lhs != shape.rhs {
        return Err("relation reflexivity conclusion is not rel x x".to_owned());
    }
    Ok(())
}

fn validate_transitivity_shape(theorem: &TheoremDecl, relation: &str) -> Result<(), String> {
    if theorem.hypotheses.len() != 2 {
        return Err("relation transitivity theorem must have two hypotheses".to_owned());
    }
    if theorem
        .hypotheses
        .iter()
        .chain(std::iter::once(&theorem.conclusion))
        .all(|formula| relation_formula_by_name(formula, relation).is_some())
    {
        Ok(())
    } else {
        Err("relation transitivity formulas use the wrong relation".to_owned())
    }
}

fn validate_symmetry_shape(theorem: &TheoremDecl, relation: &str) -> Result<(), String> {
    if theorem.hypotheses.len() != 1 {
        return Err("relation symmetry theorem must have one hypothesis".to_owned());
    }
    let Some(hypothesis) = relation_formula_by_name(&theorem.hypotheses[0], relation) else {
        return Err("relation symmetry hypothesis uses the wrong relation".to_owned());
    };
    let Some(conclusion) = relation_formula_by_name(&theorem.conclusion, relation) else {
        return Err("relation symmetry conclusion uses the wrong relation".to_owned());
    };
    if hypothesis.lhs == conclusion.rhs && hypothesis.rhs == conclusion.lhs {
        Ok(())
    } else {
        Err("relation symmetry conclusion does not flip the hypothesis".to_owned())
    }
}

fn validate_transport_shape(theorem: &TheoremDecl, _relation: &str) -> Result<(), String> {
    if theorem.hypotheses.is_empty() {
        Err("relation transport theorem must have hypotheses".to_owned())
    } else {
        Ok(())
    }
}

fn relation_formula<'a>(env: &Mm0Env, formula: &'a Formula) -> Option<RelationShape<'a>> {
    let relation_names = env
        .metadata
        .relations
        .iter()
        .map(|relation| relation.relation.as_str())
        .collect::<HashSet<_>>();
    relation_formula_matching(formula, |head| relation_names.contains(head))
}

fn relation_formula_by_name<'a>(
    formula: &'a Formula,
    relation_name: &str,
) -> Option<RelationShape<'a>> {
    relation_formula_matching(formula, |head| head == relation_name)
}

fn relation_formula_matching<'a>(
    formula: &'a Formula,
    is_relation: impl FnOnce(&str) -> bool,
) -> Option<RelationShape<'a>> {
    match formula.expr.as_ref()? {
        MathExpr::App { head, args } if args.len() == 2 && is_relation(head) => {
            Some(RelationShape {
                lhs: &args[0],
                rhs: &args[1],
            })
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
struct RelationShape<'a> {
    lhs: &'a MathExpr,
    rhs: &'a MathExpr,
}

fn is_atomic_fact(env: &Mm0Env, formula: &Formula) -> bool {
    is_atomic(formula) && relation_formula(env, formula).is_none()
}

fn is_atomic(formula: &Formula) -> bool {
    matches!(
        formula.expr,
        Some(MathExpr::Atom { .. }) | Some(MathExpr::App { .. })
    ) && formula.unsupported_reason.is_none()
}

fn application_head(expr: &MathExpr) -> Option<&str> {
    match expr {
        MathExpr::App { head, .. } => Some(head.as_str()),
        MathExpr::Atom { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{DiscoveryReport, validate_metadata};
    use crate::mm0::parse_env;

    #[test]
    fn ignores_rewrite_metadata_for_discovery_authorization() {
        let input = r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
term z: s;
term f (x: s): s;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @rewrite 100
axiom f_z (x: s): $ eq (f x) z $;
"#;
        let env = parse_env(input).unwrap();
        let report = DiscoveryReport::from_env(&env);

        assert!(env.metadata.saturations.is_empty());
        assert_eq!(report.possible_conversions[0].theorem, "f_z");
    }

    #[test]
    fn validates_saturation_conversion_shape() {
        let input = r#"
sort s;
provable sort wff;
term p (x: s): wff;
--| @saturation ltr
theorem bad (x: s): $ p x $;
"#;
        let env = parse_env(input).unwrap();
        let errors = validate_metadata(&env);

        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("declared relation"));
    }
}
