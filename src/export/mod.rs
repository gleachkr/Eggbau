use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::discover::{MetadataKind, validate_metadata};
use crate::mm0::{Formula, Mm0Env, SaturationMode, TheoremDecl};

/// Minimal validated export environment for annotated MM0 assertions.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExportEnv {
    pub sorts: Vec<String>,
    pub terms: Vec<String>,
    pub assertions: Vec<ExportAssertion>,
}

impl ExportEnv {
    pub fn from_mm0(env: &Mm0Env) -> Result<Self, ExportValidationError> {
        if let Some(error) = validate_metadata(env).into_iter().next() {
            return Err(ExportValidationError {
                theorem: error.theorem,
                use_kind: export_use_for_metadata(error.metadata_kind),
                reason: error.message,
            });
        }

        let mut assertions = Vec::new();

        for relation in &env.metadata.relations {
            validate_named_assertion(env, &relation.reflexivity, ExportUse::Relation)?;
            assertions.push(ExportAssertion {
                theorem: relation.reflexivity.clone(),
                use_kind: ExportUse::Relation,
                saturation_mode: None,
            });
            validate_named_assertion(env, &relation.transitivity, ExportUse::Relation)?;
            assertions.push(ExportAssertion {
                theorem: relation.transitivity.clone(),
                use_kind: ExportUse::Relation,
                saturation_mode: None,
            });
            validate_named_assertion(env, &relation.symmetry, ExportUse::Relation)?;
            assertions.push(ExportAssertion {
                theorem: relation.symmetry.clone(),
                use_kind: ExportUse::Relation,
                saturation_mode: None,
            });
            if let Some(transport) = &relation.transport {
                validate_named_assertion(env, transport, ExportUse::Relation)?;
                assertions.push(ExportAssertion {
                    theorem: transport.clone(),
                    use_kind: ExportUse::Relation,
                    saturation_mode: None,
                });
            }
        }

        for congruence in &env.metadata.congruences {
            validate_named_assertion(env, &congruence.theorem, ExportUse::Congruence)?;
            assertions.push(ExportAssertion {
                theorem: congruence.theorem.clone(),
                use_kind: ExportUse::Congruence,
                saturation_mode: None,
            });
        }

        for saturation in &env.metadata.saturations {
            validate_named_assertion(env, &saturation.theorem, ExportUse::Saturation)?;
            assertions.push(ExportAssertion {
                theorem: saturation.theorem.clone(),
                use_kind: ExportUse::Saturation,
                saturation_mode: Some(saturation.mode),
            });
        }

        Ok(Self {
            sorts: env.sorts.iter().map(|sort| sort.name.clone()).collect(),
            terms: env.terms.iter().map(|term| term.name.clone()).collect(),
            assertions,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExportAssertion {
    pub theorem: String,
    pub use_kind: ExportUse,
    pub saturation_mode: Option<SaturationMode>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExportUse {
    Relation,
    Congruence,
    Saturation,
}

#[derive(Debug, Error, Eq, PartialEq)]
#[error("cannot export {theorem} as {use_kind}: {reason}")]
pub struct ExportValidationError {
    pub theorem: String,
    pub use_kind: ExportUse,
    pub reason: String,
}

fn export_use_for_metadata(kind: MetadataKind) -> ExportUse {
    match kind {
        MetadataKind::Relation => ExportUse::Relation,
        MetadataKind::Congruence => ExportUse::Congruence,
        MetadataKind::Saturation => ExportUse::Saturation,
    }
}

impl std::fmt::Display for ExportUse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Relation => f.write_str("relation metadata"),
            Self::Congruence => f.write_str("congruence metadata"),
            Self::Saturation => f.write_str("saturation rule"),
        }
    }
}

fn validate_named_assertion(
    env: &Mm0Env,
    theorem: &str,
    use_kind: ExportUse,
) -> Result<(), ExportValidationError> {
    let theorem_decl = env.theorem(theorem).ok_or_else(|| ExportValidationError {
        theorem: theorem.to_owned(),
        use_kind,
        reason: "referenced theorem was not declared".to_owned(),
    })?;
    validate_theorem(theorem_decl, use_kind)
}

fn validate_theorem(
    theorem: &TheoremDecl,
    use_kind: ExportUse,
) -> Result<(), ExportValidationError> {
    if let Some(reason) = &theorem.unsupported_reason {
        return Err(ExportValidationError {
            theorem: theorem.name.clone(),
            use_kind,
            reason: reason.clone(),
        });
    }

    for formula in theorem
        .hypotheses
        .iter()
        .chain(std::iter::once(&theorem.conclusion))
    {
        validate_formula(&theorem.name, formula, use_kind)?;
    }

    Ok(())
}

fn validate_formula(
    theorem: &str,
    formula: &Formula,
    use_kind: ExportUse,
) -> Result<(), ExportValidationError> {
    if let Some(reason) = &formula.unsupported_reason {
        return Err(ExportValidationError {
            theorem: theorem.to_owned(),
            use_kind,
            reason: reason.clone(),
        });
    }
    if formula.expr.is_none() {
        return Err(ExportValidationError {
            theorem: theorem.to_owned(),
            use_kind,
            reason: "formula did not parse to a kernel expression".to_owned(),
        });
    }
    Ok(())
}

pub fn render_empty_egglog(_env: &ExportEnv) -> String {
    String::new()
}
