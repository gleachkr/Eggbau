//! Library entry points for eggbau.
//!
//! Eggbau is an untrusted proof-search and proof-elaboration tool.  It emits
//! ordinary Aufbau proof scripts; MM0 verification remains external.

pub mod auf;
pub mod cert;
pub mod cli;
pub mod discover;
pub mod egg;
pub mod export;
pub mod mm0;
mod session;

pub use session::{EggbauOptions, EggbauSession, GoalSpec, ProofResult};

use std::collections::HashSet;

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// The vendored egglog dependency is intentionally pinned in `Cargo.toml`.
pub const PINNED_EGGLOG: &str = "2.0.0";

/// Proof justifications eggbau intends to reconstruct in MM0/Aufbau.
pub const SUPPORTED_PROOF_JUSTIFICATIONS: &[&str] = &["Fiat", "Rule", "Trans", "Sym", "Congr"];

/// Proof justifications that are known but not accepted by v1 reconstruction.
pub const REJECTED_PROOF_JUSTIFICATIONS: &[&str] = &["MergeFn"];

/// Assertion metadata forms consumed by eggbau export.
pub const SUPPORTED_METADATA_FORMS: &[&str] = &[
    "@saturation ltr",
    "@saturation rtl",
    "@saturation both",
    "@saturation horn",
];

/// Stable command output modes planned for Aufbau rendering.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum OutputMode {
    /// Emit only the requested theorem block.
    Fragment,
    /// Splice the generated block into an existing proof stream.
    Splice,
    /// Emit a complete proof stream in MM0 declaration order.
    FullStream,
}

/// Configuration for the future `prove_theorem` library entry point.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EggbauConfig {
    pub theorem: Option<String>,
    pub output_mode: OutputMode,
    pub allow_synthetic_discovery: bool,
}

/// A proof target accepted by the high-level proof pipeline.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ProofTarget {
    PublicTheorem { name: String },
    LocalLemma { name: String, header: String },
}

impl ProofTarget {
    pub fn name(&self) -> &str {
        match self {
            Self::PublicTheorem { name } | Self::LocalLemma { name, .. } => name,
        }
    }
}

/// Result shape for the high-level proof pipeline.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ProveResult {
    pub auf: String,
    pub egglog_program: String,
    pub certificate_json: serde_json::Value,
    pub diagnostics: Vec<Diagnostic>,
}

/// Human-readable diagnostic text with a stable severity spelling.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    pub message: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum DiagnosticSeverity {
    Info,
    Warning,
    Error,
}

#[derive(Debug, Error)]
pub enum EggbauError {
    #[error("I/O error while reading {path}: {source}")]
    ReadFile {
        path: String,
        #[source]
        source: std::io::Error,
    },

    #[error("I/O error while writing {path}: {source}")]
    WriteFile {
        path: String,
        #[source]
        source: std::io::Error,
    },

    #[error("egglog error: {0}")]
    Egglog(String),

    #[error("{0}")]
    Export(#[from] export::ExportValidationError),

    #[error("{0}")]
    CertTranslate(#[from] cert::TranslateError),

    #[error("{0}")]
    CertValidate(#[from] cert::CertValidationError),

    #[error("{0}")]
    AufRender(#[from] auf::AufRenderError),

    #[error("{0}")]
    ParseMm0(#[from] mm0::Mm0ParseError),

    #[error("unsupported command: {0}")]
    UnsupportedCommand(String),
}

/// Run the current proof-search pipeline for a designated theorem.
pub fn prove_theorem(mm0: &str, config: EggbauConfig) -> Result<ProveResult, EggbauError> {
    prove_theorem_with_auf_format(mm0, config, auf::AufRenderFormat::explicit())
}

/// Run the proof-search pipeline for public theorem targets.
///
/// The generated theorem blocks are emitted in MM0 declaration order, not in
/// caller order. If an emitted theorem has earlier public proof obligations
/// that are not included in `theorems`, the result contains a warning
/// diagnostic rather than failing.
pub fn prove_theorems(
    mm0: &str,
    theorems: &[String],
    output_mode: OutputMode,
) -> Result<ProveResult, EggbauError> {
    prove_theorems_with_auf_format(mm0, theorems, output_mode, auf::AufRenderFormat::explicit())
}

/// Run proof search for public theorem and proof-local lemma targets.
pub fn prove_targets(
    mm0: &str,
    targets: &[ProofTarget],
    output_mode: OutputMode,
) -> Result<ProveResult, EggbauError> {
    prove_targets_with_auf_format(mm0, targets, output_mode, auf::AufRenderFormat::explicit())
}

pub(crate) fn prove_theorem_with_auf_format(
    mm0: &str,
    config: EggbauConfig,
    auf_format: auf::AufRenderFormat,
) -> Result<ProveResult, EggbauError> {
    let EggbauConfig {
        theorem,
        output_mode,
        allow_synthetic_discovery: _,
    } = config;
    let theorem = theorem.ok_or_else(|| {
        EggbauError::UnsupportedCommand("prove_theorem requires a theorem name".to_owned())
    })?;
    let env = mm0::parse_env(mm0)?;
    let export_env = export::ExportEnv::from_mm0(&env)?;
    let proof = egg::prove_theorem(&env, &export_env, &theorem)?;
    let certificate = proof
        .certificate
        .clone()
        .unwrap_or_else(cert::Certificate::empty);
    let (certificate, compact_diagnostics) =
        maybe_compact_certificate(&certificate, &env, &export_env, &theorem, auf_format)?;
    let auf = auf::render_certificate(
        &env,
        &export_env,
        &theorem,
        &certificate,
        auf::AufRenderOptions {
            output_mode,
            format: auf_format,
        },
    )?;
    let mut certificate_json =
        serde_json::to_value(certificate).expect("certificate should serialize to JSON");
    if let serde_json::Value::Object(object) = &mut certificate_json {
        object.insert(
            "extracted_proof".to_owned(),
            serde_json::to_value(&proof).expect("extracted proof should serialize"),
        );
    }

    Ok(ProveResult {
        auf: auf.text,
        egglog_program: proof.egglog_program,
        certificate_json,
        diagnostics: extend_diagnostics(proof.diagnostics, compact_diagnostics),
    })
}

pub(crate) fn prove_theorems_with_auf_format(
    mm0: &str,
    theorems: &[String],
    output_mode: OutputMode,
    auf_format: auf::AufRenderFormat,
) -> Result<ProveResult, EggbauError> {
    if theorems.is_empty() {
        return Err(EggbauError::UnsupportedCommand(
            "at least one proof target is required".to_owned(),
        ));
    }

    let env = mm0::parse_env(mm0)?;
    let ordered_theorems = order_public_theorem_targets(&env, theorems)?;
    let export_env = export::ExportEnv::from_mm0(&env)?;
    let mut auf_text = String::new();
    let mut egglog_programs = Vec::new();
    let mut certificates = Vec::new();
    let mut diagnostics = stream_order_diagnostics(&env, &ordered_theorems);

    for theorem in &ordered_theorems {
        let proof = egg::prove_theorem(&env, &export_env, theorem)?;
        let certificate = proof
            .certificate
            .clone()
            .unwrap_or_else(cert::Certificate::empty);
        let (certificate, compact_diagnostics) =
            maybe_compact_certificate(&certificate, &env, &export_env, theorem, auf_format)?;
        let rendered = auf::render_certificate(
            &env,
            &export_env,
            theorem,
            &certificate,
            auf::AufRenderOptions {
                output_mode: output_mode.clone(),
                format: auf_format,
            },
        )?;

        if !auf_text.is_empty() && !auf_text.ends_with("\n\n") {
            auf_text.push('\n');
        }
        auf_text.push_str(&rendered.text);
        certificates.push(certificate_json_value(certificate, &proof));
        egglog_programs.push(proof.egglog_program);
        diagnostics.extend(proof.diagnostics);
        diagnostics.extend(compact_diagnostics);
    }

    Ok(ProveResult {
        auf: auf_text,
        egglog_program: egglog_programs.join("\n"),
        certificate_json: serde_json::Value::Array(certificates),
        diagnostics,
    })
}

pub(crate) fn prove_targets_with_auf_format(
    mm0: &str,
    targets: &[ProofTarget],
    output_mode: OutputMode,
    auf_format: auf::AufRenderFormat,
) -> Result<ProveResult, EggbauError> {
    if targets.is_empty() {
        return Err(EggbauError::UnsupportedCommand(
            "at least one proof target is required".to_owned(),
        ));
    }

    let env = mm0::parse_env(mm0)?;
    let prepared_targets = prepare_proof_targets(&env, targets)?;
    let mut proof_env = env.clone();
    proof_env
        .theorems
        .extend(prepared_targets.iter().filter_map(|target| match target {
            PreparedProofTarget::LocalLemma { decl, .. } => Some((**decl).clone()),
            PreparedProofTarget::PublicTheorem { .. } => None,
        }));
    let public_theorems = ordered_public_targets_from_prepared(&env, &prepared_targets);
    let export_env = export::ExportEnv::from_mm0(&env)?;
    let mut auf_text = String::new();
    let mut egglog_programs = Vec::new();
    let mut certificates = Vec::new();
    let mut diagnostics = stream_order_diagnostics(&env, &public_theorems);

    for target in prepared_targets
        .iter()
        .filter(|target| matches!(target, PreparedProofTarget::LocalLemma { .. }))
        .chain(public_theorems.iter().map(|name| {
            prepared_targets
                .iter()
                .find(|target| target.name() == name)
                .expect("ordered public target was prepared")
        }))
    {
        let theorem_env = match target {
            PreparedProofTarget::LocalLemma { .. } => &proof_env,
            PreparedProofTarget::PublicTheorem { .. } => &env,
        };
        let proof = egg::prove_theorem(theorem_env, &export_env, target.name())?;
        let certificate = proof
            .certificate
            .clone()
            .unwrap_or_else(cert::Certificate::empty);
        let (certificate, compact_diagnostics) = maybe_compact_certificate(
            &certificate,
            theorem_env,
            &export_env,
            target.name(),
            auf_format,
        )?;
        let options = auf::AufRenderOptions {
            output_mode: output_mode.clone(),
            format: auf_format,
        };
        let rendered = match target {
            PreparedProofTarget::LocalLemma { block_header, .. } => {
                auf::render_certificate_with_block_header(
                    theorem_env,
                    &export_env,
                    target.name(),
                    &certificate,
                    options,
                    Some(block_header),
                )?
            }
            PreparedProofTarget::PublicTheorem { .. } => auf::render_certificate(
                theorem_env,
                &export_env,
                target.name(),
                &certificate,
                options,
            )?,
        };

        append_rendered_block(&mut auf_text, &rendered.text);
        certificates.push(certificate_json_value(certificate, &proof));
        egglog_programs.push(proof.egglog_program);
        diagnostics.extend(proof.diagnostics);
        diagnostics.extend(compact_diagnostics);
    }

    Ok(ProveResult {
        auf: auf_text,
        egglog_program: egglog_programs.join("\n"),
        certificate_json: serde_json::Value::Array(certificates),
        diagnostics,
    })
}

#[derive(Clone, Debug)]
enum PreparedProofTarget {
    PublicTheorem {
        name: String,
    },
    LocalLemma {
        name: String,
        block_header: String,
        decl: Box<mm0::TheoremDecl>,
    },
}

impl PreparedProofTarget {
    fn name(&self) -> &str {
        match self {
            Self::PublicTheorem { name } | Self::LocalLemma { name, .. } => name,
        }
    }
}

fn prepare_proof_targets(
    env: &mm0::Mm0Env,
    targets: &[ProofTarget],
) -> Result<Vec<PreparedProofTarget>, EggbauError> {
    let mut seen = HashSet::new();
    let mut prepared = Vec::new();
    for target in targets {
        let name = target.name();
        if !seen.insert(name.to_owned()) {
            return Err(EggbauError::UnsupportedCommand(format!(
                "duplicate proof target: {name}"
            )));
        }
        match target {
            ProofTarget::PublicTheorem { name } => {
                validate_public_theorem_target(env, name)?;
                prepared.push(PreparedProofTarget::PublicTheorem { name: name.clone() });
            }
            ProofTarget::LocalLemma { name, header } => {
                if env.theorem(name).is_some() {
                    return Err(EggbauError::UnsupportedCommand(format!(
                        "local lemma target collides with public assertion: {name}"
                    )));
                }
                let decl = mm0::parse_local_lemma_header(env, header)?;
                if decl.name != *name {
                    return Err(EggbauError::UnsupportedCommand(format!(
                        "local lemma target name mismatch: expected {name}, found {}",
                        decl.name
                    )));
                }
                if let Some(reason) = &decl.unsupported_reason {
                    return Err(EggbauError::UnsupportedCommand(format!(
                        "local lemma target `{name}` uses unsupported syntax: {reason}"
                    )));
                }
                if let Some(reason) = decl
                    .hypotheses
                    .iter()
                    .chain(std::iter::once(&decl.conclusion))
                    .find_map(|formula| formula.unsupported_reason.as_ref())
                {
                    return Err(EggbauError::UnsupportedCommand(format!(
                        "local lemma target `{name}` uses unsupported syntax: {reason}"
                    )));
                }
                prepared.push(PreparedProofTarget::LocalLemma {
                    name: name.clone(),
                    block_header: format!("lemma {header}"),
                    decl: Box::new(decl),
                });
            }
        }
    }
    Ok(prepared)
}

fn validate_public_theorem_target(env: &mm0::Mm0Env, theorem: &str) -> Result<(), EggbauError> {
    match env.theorem(theorem) {
        Some(decl) if decl.kind == mm0::AssertionKind::Theorem => Ok(()),
        Some(_) => Err(EggbauError::UnsupportedCommand(format!(
            "proof target is not a public theorem: {theorem}"
        ))),
        None => Err(EggbauError::UnsupportedCommand(format!(
            "unknown proof target: {theorem}"
        ))),
    }
}

fn ordered_public_targets_from_prepared(
    env: &mm0::Mm0Env,
    targets: &[PreparedProofTarget],
) -> Vec<String> {
    let requested = targets
        .iter()
        .filter_map(|target| match target {
            PreparedProofTarget::PublicTheorem { name } => Some(name.as_str()),
            PreparedProofTarget::LocalLemma { .. } => None,
        })
        .collect::<HashSet<_>>();

    env.theorems
        .iter()
        .filter(|decl| decl.kind == mm0::AssertionKind::Theorem)
        .filter(|decl| requested.contains(decl.name.as_str()))
        .map(|decl| decl.name.clone())
        .collect()
}

fn append_rendered_block(out: &mut String, block: &str) {
    if !out.is_empty() && !out.ends_with("\n\n") {
        out.push('\n');
    }
    out.push_str(block);
}

fn maybe_compact_certificate(
    certificate: &cert::Certificate,
    env: &mm0::Mm0Env,
    export_env: &export::ExportEnv,
    theorem: &str,
    format: auf::AufRenderFormat,
) -> Result<(cert::Certificate, Vec<Diagnostic>), EggbauError> {
    if !format.compact_enabled() {
        return Ok((certificate.clone(), Vec::new()));
    }
    let (certificate, stats) =
        cert::compact_certificate_for_theorem(certificate, env, export_env, theorem)?;
    let diagnostics = vec![
        Diagnostic {
            severity: DiagnosticSeverity::Info,
            message: format!(
                "compact mode requested for theorem {theorem}: certificate steps before \
                 compaction: {}",
                stats.before_steps
            ),
        },
        Diagnostic {
            severity: DiagnosticSeverity::Info,
            message: format!(
                "compact mode requested for theorem {theorem}: certificate steps after \
                 compaction: {} (removed {})",
                stats.after_steps,
                stats.removed_steps()
            ),
        },
    ];
    Ok((certificate, diagnostics))
}

fn extend_diagnostics(mut diagnostics: Vec<Diagnostic>, extra: Vec<Diagnostic>) -> Vec<Diagnostic> {
    diagnostics.extend(extra);
    diagnostics
}

fn certificate_json_value(
    certificate: cert::Certificate,
    proof: &egg::TheoremProof,
) -> serde_json::Value {
    let mut certificate_json =
        serde_json::to_value(certificate).expect("certificate should serialize to JSON");
    if let serde_json::Value::Object(object) = &mut certificate_json {
        object.insert(
            "extracted_proof".to_owned(),
            serde_json::to_value(proof).expect("extracted proof should serialize"),
        );
    }
    certificate_json
}

fn order_public_theorem_targets(
    env: &mm0::Mm0Env,
    theorems: &[String],
) -> Result<Vec<String>, EggbauError> {
    let mut requested = HashSet::new();
    for theorem in theorems {
        if !requested.insert(theorem.as_str()) {
            return Err(EggbauError::UnsupportedCommand(format!(
                "duplicate proof target: {theorem}"
            )));
        }
        match env.theorem(theorem) {
            Some(decl) if decl.kind == mm0::AssertionKind::Theorem => {}
            Some(_) => {
                return Err(EggbauError::UnsupportedCommand(format!(
                    "proof target is not a public theorem: {theorem}"
                )));
            }
            None => {
                return Err(EggbauError::UnsupportedCommand(format!(
                    "unknown proof target: {theorem}"
                )));
            }
        }
    }

    Ok(env
        .theorems
        .iter()
        .filter(|decl| decl.kind == mm0::AssertionKind::Theorem)
        .filter(|decl| requested.contains(decl.name.as_str()))
        .map(|decl| decl.name.clone())
        .collect())
}

fn stream_order_diagnostics(env: &mm0::Mm0Env, ordered_theorems: &[String]) -> Vec<Diagnostic> {
    let requested = ordered_theorems
        .iter()
        .map(String::as_str)
        .collect::<HashSet<_>>();
    let mut missing_earlier = Vec::new();
    for decl in &env.theorems {
        if decl.kind != mm0::AssertionKind::Theorem {
            continue;
        }
        if requested.contains(decl.name.as_str()) {
            if !missing_earlier.is_empty() {
                let missing = missing_earlier.join(", ");
                return vec![Diagnostic {
                    severity: DiagnosticSeverity::Warning,
                    message: format!(
                        "emitted `{}` before earlier public obligations: {missing}\n\n\
                         The generated .auf may be useful for LSP or manual \
                         splicing, but may not compile as a standalone stream \
                         with `abc compile`.",
                        decl.name
                    ),
                }];
            }
        } else {
            missing_earlier.push(decl.name.clone());
        }
    }
    Vec::new()
}

/// Produce the long-form version report required by the CLI smoke tests.
pub fn version_report() -> String {
    let mut report = String::new();
    report.push_str(&format!("eggbau {}\n", env!("CARGO_PKG_VERSION")));
    report.push_str(&format!("egglog {} (vendored patch)\n", PINNED_EGGLOG));
    report.push_str(&format!(
        "supported proof justifications: {}\n",
        SUPPORTED_PROOF_JUSTIFICATIONS.join(", ")
    ));
    report.push_str(&format!(
        "rejected proof justifications: {}\n",
        REJECTED_PROOF_JUSTIFICATIONS.join(", ")
    ));
    report.push_str(&format!(
        "supported metadata forms: {}\n",
        SUPPORTED_METADATA_FORMS.join(", ")
    ));
    report
}
