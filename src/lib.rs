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

use serde::{Deserialize, Serialize};
use thiserror::Error;

/// The vendored egglog dependency is intentionally pinned in `Cargo.toml`.
pub const PINNED_EGGLOG: &str = "2.0.0";

/// Proof justifications eggbau intends to reconstruct in MM0/Aufbau.
pub const SUPPORTED_PROOF_JUSTIFICATIONS: &[&str] = &["Fiat", "Rule", "Trans", "Sym", "Congr"];

/// Proof justifications that are known but not accepted by v1 reconstruction.
pub const REJECTED_PROOF_JUSTIFICATIONS: &[&str] = &["MergeFn"];

/// Assertion metadata forms consumed by the first eggbau stages.
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

/// Placeholder result shape for the staged implementation.
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
    ParseMm0(#[from] mm0::Mm0ParseError),

    #[error("unsupported command: {0}")]
    UnsupportedCommand(String),
}

/// Run the current proof-search pipeline for a designated theorem.
pub fn prove_theorem(mm0: &str, config: EggbauConfig) -> Result<ProveResult, EggbauError> {
    let theorem = config.theorem.ok_or_else(|| {
        EggbauError::UnsupportedCommand("prove_theorem requires a theorem name".to_owned())
    })?;
    let env = mm0::parse_env(mm0)?;
    let export_env = export::ExportEnv::from_mm0(&env)?;
    let proof = egg::prove_theorem(&env, &export_env, &theorem)?;
    let mut certificate_json = serde_json::to_value(
        proof
            .certificate
            .clone()
            .unwrap_or_else(cert::Certificate::empty),
    )
    .expect("certificate should serialize to JSON");
    if let serde_json::Value::Object(object) = &mut certificate_json {
        object.insert(
            "stage4_proof".to_owned(),
            serde_json::to_value(&proof).expect("stage4 proof should serialize"),
        );
    }

    Ok(ProveResult {
        auf: String::new(),
        egglog_program: proof.egglog_program,
        certificate_json,
        diagnostics: proof.diagnostics,
    })
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
