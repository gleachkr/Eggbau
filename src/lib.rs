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
    ParseMm0(#[from] mm0::Mm0ParseError),

    #[error("unsupported command: {0}")]
    UnsupportedCommand(String),
}

/// Stage-0 stub for the future proof search entry point.
pub fn prove_theorem(_mm0: &str, _config: EggbauConfig) -> Result<ProveResult, EggbauError> {
    Err(EggbauError::UnsupportedCommand(
        "proof search is not implemented in stage 0".to_owned(),
    ))
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
