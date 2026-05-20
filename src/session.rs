use serde::{Deserialize, Serialize};

use crate::auf::{self, AufRenderFormat};
use crate::cert::{self, Certificate};
use crate::export::ExportEnv;
use crate::mm0::{self, Mm0Env, TheoremDecl};
use crate::{Diagnostic, EggbauError, OutputMode};

/// Options used by the public library proof session.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EggbauOptions {
    pub output_mode: OutputMode,
    pub auf_format: AufRenderFormat,
    pub include_egglog_program: bool,
}

impl Default for EggbauOptions {
    fn default() -> Self {
        Self {
            output_mode: OutputMode::Fragment,
            auf_format: AufRenderFormat::explicit(),
            include_egglog_program: true,
        }
    }
}

/// A proof goal that can be supplied by a downstream library caller.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum GoalSpec {
    /// Prove a public theorem already declared in the MM0 source.
    Theorem { name: String },
    /// Prove a theorem declaration supplied by the caller.
    ///
    /// The header is the text after the `theorem` keyword, for example
    /// `target (x: s): $ eq (f x) x $`. A leading `theorem` keyword is also
    /// accepted for callers that keep complete declaration snippets.
    GeneratedTheorem { header: String },
}

impl GoalSpec {
    pub fn theorem(name: impl Into<String>) -> Self {
        Self::Theorem { name: name.into() }
    }

    pub fn generated_theorem(header: impl Into<String>) -> Self {
        Self::GeneratedTheorem {
            header: header.into(),
        }
    }
}

/// Result returned by the stable library API.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ProofResult {
    pub theorem: String,
    pub auf_block: String,
    pub egglog_program: Option<String>,
    pub certificate: Certificate,
    pub diagnostics: Vec<Diagnostic>,
}

/// Reusable proof-search session for Rust callers.
///
/// The session keeps parsed MM0 metadata and the validated export environment
/// in memory, so downstream tools can prove several generated obligations
/// without reparsing the input each time.
#[derive(Clone, Debug)]
pub struct EggbauSession {
    env: Mm0Env,
    export_env: ExportEnv,
    options: EggbauOptions,
}

impl EggbauSession {
    /// Parse MM0 source and build a validated export environment.
    pub fn from_mm0(mm0: &str) -> Result<Self, EggbauError> {
        Self::from_mm0_with_options(mm0, EggbauOptions::default())
    }

    /// Parse MM0 source using explicit library options.
    pub fn from_mm0_with_options(mm0: &str, options: EggbauOptions) -> Result<Self, EggbauError> {
        let env = mm0::parse_env(mm0)?;
        let export_env = ExportEnv::from_mm0(&env)?;
        Ok(Self {
            env,
            export_env,
            options,
        })
    }

    pub fn env(&self) -> &Mm0Env {
        &self.env
    }

    pub fn export_env(&self) -> &ExportEnv {
        &self.export_env
    }

    pub fn options(&self) -> &EggbauOptions {
        &self.options
    }

    pub fn options_mut(&mut self) -> &mut EggbauOptions {
        &mut self.options
    }

    /// Prove a public theorem already declared in the MM0 input.
    pub fn prove_theorem(&mut self, theorem: &str) -> Result<ProofResult, EggbauError> {
        self.prove_named_theorem(theorem)
    }

    /// Prove a public theorem and return only certificate IR.
    pub fn prove_to_cert(&mut self, theorem: &str) -> Result<Certificate, EggbauError> {
        self.prove_theorem(theorem).map(|result| result.certificate)
    }

    /// Prove a public theorem or caller-supplied generated theorem.
    pub fn prove_goal(&mut self, goal: GoalSpec) -> Result<ProofResult, EggbauError> {
        match goal {
            GoalSpec::Theorem { name } => self.prove_named_theorem(&name),
            GoalSpec::GeneratedTheorem { header } => {
                let decl = self.parse_generated_theorem(&header)?;
                let name = decl.name.clone();
                let original_len = self.env.theorems.len();
                self.env.theorems.push(decl);
                match self.prove_named_theorem(&name) {
                    Ok(result) => Ok(result),
                    Err(err) => {
                        self.env.theorems.truncate(original_len);
                        Err(err)
                    }
                }
            }
        }
    }

    /// Render certificate IR as an Aufbau block.
    ///
    /// If several theorems in the session match the same certificate, the
    /// first declaration-order theorem is used. Use `render_auf_for_theorem`
    /// when a caller needs to disambiguate.
    pub fn render_auf(&self, cert: &Certificate) -> Result<String, EggbauError> {
        let theorem = self
            .env
            .theorems
            .iter()
            .filter(|decl| decl.kind == mm0::AssertionKind::Theorem)
            .find(|decl| {
                cert::validate_certificate_for_theorem(
                    cert,
                    &self.env,
                    &self.export_env,
                    &decl.name,
                )
                .is_ok()
            })
            .map(|decl| decl.name.as_str())
            .ok_or_else(|| {
                EggbauError::UnsupportedCommand(
                    "certificate does not match a theorem in this session".to_owned(),
                )
            })?;
        self.render_auf_for_theorem(theorem, cert)
    }

    /// Render certificate IR for a known theorem name.
    pub fn render_auf_for_theorem(
        &self,
        theorem: &str,
        cert: &Certificate,
    ) -> Result<String, EggbauError> {
        let rendered = auf::render_certificate(
            &self.env,
            &self.export_env,
            theorem,
            cert,
            auf::AufRenderOptions {
                output_mode: self.options.output_mode.clone(),
                format: self.options.auf_format,
            },
        )?;
        Ok(rendered.text)
    }

    fn prove_named_theorem(&self, theorem: &str) -> Result<ProofResult, EggbauError> {
        let proof = crate::egg::prove_theorem(&self.env, &self.export_env, theorem)?;
        let certificate = proof
            .certificate
            .clone()
            .ok_or_else(|| EggbauError::Egglog("proof did not produce a certificate".to_owned()))?;
        let auf_block = self.render_auf_for_theorem(theorem, &certificate)?;
        let egglog_program = self
            .options
            .include_egglog_program
            .then_some(proof.egglog_program);
        Ok(ProofResult {
            theorem: theorem.to_owned(),
            auf_block,
            egglog_program,
            certificate,
            diagnostics: proof.diagnostics,
        })
    }

    fn parse_generated_theorem(&self, header: &str) -> Result<TheoremDecl, EggbauError> {
        let header = normalize_generated_header(header);
        let decl = mm0::parse_local_lemma_header(&self.env, &header)?;
        if self.env.theorem(&decl.name).is_some() {
            return Err(EggbauError::UnsupportedCommand(format!(
                "generated theorem target collides with existing assertion: {}",
                decl.name
            )));
        }
        if let Some(reason) = &decl.unsupported_reason {
            return Err(EggbauError::UnsupportedCommand(format!(
                "generated theorem `{}` uses unsupported syntax: {reason}",
                decl.name
            )));
        }
        if let Some(reason) = decl
            .hypotheses
            .iter()
            .chain(std::iter::once(&decl.conclusion))
            .find_map(|formula| formula.unsupported_reason.as_ref())
        {
            return Err(EggbauError::UnsupportedCommand(format!(
                "generated theorem `{}` uses unsupported syntax: {reason}",
                decl.name
            )));
        }
        Ok(decl)
    }
}

fn normalize_generated_header(header: &str) -> String {
    let trimmed = header.trim().trim_end_matches(';').trim();
    trimmed
        .strip_prefix("theorem ")
        .unwrap_or(trimmed)
        .trim()
        .to_owned()
}
