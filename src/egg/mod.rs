use serde::{Deserialize, Serialize};

use crate::{EggbauError, PINNED_EGGLOG};

/// Result of the stage-0 proof API spike.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EgglogProofApiSpike {
    pub egglog_version: String,
    pub term_encoding_runs: bool,
    pub prove_exists_command_available: bool,
    pub structured_proof_api_available: bool,
    pub note: String,
}

/// Run a tiny proof-mode-adjacent egglog program through the Rust API.
///
/// egglog 2.0.0 exposes term encoding, but not the `ProofStore`/
/// `Justification` API described in `PLAN.md`.  This function records that
/// decision explicitly so later work can replace the pin or carry a patch.
pub fn run_proof_api_spike() -> Result<EgglogProofApiSpike, EggbauError> {
    let mut egraph = egglog::EGraph::new_with_term_encoding();
    egraph
        .parse_and_run_program(
            None,
            r#"
(sort Expr)
(constructor A () Expr)
(constructor B () Expr)
(union (A) (B))
(run-schedule (saturate (run)))
(check (= (A) (B)))
"#,
        )
        .map_err(|err| EggbauError::Egglog(err.to_string()))?;

    Ok(EgglogProofApiSpike {
        egglog_version: PINNED_EGGLOG.to_owned(),
        term_encoding_runs: true,
        prove_exists_command_available: false,
        structured_proof_api_available: false,
        note: concat!(
            "egglog 2.0.0 has no public CommandOutput::ProveExists or ",
            "read-only ProofStore/Justification API; use a patch or newer pin"
        )
        .to_owned(),
    })
}
