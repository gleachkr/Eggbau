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

/// Run a tiny proof-mode egglog program through the Rust API.
///
/// This depends on the vendored egglog patch exposing a read-only proof API.
/// The spike does not translate proofs yet; it only checks that eggbau can
/// receive a structured `ProofStore`, inspect a `Justification`, and resolve
/// proof terms through the proof store's `TermDag`.
pub fn run_proof_api_spike() -> Result<EgglogProofApiSpike, EggbauError> {
    let mut egraph = egglog::EGraph::new_with_proofs();
    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
(sort Expr)
(constructor A () Expr)
(constructor B () Expr)
(ruleset demo)
(A)
(rule ((= x (A))) ((union x (B))) :ruleset demo)
(run-schedule (saturate (run demo)))
(prove-exists B)
"#,
        )
        .map_err(|err| EggbauError::Egglog(err.to_string()))?;

    let Some((proof_store, proof_id)) = outputs.iter().find_map(|output| match output {
        egglog::CommandOutput::ProveExists {
            proof_store,
            proof_id,
        } => Some((proof_store, proof_id)),
        _ => None,
    }) else {
        return Ok(EgglogProofApiSpike {
            egglog_version: PINNED_EGGLOG.to_owned(),
            term_encoding_runs: true,
            prove_exists_command_available: false,
            structured_proof_api_available: false,
            note: "vendored egglog did not return CommandOutput::ProveExists".to_owned(),
        });
    };

    let proof = proof_store.get(*proof_id);
    let proposition = proof.proposition();
    let _lhs = proof_store.term_dag().to_string(proposition.lhs());
    let _rhs = proof_store.term_dag().to_string(proposition.rhs());

    match proof.justification() {
        egglog::proof::Justification::Fiat
        | egglog::proof::Justification::Rule { .. }
        | egglog::proof::Justification::Trans(_, _)
        | egglog::proof::Justification::Sym(_)
        | egglog::proof::Justification::Congr { .. }
        | egglog::proof::Justification::MergeFn { .. } => {}
    }

    Ok(EgglogProofApiSpike {
        egglog_version: PINNED_EGGLOG.to_owned(),
        term_encoding_runs: true,
        prove_exists_command_available: true,
        structured_proof_api_available: true,
        note: concat!(
            "vendored egglog exposes CommandOutput::ProveExists and a ",
            "read-only ProofStore/Justification API"
        )
        .to_owned(),
    })
}
