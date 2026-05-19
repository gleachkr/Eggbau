use std::process::Command;

use eggbau::export::ExportEnv;
use eggbau::mm0::parse_env;
use eggbau::{EggbauConfig, OutputMode};

const CONVERSION_INPUT: &str = r#"
sort s;
provable sort wff;
term z: s;
term f (x: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
theorem target (x: s): $ eq (f x) x $;
"#;

const HORN_INPUT: &str = r#"
sort s;
provable sort wff;
term z: s;
term eq (x y: s): wff;
term p (x: s): wff;
term q (x: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation horn
axiom p_from_q (x: s): $ q x $ > $ p x $;
theorem target (x: s): $ q x $ > $ p x $;
"#;

const MODULO_EQUALITY_INPUT: &str = r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
term bi (x y: wff): wff;
term p (x: s): wff;
term q (x: s): wff;
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
axiom q_congr (x y: s): $ eq x y $ > $ bi (q x) (q y) $;
--| @saturation horn
axiom p_from_q (x: s): $ q x $ > $ p x $;
theorem target (x y: s): $ eq x y $ > $ q y $ > $ p x $;
"#;

#[test]
fn proves_designated_equality_theorem_and_extracts_proof() {
    let env = parse_env(CONVERSION_INPUT).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let proof = eggbau::egg::prove_theorem(&env, &export, "target").unwrap();

    assert_eq!(proof.theorem, "target");
    assert_eq!(proof.goal.constructor, "ProvenEqS");
    assert!(proof.egglog_program.contains("(prove (ProvenEqS"));
    assert!(proof.proof_debug.contains("Rule f_id"));
    assert!(proof.proof_debug.contains("Rule prove_eq_s"));
    assert!(proof.proof_summary.rule >= 2);
}

#[test]
fn theorem_hypothesis_becomes_allowed_input_fact() {
    let env = parse_env(HORN_INPUT).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let proof = eggbau::egg::prove_theorem(&env, &export, "target").unwrap();

    assert_eq!(proof.goal.constructor, "ProvenP");
    assert!(proof.proof_debug.contains("Rule p_from_q"));
    assert!(proof.allowed_fiats.iter().any(|fiat| {
        fiat.proposition.contains("q (EggbauVarTargetX)")
            && fiat.reason == eggbau::egg::FiatReason::TheoremHypothesis
    }));
}

#[test]
fn horn_rule_can_match_modulo_equality_and_records_fiat_hypotheses() {
    let env = parse_env(MODULO_EQUALITY_INPUT).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let proof = eggbau::egg::prove_theorem(&env, &export, "target").unwrap();

    assert!(proof.proof_debug.contains("Congr child"));
    assert!(
        proof
            .allowed_fiats
            .iter()
            .any(|fiat| { fiat.proposition == "(EggbauVarTargetY) = (EggbauVarTargetX)" })
    );
}

#[test]
fn unprovable_goal_is_reported_as_proof_extraction_failure() {
    let input = CONVERSION_INPUT.replace("--| @saturation ltr", "-- no saturation");
    let env = parse_env(&input).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let err = eggbau::egg::prove_theorem(&env, &export, "target").unwrap_err();

    assert!(err.to_string().contains("Could not find a proof"));
}

#[test]
fn public_prove_theorem_api_wraps_stage_four_result() {
    let result = eggbau::prove_theorem(
        CONVERSION_INPUT,
        EggbauConfig {
            theorem: Some("target".to_owned()),
            output_mode: OutputMode::Fragment,
            allow_synthetic_discovery: false,
        },
    )
    .unwrap();

    assert!(result.auf.is_empty());
    assert!(
        result
            .egglog_program
            .contains("theorem-local symbolic inputs")
    );
    assert!(result.certificate_json.get("stage4_proof").is_some());
}

#[test]
fn cli_prove_egglog_outputs_stage_four_json() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args([
            "prove-egglog",
            "tests/fixtures/stage4_conversion.mm0",
            "--theorem",
            "target",
        ])
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"theorem\": \"target\""));
    assert!(stdout.contains("Rule f_id"));
}
