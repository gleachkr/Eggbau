use eggbau::cert::{CertStep, validate_certificate_for_theorem};
use eggbau::export::ExportEnv;
use eggbau::mm0::parse_env;

const LTR_INPUT: &str = r#"
sort s;
provable sort wff;
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

const RTL_INPUT: &str = r#"
sort s;
provable sort wff;
term pair (x y: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation rtl
axiom pair_comm (x y: s): $ eq (pair x y) (pair y x) $;
theorem target (x y: s): $ eq (pair y x) (pair x y) $;
"#;

const BOTH_INPUT: &str = r#"
sort s;
provable sort wff;
term pair (x y: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq y x $ > $ eq x y $;
--| @saturation both
axiom pair_comm (x y: s): $ eq (pair x y) (pair y x) $;
theorem target (x y: s): $ eq (pair y x) (pair x y) $;
"#;

const TRANS_INPUT: &str = r#"
sort s;
provable sort wff;
term f (x: s): s;
term g (x: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation ltr
axiom f_to_g (x: s): $ eq (f x) (g x) $;
--| @saturation ltr
axiom g_id (x: s): $ eq (g x) x $;
theorem target (x: s): $ eq (f x) x $;
"#;

const CONGR_INPUT: &str = r#"
sort s;
provable sort wff;
term f (x: s): s;
term h (x: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @congr
axiom h_congr (x y: s): $ eq x y $ > $ eq (h x) (h y) $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
theorem target (x: s): $ eq (h (f x)) (h x) $;
"#;

fn prove_cert(input: &str) -> (eggbau::mm0::Mm0Env, ExportEnv, eggbau::cert::Certificate) {
    let env = parse_env(input).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let proof = eggbau::egg::prove_theorem(&env, &export, "target").unwrap();
    let cert = proof.certificate.expect("equality theorem has certificate");
    validate_certificate_for_theorem(&cert, &env, &export, "target").unwrap();
    (env, export, cert)
}

#[test]
fn translates_ltr_conversion_to_certificate_ir() {
    let (_, _, cert) = prove_cert(LTR_INPUT);

    assert!(matches!(
        cert.steps.as_slice(),
        [CertStep::RuleApply { .. }]
    ));
}

#[test]
fn translates_rtl_conversion_with_explicit_symmetry() {
    let (_, _, cert) = prove_cert(RTL_INPUT);

    assert!(
        cert.steps
            .iter()
            .any(|step| matches!(step, CertStep::EqSym { .. }))
    );
}

#[test]
fn translates_bidirectional_reverse_rule_with_symmetry() {
    let (_, _, cert) = prove_cert(BOTH_INPUT);

    assert!(
        cert.steps
            .iter()
            .any(|step| matches!(step, CertStep::EqSym { .. }))
    );
    assert!(cert.to_pretty_json().contains("pair_comm"));
}

#[test]
fn translates_transitive_equality_chain() {
    let (_, _, cert) = prove_cert(TRANS_INPUT);

    assert!(
        cert.steps
            .iter()
            .any(|step| matches!(step, CertStep::EqTrans { .. }))
    );
}

#[test]
fn translates_congruence_using_mm0_congruence_rule() {
    let (_, _, cert) = prove_cert(CONGR_INPUT);

    assert!(
        cert.steps
            .iter()
            .any(|step| matches!(step, CertStep::EqCongr { .. }))
    );
    assert!(cert.to_pretty_json().contains("h_congr"));
}
