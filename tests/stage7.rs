use eggbau::cert::{CertStep, TranslateError, validate_certificate_for_theorem};
use eggbau::export::ExportEnv;
use eggbau::mm0::parse_env;

const HORN_BASE: &str = r#"
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
axiom p_congr (x y: s): $ eq x y $ > $ bi (p x) (p y) $;
--| @congr
axiom q_congr (x y: s): $ eq x y $ > $ bi (q x) (q y) $;
--| @saturation horn
axiom p_from_q (x: s): $ q x $ > $ p x $;
"#;

fn prove(input: &str) -> (eggbau::mm0::Mm0Env, ExportEnv, eggbau::cert::Certificate) {
    let env = parse_env(input).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let proof = eggbau::egg::prove_theorem(&env, &export, "target").unwrap();
    let cert = proof.certificate.expect("fact theorem has certificate");
    validate_certificate_for_theorem(&cert, &env, &export, "target").unwrap();
    (env, export, cert)
}

#[test]
fn translates_exact_horn_fact_proof_to_certificate_ir() {
    let input = format!("{HORN_BASE}\ntheorem target (x: s): $ q x $ > $ p x $;\n");
    let (_, _, cert) = prove(&input);

    assert!(matches!(
        cert.steps.as_slice(),
        [CertStep::Hyp { .. }, CertStep::RuleApply { .. }]
    ));
    assert!(cert.to_pretty_json().contains("p_from_q"));
}

#[test]
fn translates_horn_premise_transport_to_certificate_ir() {
    let input = format!(
        "{HORN_BASE}\ntheorem target (x y: s): \
         $ eq x y $ > $ q y $ > $ p x $;\n"
    );
    let (_, _, cert) = prove(&input);

    assert!(cert.steps.iter().any(|step| {
        matches!(step, CertStep::Transport { mm0_transport_rule, .. }
            if mm0_transport_rule == "bi_mp")
    }));
    assert!(cert.to_pretty_json().contains("q_congr"));
}

#[test]
fn translates_horn_conclusion_transport_to_certificate_ir() {
    let input = format!(
        "{HORN_BASE}\ntheorem target (x y: s): \
         $ eq x y $ > $ q x $ > $ p y $;\n"
    );
    let (_, _, cert) = prove(&input);

    assert!(cert.steps.iter().any(|step| {
        matches!(step, CertStep::Transport { mm0_transport_rule, .. }
            if mm0_transport_rule == "bi_mp")
    }));
    assert!(cert.to_pretty_json().contains("p_congr"));
}

#[test]
fn reports_missing_congruence_for_modulo_equality_fact_proof() {
    let input = r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
term p (x: s): wff;
term q (x: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation horn
axiom p_from_q (x: s): $ q x $ > $ p x $;
theorem target (x y: s): $ eq x y $ > $ q y $ > $ p x $;
"#;
    let env = parse_env(input).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let err = eggbau::egg::prove_theorem(&env, &export, "target").unwrap_err();

    assert!(matches!(
        err,
        eggbau::EggbauError::CertTranslate(TranslateError::MissingCongruence { .. })
    ));
}

#[test]
fn reports_missing_fact_transport_for_fact_congruence() {
    let input = r#"
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
--| @relation wff bi bi_refl bi_trans bi_sym _
axiom bi_refl (x: wff): $ bi x x $;
axiom bi_trans (x y z: wff): $ bi x y $ > $ bi y z $ > $ bi x z $;
axiom bi_sym (x y: wff): $ bi x y $ > $ bi y x $;
--| @congr
axiom q_congr (x y: s): $ eq x y $ > $ bi (q x) (q y) $;
--| @saturation horn
axiom p_from_q (x: s): $ q x $ > $ p x $;
theorem target (x y: s): $ eq x y $ > $ q y $ > $ p x $;
"#;
    let env = parse_env(input).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let err = eggbau::egg::prove_theorem(&env, &export, "target").unwrap_err();

    assert!(matches!(
        err,
        eggbau::EggbauError::CertTranslate(TranslateError::MissingFactTransport { .. })
    ));
}

#[test]
fn translates_horn_transport_for_non_wff_provable_sort() {
    let input = r#"
sort s;
provable sort prop;
term eq (x y: s): prop;
term iff (x y: prop): prop;
term p (x: s): prop;
term q (x: s): prop;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @relation prop iff iff_refl iff_trans iff_sym iff_mp
axiom iff_refl (x: prop): $ iff x x $;
axiom iff_trans (x y z: prop): $ iff x y $ > $ iff y z $ > $ iff x z $;
axiom iff_sym (x y: prop): $ iff x y $ > $ iff y x $;
axiom iff_mp (x y: prop): $ iff x y $ > $ x $ > $ y $;
--| @congr
axiom p_congr (x y: s): $ eq x y $ > $ iff (p x) (p y) $;
--| @congr
axiom q_congr (x y: s): $ eq x y $ > $ iff (q x) (q y) $;
--| @saturation horn
axiom p_from_q (x: s): $ q x $ > $ p x $;
theorem target (x y: s): $ eq x y $ > $ q y $ > $ p x $;
"#;
    let (_, export, cert) = prove(input);

    assert!(
        export
            .sorts
            .iter()
            .any(|sort| { sort.source_name == "prop" && sort.provable })
    );
    assert!(cert.steps.iter().any(|step| {
        matches!(step, CertStep::Transport { mm0_transport_rule, .. }
            if mm0_transport_rule == "iff_mp")
    }));
}
