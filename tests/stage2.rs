use std::path::Path;
use std::process::Command;

mod common;

use eggbau::discover::{DiscoveryReport, validate_metadata};
use eggbau::export::ExportEnv;
use eggbau::mm0::parse_env;

const STAGE2_INPUT: &str = include_str!("fixtures/stage2/input.mm0");

#[test]
fn discovers_conversion_horn_and_congruence_candidates() {
    let env = parse_env(STAGE2_INPUT).unwrap();
    let report = DiscoveryReport::from_env(&env);

    assert_eq!(
        report
            .possible_conversions
            .iter()
            .map(|candidate| candidate.theorem.as_str())
            .collect::<Vec<_>>(),
        ["f_id", "rewrite_only"]
    );
    assert_eq!(report.possible_horn_rules[0].theorem, "p_from_q");
    assert_eq!(report.possible_congruences[0].theorem, "g_congr");
    assert!(report.metadata_errors.is_empty());
}

#[test]
fn discover_rendering_is_deterministic_and_suggests_annotations() {
    let output = eggbau::discover::render_discovery(
        Path::new("tests/fixtures/stage2/input.mm0"),
        STAGE2_INPUT,
        true,
    )
    .unwrap();

    let expected = concat!(
        "discovery report\n",
        "input: tests/fixtures/stage2/input.mm0\n",
        "\n",
        "possible saturation conversions:\n",
        "  f_id: eq (f x) x\n",
        "    suggested annotation: --| @saturation ltr\n",
        "  rewrite_only: eq (g x) x\n",
        "    suggested annotation: --| @saturation ltr\n",
        "\n",
        "possible saturation horn rules:\n",
        "  p_from_q: q x -> p x\n",
        "    suggested annotation: --| @saturation horn\n",
        "\n",
        "possible congruences:\n",
        "  g_congr: eq a b -> eq (g a) (g b)\n",
        "    existing annotation needed: --| @congr\n",
        "\n",
        "suggested annotation patch:\n",
        "  before theorem f_id:\n",
        "    + --| @saturation ltr\n",
        "  before theorem rewrite_only:\n",
        "    + --| @saturation ltr\n",
        "  before theorem p_from_q:\n",
        "    + --| @saturation horn\n",
    );

    assert_eq!(output, expected);
}

#[test]
fn hilbert_style_modus_ponens_is_not_a_v1_horn_candidate() {
    let env = parse_env(
        r#"
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
"#,
    )
    .unwrap();
    let report = DiscoveryReport::from_env(&env);

    assert!(report.possible_horn_rules.is_empty());
}

#[test]
fn zero_premise_fact_producing_rule_is_not_a_horn_candidate() {
    let env = parse_env(
        r#"
provable sort wff;
term p: wff;
axiom p_axiom: $ p $;
"#,
    )
    .unwrap();
    let report = DiscoveryReport::from_env(&env);

    assert!(report.possible_horn_rules.is_empty());
}

#[test]
fn judgment_modus_ponens_accepts_unparenthesized_prefix_argument() {
    let env = parse_env(
        r#"
delimiter $ ( ) $;
provable sort jdg;
sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
term provable (a: wff): jdg; prefix provable: $⊢$ prec 25;
--| @saturation horn
axiom mp (a b: wff): $ ⊢ a $ > $ ⊢ a -> b $ > $ ⊢ b $;
"#,
    )
    .unwrap();

    assert!(validate_metadata(&env).is_empty());
}

#[test]
fn annotated_hilbert_style_modus_ponens_is_rejected_as_unsupported() {
    let env = parse_env(
        r#"
delimiter $ ( ) $;
provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
--| @saturation horn
axiom mp (a b: wff): $ a $ > $ a -> b $ > $ b $;
"#,
    )
    .unwrap();
    let errors = validate_metadata(&env);

    assert_eq!(errors[0].theorem, "mp");
    assert!(errors[0].message.contains("atomic fact relation"));
}

#[test]
fn annotated_zero_premise_horn_rule_is_rejected() {
    let env = parse_env(
        r#"
provable sort wff;
term p: wff;
--| @saturation horn
axiom p_axiom: $ p $;
"#,
    )
    .unwrap();
    let errors = validate_metadata(&env);

    assert_eq!(errors[0].theorem, "p_axiom");
    assert!(errors[0].message.contains("at least one premise"));
}

#[test]
fn cli_discover_supports_suggest_annotations() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args([
            "discover",
            "tests/fixtures/stage2/input.mm0",
            "--suggest-annotations",
        ])
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("suggested annotation patch"));
    assert!(stdout.contains("before theorem p_from_q"));
}

#[test]
fn discover_stress_runs_on_extracted_mm0_fixture_inventory() {
    let paths = common::all_third_party_fixture_paths();

    let mut totals = DiscoveryStressTotals::default();
    for path in &paths {
        let input = std::fs::read_to_string(path).unwrap();
        let env = parse_env(&input)
            .unwrap_or_else(|err| panic!("fixture {} did not parse: {err}", path.display()));
        let report = DiscoveryReport::from_env(&env);
        let rendered = report.render(path, true);

        assert_eq!(rendered, report.render(path, true));
        assert!(rendered.contains("possible saturation conversions:"));
        assert!(rendered.contains("possible saturation horn rules:"));
        assert!(rendered.contains("possible congruences:"));

        totals.conversions += report.possible_conversions.len();
        totals.horn_rules += report.possible_horn_rules.len();
        totals.congruences += report.possible_congruences.len();
        totals.metadata_errors += report.metadata_errors.len();
    }

    assert_eq!(paths.len(), 47);
    assert_eq!(totals.conversions, 117);
    assert_eq!(totals.horn_rules, 17);
    assert_eq!(totals.congruences, 0);
    assert_eq!(totals.metadata_errors, 47);
}

#[derive(Default)]
struct DiscoveryStressTotals {
    conversions: usize,
    horn_rules: usize,
    congruences: usize,
    metadata_errors: usize,
}

#[test]
fn saturation_ltr_with_hypotheses_is_rejected_by_export_validation() {
    let env = parse_env(
        r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation ltr
axiom bad (x y: s): $ eq x y $ > $ eq y x $;
"#,
    )
    .unwrap();

    let err = ExportEnv::from_mm0(&env).unwrap_err();

    assert_eq!(err.theorem, "bad");
    assert!(err.reason.contains("may not have hypotheses"));
}

#[test]
fn saturation_horn_with_relation_conclusion_is_rejected() {
    let env = parse_env(
        r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
term p (x: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation horn
axiom bad (x y: s): $ p x $ > $ eq x y $;
"#,
    )
    .unwrap();

    let errors = validate_metadata(&env);

    assert_eq!(errors[0].theorem, "bad");
    assert!(errors[0].message.contains("atomic fact"));
}

#[test]
fn congruence_shape_mismatch_is_rejected() {
    let env = parse_env(
        r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
term f (x: s): s;
term g (x: s): s;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @congr
axiom bad (a b: s): $ eq a b $ > $ eq (f a) (g b) $;
"#,
    )
    .unwrap();

    let err = ExportEnv::from_mm0(&env).unwrap_err();

    assert_eq!(err.theorem, "bad");
    assert!(err.reason.contains("different heads"));
}

#[test]
fn relation_references_missing_theorem_is_rejected() {
    let env = parse_env(
        r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
--| @relation s eq eq_refl missing_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
"#,
    )
    .unwrap();

    let err = ExportEnv::from_mm0(&env).unwrap_err();

    assert_eq!(err.theorem, "missing_trans");
    assert!(err.reason.contains("not declared"));
}

#[test]
fn rewrite_only_theorem_is_not_exported_without_saturation() {
    let env = parse_env(STAGE2_INPUT).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();

    assert!(
        !export
            .assertions
            .iter()
            .any(|assertion| assertion.theorem == "rewrite_only")
    );
    assert!(
        export
            .assertions
            .iter()
            .any(|assertion| assertion.theorem == "annotated")
    );
}
