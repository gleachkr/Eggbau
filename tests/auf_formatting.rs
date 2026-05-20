use std::fs;
use std::path::PathBuf;

use eggbau::auf::{AufMathFormat, AufRenderCompaction, AufRenderFormat, AufRenderOptions};
use eggbau::cert::{self, CertStep, Certificate, Label, Term};
use eggbau::{EggbauOptions, EggbauSession, OutputMode};

const E2E_PATH: &str = "tests/fixtures/cli_e2e.mm0";
const E2E: &str = include_str!("fixtures/cli_e2e.mm0");

#[test]
fn cli_format_values_are_orthogonal_and_last_value_wins() {
    let implicit_compact = eggbau::cli::run([
        "eggbau",
        "prove",
        E2E_PATH,
        "--theorem",
        "target",
        "--format",
        "implicit",
        "--format",
        "compact",
    ])
    .unwrap();
    assert!(implicit_compact.contains("by f_id []"));
    assert!(!implicit_compact.contains(":="));

    let explicit_after_implicit = eggbau::cli::run([
        "eggbau",
        "prove",
        E2E_PATH,
        "--theorem",
        "target",
        "--format",
        "implicit",
        "--format",
        "explicit",
    ])
    .unwrap();
    assert!(explicit_after_implicit.contains("x := $ x $"));

    let nocompact_after_compact = eggbau::cli::run([
        "eggbau",
        "prove",
        E2E_PATH,
        "--theorem",
        "target",
        "--format",
        "compact",
        "--format",
        "nocompact",
    ])
    .unwrap();
    let explicit_default =
        eggbau::cli::run(["eggbau", "prove", E2E_PATH, "--theorem", "target"]).unwrap();
    assert_eq!(nocompact_after_compact, explicit_default);
}

#[test]
fn cli_notation_format_is_orthogonal() {
    let path = temp_file("auf_format_notation.mm0");
    fs::write(
        &path,
        r#"
sort s;
provable sort wff;
term f (x: s): s;
term eq (x y: s): wff;
prefix f: $ƒ$ prec 80;
infixl eq: $=$ prec 10;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ x = x $;
axiom eq_trans (x y z: s): $ x = y $ > $ y = z $ > $ x = z $;
axiom eq_sym (x y: s): $ x = y $ > $ y = x $;
--| @saturation ltr
axiom f_id (x: s): $ ƒ x = x $;
theorem target (x: s): $ ƒ x = x $;
"#,
    )
    .unwrap();

    let rendered = eggbau::cli::run([
        "eggbau".to_owned(),
        "prove".to_owned(),
        path.display().to_string(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--format".to_owned(),
        "implicit".to_owned(),
        "--format".to_owned(),
        "notation".to_owned(),
    ])
    .unwrap();

    assert!(rendered.contains("$ ƒ x = x $"));
    assert!(rendered.contains("by f_id []"));
    assert!(!rendered.contains(":="));
}

#[test]
fn notation_format_renders_explicit_bindings() {
    let env = eggbau::mm0::parse_env(
        r#"
sort s;
provable sort wff;
term f (x: s): s;
term eq (x y: s): wff;
prefix f: $ƒ$ prec 80;
infixl eq: $=$ prec 10;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ x = x $;
axiom eq_trans (x y z: s): $ x = y $ > $ y = z $ > $ x = z $;
axiom eq_sym (x y: s): $ x = y $ > $ y = x $;
theorem target (x: s): $ ƒ x = ƒ x $;
"#,
    )
    .unwrap();
    let export = eggbau::export::ExportEnv::from_mm0(&env).unwrap();
    let cert = Certificate::new(vec![CertStep::EqRefl {
        label: Label::from("r"),
        relation: "eq".to_owned(),
        term: Term::app("f", vec![Term::var("x")]),
    }]);
    let format = AufRenderFormat {
        math: AufMathFormat::Notation,
        ..AufRenderFormat::explicit()
    };

    let rendered = eggbau::auf::render_certificate(
        &env,
        &export,
        "target",
        &cert,
        AufRenderOptions {
            output_mode: OutputMode::Fragment,
            format,
        },
    )
    .unwrap();

    assert!(rendered.text.contains("r: $ ƒ x = ƒ x $ by eq_refl"));
    assert!(rendered.text.contains("x := $ ƒ x $"));
}

#[test]
fn cli_unknown_format_value_is_clear() {
    let err = eggbau::cli::run([
        "eggbau",
        "prove",
        E2E_PATH,
        "--theorem",
        "target",
        "--format",
        "dense",
    ])
    .unwrap_err();

    assert!(
        err.to_string()
            .contains("unknown Aufbau output format: dense")
    );
}

#[test]
fn compact_session_output_is_deterministic() {
    let options = EggbauOptions {
        auf_format: AufRenderFormat::explicit().with_compaction(AufRenderCompaction::Compact),
        ..EggbauOptions::default()
    };
    let mut first = EggbauSession::from_mm0_with_options(E2E, options.clone()).unwrap();
    let mut second = EggbauSession::from_mm0_with_options(E2E, options).unwrap();

    let first = first.prove_theorem("target").unwrap();
    let second = second.prove_theorem("target").unwrap();

    assert_eq!(first.auf_block, second.auf_block);
    assert_eq!(
        first.certificate.to_pretty_json(),
        second.certificate.to_pretty_json()
    );
    assert!(
        first
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message.contains("certificate steps after"))
    );
}

#[test]
fn compact_certificate_deduplicates_internal_duplicate_formulas() {
    let env = eggbau::mm0::parse_env(
        r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
theorem target (x: s): $ eq x x $;
"#,
    )
    .unwrap();
    let export = eggbau::export::ExportEnv::from_mm0(&env).unwrap();
    let cert = Certificate::new(vec![
        CertStep::EqRefl {
            label: Label::from("r1"),
            relation: "eq".to_owned(),
            term: Term::var("x"),
        },
        CertStep::EqRefl {
            label: Label::from("r2"),
            relation: "eq".to_owned(),
            term: Term::var("x"),
        },
        CertStep::EqTrans {
            label: Label::from("goal"),
            relation: "eq".to_owned(),
            left: Label::from("r2"),
            right: Label::from("r1"),
        },
    ]);

    let (compact, stats) =
        cert::compact_certificate_for_theorem(&cert, &env, &export, "target").unwrap();

    assert_eq!(stats.before_steps, 3);
    assert_eq!(stats.after_steps, 2);
    assert!(matches!(
        &compact.steps[1],
        CertStep::EqTrans { left, right, .. }
            if left.as_str() == "r1" && right.as_str() == "r1"
    ));

    let no_compact = eggbau::auf::render_certificate(
        &env,
        &export,
        "target",
        &cert,
        AufRenderOptions::default(),
    )
    .unwrap();
    let compact_rendered = eggbau::auf::render_certificate(
        &env,
        &export,
        "target",
        &compact,
        AufRenderOptions {
            output_mode: OutputMode::Fragment,
            format: AufRenderFormat::explicit().with_compaction(AufRenderCompaction::Compact),
        },
    )
    .unwrap();

    assert!(proof_line_count(&compact_rendered.text) < proof_line_count(&no_compact.text));
}

#[test]
fn lint_reports_malformed_metadata() {
    let path = temp_file("auf_format_bad_metadata.mm0");
    fs::write(
        &path,
        r#"
sort s;
provable sort wff;
term eq (x y: s): wff;
--| @relation s eq missing_refl eq_trans eq_sym _
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
"#,
    )
    .unwrap();

    let err = eggbau::cli::run([
        "eggbau".to_owned(),
        "lint".to_owned(),
        path.display().to_string(),
    ])
    .unwrap_err();

    assert!(err.to_string().contains("metadata lint failed"));
    assert!(err.to_string().contains("missing_refl"));
}

fn proof_line_count(text: &str) -> usize {
    text.lines().filter(|line| line.contains(" by ")).count()
}

fn temp_file(name: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("eggbau_{}_{}", std::process::id(), name));
    path
}
