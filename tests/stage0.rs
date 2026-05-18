use std::path::Path;
use std::process::Command;

use eggbau::auf::labels::LabelGenerator;
use eggbau::cert::Certificate;
use eggbau::discover::render_empty_discovery;
use eggbau::egg::run_proof_api_spike;
use eggbau::export::{ExportEnv, render_empty_egglog};

#[test]
fn version_report_mentions_stage0_contracts() {
    let report = eggbau::version_report();

    assert!(report.contains("eggbau 0.1.0"));
    assert!(report.contains("egglog 2.0.0"));
    assert!(report.contains("Fiat, Rule, Trans, Sym, Congr"));
    assert!(report.contains("MergeFn"));
    assert!(report.contains("@saturation ltr"));
    assert!(!report.contains("@rewrite"));
}

#[test]
fn empty_discovery_output_is_snapshotted() {
    let path = Path::new("tests/fixtures/empty/input.mm0");
    let input = std::fs::read_to_string(path).unwrap();
    let output = render_empty_discovery(path, &input);

    insta::assert_snapshot!(output);
}

#[test]
fn fixture_expected_files_are_byte_compared() {
    let fixture = Path::new("tests/fixtures/empty");
    let env = ExportEnv::default();
    let cert = Certificate::empty();

    let expected_egg = std::fs::read_to_string(fixture.join("expected.egg")).unwrap();
    let expected_cert = std::fs::read_to_string(fixture.join("expected.cert.json")).unwrap();
    let expected_auf = std::fs::read_to_string(fixture.join("expected.auf")).unwrap();

    let actual_cert = serde_json::to_string_pretty(&cert).unwrap() + "\n";

    assert_eq!(render_empty_egglog(&env), expected_egg);
    assert_eq!(actual_cert, expected_cert);
    assert_eq!(String::new(), expected_auf);
}

#[test]
fn label_generation_is_byte_deterministic() {
    let labels = || {
        let mut generator = LabelGenerator::new("eggbau_");
        (0..5).map(|_| generator.fresh()).collect::<Vec<_>>()
    };

    assert_eq!(labels(), labels());
}

#[test]
fn proof_api_spike_documents_current_gap() {
    let spike = run_proof_api_spike().unwrap();

    assert_eq!(spike.egglog_version, "2.0.0");
    assert!(spike.term_encoding_runs);
    assert!(!spike.prove_exists_command_available);
    assert!(!spike.structured_proof_api_available);
}

#[test]
fn cli_version_smoke_test() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .arg("--version")
        .output()
        .unwrap();

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("eggbau 0.1.0"));
    assert!(stdout.contains("egglog 2.0.0"));
}

#[test]
fn cli_discover_is_deterministic() {
    let binary = env!("CARGO_BIN_EXE_eggbau");
    let file = "tests/fixtures/empty/input.mm0";

    let first = Command::new(binary)
        .args(["discover", file])
        .output()
        .unwrap();
    let second = Command::new(binary)
        .args(["discover", file])
        .output()
        .unwrap();

    assert!(first.status.success());
    assert!(second.status.success());
    assert_eq!(first.stdout, second.stdout);
    assert!(first.stderr.is_empty());
    assert!(second.stderr.is_empty());
}
