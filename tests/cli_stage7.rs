use std::io::Write;
use std::process::{Command, Stdio};

const CONVERSION_FIXTURE: &str = "tests/fixtures/stage4_conversion.mm0";
const MULTI_FIXTURE: &str = "tests/fixtures/cli_multi.mm0";

#[test]
fn script_check_accepts_a_freshly_emitted_script() {
    let script = eggbau::cli::run([
        "eggbau",
        "script",
        "emit",
        CONVERSION_FIXTURE,
        "--theorem",
        "target",
    ])
    .unwrap();
    let script_path = temp_script_path("fresh");
    std::fs::write(&script_path, script).unwrap();

    let output = eggbau::cli::run([
        "eggbau".to_owned(),
        "script".to_owned(),
        "check".to_owned(),
        CONVERSION_FIXTURE.to_owned(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--script".to_owned(),
        script_path.to_string_lossy().into_owned(),
    ])
    .unwrap();
    std::fs::remove_file(script_path).unwrap();

    assert!(output.contains("\"theorem\": \"target\""));
    assert!(output.contains("Rule f_id"));
    assert!(output.contains("validated certificate IR"));
    assert!(!output.contains("target\n------\n"));
}

#[test]
fn script_check_accepts_script_from_stdin() {
    let script = eggbau::cli::run([
        "eggbau",
        "script",
        "emit",
        CONVERSION_FIXTURE,
        "--theorem",
        "target",
    ])
    .unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args([
            "script",
            "check",
            CONVERSION_FIXTURE,
            "--theorem",
            "target",
            "--script",
            "-",
        ])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(script.as_bytes())
        .unwrap();

    let output = child.wait_with_output().unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"theorem\": \"target\""));
    assert!(stdout.contains("Rule f_id"));
}

#[test]
fn script_check_rejects_a_script_for_the_wrong_theorem() {
    let script = eggbau::cli::run([
        "eggbau",
        "script",
        "emit",
        MULTI_FIXTURE,
        "--theorem",
        "first",
    ])
    .unwrap();
    let script_path = temp_script_path("wrong-theorem");
    std::fs::write(&script_path, script).unwrap();

    let err = eggbau::cli::run([
        "eggbau".to_owned(),
        "script".to_owned(),
        "check".to_owned(),
        MULTI_FIXTURE.to_owned(),
        "--theorem".to_owned(),
        "second".to_owned(),
        "--script".to_owned(),
        script_path.to_string_lossy().into_owned(),
    ])
    .unwrap_err();
    std::fs::remove_file(script_path).unwrap();

    assert!(err.to_string().contains("supplied egglog script proves"));
    assert!(err.to_string().contains("expected theorem second goal"));
}

#[test]
fn script_check_rejects_an_unknown_egglog_rule() {
    let script = eggbau::cli::run([
        "eggbau",
        "script",
        "emit",
        CONVERSION_FIXTURE,
        "--theorem",
        "target",
    ])
    .unwrap()
    .replace(":name \"f_id\"", ":name \"unknown_rule\"");
    let script_path = temp_script_path("unknown-rule");
    std::fs::write(&script_path, script).unwrap();

    let err = eggbau::cli::run([
        "eggbau".to_owned(),
        "script".to_owned(),
        "check".to_owned(),
        CONVERSION_FIXTURE.to_owned(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--script".to_owned(),
        script_path.to_string_lossy().into_owned(),
    ])
    .unwrap_err();
    std::fs::remove_file(script_path).unwrap();

    assert!(err.to_string().contains("egglog rule"));
    assert!(err.to_string().contains("unknown_rule"));
}

#[test]
fn old_prove_egglog_top_level_command_is_rejected() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .arg("prove-egglog")
        .output()
        .unwrap();

    assert!(!output.status.success());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("unsupported command: prove-egglog")
    );
}

fn temp_script_path(name: &str) -> std::path::PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "eggbau-cli-stage7-{name}-{}-{}.egg",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    path
}
