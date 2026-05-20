use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

const CONVERSION_FIXTURE: &str = "tests/fixtures/conversion.mm0";

#[test]
fn script_prove_emitted_script_to_file() {
    let script = emit_target_script();
    let script_path = temp_path("emitted.egg");
    let out_path = temp_path("emitted.auf");
    std::fs::write(&script_path, script).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args([
            "script",
            "prove",
            CONVERSION_FIXTURE,
            "--theorem",
            "target",
            "--script",
            script_path.to_str().unwrap(),
            "--out",
            out_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    let auf = std::fs::read_to_string(out_path).unwrap();
    assert!(auf.contains("target\n------\n"));
    assert!(auf.contains("by f_id"));
}

#[test]
fn script_prove_accepts_script_from_stdin() {
    let script = emit_target_script();
    let mut child = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args([
            "script",
            "prove",
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
    assert!(stdout.contains("target\n------\n"));
    assert!(stdout.contains("by f_id"));
}

#[test]
fn script_prove_supports_explicit_format() {
    let script = emit_target_script();
    let script_path = temp_path("explicit.egg");
    std::fs::write(&script_path, script).unwrap();

    let output = eggbau::cli::run([
        "eggbau".to_owned(),
        "script".to_owned(),
        "prove".to_owned(),
        CONVERSION_FIXTURE.to_owned(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--script".to_owned(),
        script_path.to_string_lossy().into_owned(),
        "--format".to_owned(),
        "explicit".to_owned(),
    ])
    .unwrap();

    assert!(output.contains("target\n------\n"));
    assert!(output.contains("x := $ x $"));
}

#[test]
fn script_prove_supports_implicit_format() {
    let script = emit_target_script();
    let script_path = temp_path("implicit.egg");
    std::fs::write(&script_path, script).unwrap();

    let output = eggbau::cli::run([
        "eggbau".to_owned(),
        "script".to_owned(),
        "prove".to_owned(),
        CONVERSION_FIXTURE.to_owned(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--script".to_owned(),
        script_path.to_string_lossy().into_owned(),
        "--format".to_owned(),
        "implicit".to_owned(),
    ])
    .unwrap();

    assert!(output.contains("target\n------\n"));
    assert!(output.contains("by f_id []"));
    assert!(!output.contains(":="));
}

#[test]
fn script_prove_rejects_unreconstructible_edited_script() {
    let script = emit_target_script().replace(":name \"f_id\"", ":name \"unknown_rule\"");
    let script_path = temp_path("bad-rule.egg");
    std::fs::write(&script_path, script).unwrap();

    let err = eggbau::cli::run([
        "eggbau".to_owned(),
        "script".to_owned(),
        "prove".to_owned(),
        CONVERSION_FIXTURE.to_owned(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--script".to_owned(),
        script_path.to_string_lossy().into_owned(),
    ])
    .unwrap_err();

    assert!(err.to_string().contains("egglog rule"));
    assert!(err.to_string().contains("unknown_rule"));
}

#[test]
fn script_prove_matches_main_prove_for_simple_theorem() {
    let script = emit_target_script();
    let script_path = temp_path("equivalent.egg");
    std::fs::write(&script_path, script).unwrap();
    let main_output =
        eggbau::cli::run(["eggbau", "prove", CONVERSION_FIXTURE, "--theorem", "target"]).unwrap();

    let script_output = eggbau::cli::run([
        "eggbau".to_owned(),
        "script".to_owned(),
        "prove".to_owned(),
        CONVERSION_FIXTURE.to_owned(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--script".to_owned(),
        script_path.to_string_lossy().into_owned(),
    ])
    .unwrap();

    assert_eq!(script_output, main_output);
}

fn emit_target_script() -> String {
    eggbau::cli::run([
        "eggbau",
        "script",
        "emit",
        CONVERSION_FIXTURE,
        "--theorem",
        "target",
    ])
    .unwrap()
}

fn temp_path(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli_script_prove");
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(format!("{}_{}", std::process::id(), name))
}
