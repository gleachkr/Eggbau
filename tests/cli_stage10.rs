use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const FIXTURE: &str = "tests/fixtures/cli_e2e.mm0";
const THEOREM: &str = "target";

#[test]
fn documented_main_prove_workflow_verifies_end_to_end() {
    let Some(tools) = external_tools() else {
        return;
    };
    let dir = temp_path("main_prove_workflow");
    fs::create_dir_all(&dir).unwrap();
    let auf = dir.join("generated.auf");
    let mmb = dir.join("generated.mmb");

    let prove = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args(["prove", FIXTURE, "--theorem", THEOREM, "--out"])
        .arg(&auf)
        .output()
        .unwrap();
    assert_success("eggbau prove", &prove);
    assert!(prove.stdout.is_empty());
    assert!(fs::read_to_string(&auf).unwrap().contains("by f_id"));

    verify_with_external_tools(&tools, Path::new(FIXTURE), &auf, &mmb);
}

#[test]
fn documented_script_workflow_verifies_end_to_end() {
    let Some(tools) = external_tools() else {
        return;
    };
    let dir = temp_path("script_workflow");
    fs::create_dir_all(&dir).unwrap();
    let script = dir.join("target.egg");
    let auf = dir.join("generated.auf");
    let mmb = dir.join("generated.mmb");

    let emit = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args(["script", "emit", FIXTURE, "--theorem", THEOREM])
        .output()
        .unwrap();
    assert_success("eggbau script emit", &emit);
    fs::write(&script, &emit.stdout).unwrap();
    let script_text = String::from_utf8(emit.stdout).unwrap();
    assert!(script_text.contains("script kind: proof-problem"));
    assert!(script_text.contains(":name \"f_id\""));

    let prove = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args(["script", "prove", FIXTURE, "--theorem", THEOREM, "--script"])
        .arg(&script)
        .arg("--out")
        .arg(&auf)
        .output()
        .unwrap();
    assert_success("eggbau script prove", &prove);
    assert!(fs::read_to_string(&auf).unwrap().contains("by f_id"));

    verify_with_external_tools(&tools, Path::new(FIXTURE), &auf, &mmb);
}

fn verify_with_external_tools(tools: &ExternalTools, mm0: &Path, auf: &Path, mmb: &Path) {
    let abc = Command::new(&tools.abc)
        .arg("compile")
        .arg(mm0)
        .arg(auf)
        .arg(mmb)
        .output()
        .unwrap();
    assert_success("abc compile", &abc);

    let mm0_zig = Command::new(&tools.mm0_zig)
        .arg(mmb)
        .stdin(fs::File::open(mm0).unwrap())
        .output()
        .unwrap();
    assert_success("mm0-zig", &mm0_zig);
}

fn assert_success(name: &str, output: &std::process::Output) {
    assert!(
        output.status.success(),
        "{name} failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

struct ExternalTools {
    abc: PathBuf,
    mm0_zig: PathBuf,
}

fn external_tools() -> Option<ExternalTools> {
    let abc = configured_tool("EGGBAU_ABC", "abc")?;
    let mm0_zig = configured_tool("EGGBAU_MM0_ZIG", "mm0-zig")?;
    Some(ExternalTools { abc, mm0_zig })
}

fn configured_tool(env_name: &str, fallback: &str) -> Option<PathBuf> {
    if let Some(value) = nonempty_env(env_name) {
        return Some(PathBuf::from(value));
    }
    if command_available(fallback) {
        return Some(PathBuf::from(fallback));
    }
    eprintln!("skipping CLI-10 e2e tests: set {env_name} or put {fallback} on PATH");
    None
}

fn nonempty_env(name: &str) -> Option<String> {
    std::env::var(name).ok().filter(|value| !value.is_empty())
}

fn command_available(name: &str) -> bool {
    Command::new(name)
        .arg("--help")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|_| true)
        .unwrap_or(false)
}

fn temp_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("target/cli_stage10")
        .join(format!("{}_{}", std::process::id(), name))
}
