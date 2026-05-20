use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const AXIOMS: &str = r#"
delimiter $ ( ) $;
sort bool;
provable sort wff;
term eq (x y: bool): wff;
term top: bool;
term bot: bool;
term and (x y: bool): bool;
term or (x y: bool): bool;
term not (x: bool): bool;

--| @relation bool eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: bool): $ eq x x $;
axiom eq_trans (x y z: bool): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: bool): $ eq x y $ > $ eq y x $;

--| @congr
axiom and_congr (a b c d: bool):
  $ eq a b $ > $ eq c d $ > $ eq (and a c) (and b d) $;
--| @congr
axiom or_congr (a b c d: bool):
  $ eq a b $ > $ eq c d $ > $ eq (or a c) (or b d) $;
--| @congr
axiom not_congr (a b: bool): $ eq a b $ > $ eq (not a) (not b) $;

-- Lattice axioms (and)
--| @saturation ltr
axiom and_comm (x y: bool): $ eq (and x y) (and y x) $;
--| @saturation ltr
axiom and_assoc (x y z: bool):
  $ eq (and (and x y) z) (and x (and y z)) $;
--| @saturation ltr
axiom and_idem (x: bool): $ eq (and x x) x $;
--| @saturation ltr
axiom and_top (x: bool): $ eq (and top x) x $;
--| @saturation ltr
axiom and_bot (x: bool): $ eq (and bot x) bot $;

-- Lattice axioms (or)
--| @saturation ltr
axiom or_comm (x y: bool): $ eq (or x y) (or y x) $;
--| @saturation ltr
axiom or_assoc (x y z: bool):
  $ eq (or (or x y) z) (or x (or y z)) $;
--| @saturation ltr
axiom or_idem (x: bool): $ eq (or x x) x $;
--| @saturation ltr
axiom or_bot (x: bool): $ eq (or bot x) x $;
--| @saturation ltr
axiom or_top (x: bool): $ eq (or top x) top $;

-- Absorption laws
--| @saturation ltr
axiom and_absorb (x y: bool): $ eq (and x (or x y)) x $;
--| @saturation ltr
axiom or_absorb (x y: bool): $ eq (or x (and x y)) x $;

-- Complementation
--| @saturation ltr
axiom and_compl (x: bool): $ eq (and x (not x)) bot $;
--| @saturation ltr
axiom or_compl (x: bool): $ eq (or x (not x)) top $;

-- Negation laws
--| @saturation ltr
axiom not_not (x: bool): $ eq (not (not x)) x $;
--| @saturation ltr
axiom not_top: $ eq (not top) bot $;
--| @saturation ltr
axiom not_bot: $ eq (not bot) top $;
--| @saturation ltr
axiom demorgan_and (x y: bool):
  $ eq (not (and x y)) (or (not x) (not y)) $;
--| @saturation ltr
axiom demorgan_or (x y: bool):
  $ eq (not (or x y)) (and (not x) (not y)) $;

-- Distributivity (factoring direction only: keeps the e-graph small).
--| @saturation ltr
axiom or_factor (x y z: bool):
  $ eq (or (and x y) (and x z)) (and x (or y z)) $;
--| @saturation ltr
axiom and_factor (x y z: bool):
  $ eq (and (or x y) (or x z)) (or x (and y z)) $;
"#;

fn prove_auf(theorem_decl: &str) -> String {
    let input = format!("{AXIOMS}{theorem_decl}");
    eggbau::prove_theorem(
        &input,
        EggbauConfig {
            theorem: Some("target".to_owned()),
            output_mode: OutputMode::Fragment,
            allow_synthetic_discovery: false,
        },
    )
    .unwrap()
    .auf
}

fn prove_implicit_auf(name: &str, theorem_decl: &str) -> String {
    let dir = temp_test_dir(&format!("{name}_emit"));
    fs::create_dir_all(&dir).unwrap();
    let mm0_path = dir.join("input.mm0");
    fs::write(&mm0_path, format!("{AXIOMS}{theorem_decl}")).unwrap();

    eggbau::cli::run([
        "eggbau".to_owned(),
        "prove".to_owned(),
        mm0_path.display().to_string(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--format".to_owned(),
        "implicit".to_owned(),
    ])
    .unwrap()
}

fn verify(name: &str, theorem_decl: &str, auf: &str) {
    let mm0 = format!("{AXIOMS}{theorem_decl}");
    verify_with_external_tools(name, &mm0, auf);
}

#[test]
fn proves_and_top_via_commutativity() {
    let decl = "\ntheorem target (x: bool): $ eq (and x top) x $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by and_top"));
    assert!(auf.contains("by and_comm"));
    verify("stage8_bool_and_top", decl, &auf);
}

#[test]
fn proves_or_annihilation_via_commutativity() {
    let decl = "\ntheorem target (x: bool): $ eq (or x top) top $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by or_top"));
    assert!(auf.contains("by or_comm"));
    verify("stage8_bool_or_top", decl, &auf);
}

#[test]
fn proves_double_negation() {
    let decl = "\ntheorem target (x: bool): $ eq (not (not x)) x $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by not_not"));
    verify("stage8_bool_not_not", decl, &auf);
}

#[test]
fn proves_de_morgan_for_conjunction() {
    let decl = "\ntheorem target (x y: bool):\n  $ eq (not (and x y)) (or (not x) (not y)) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by demorgan_and"));
    verify("stage8_bool_demorgan_and", decl, &auf);
}

#[test]
fn proves_absorption_law() {
    let decl = "\ntheorem target (x y: bool): $ eq (or x (and x y)) x $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by or_absorb"));
    verify("stage8_bool_absorb", decl, &auf);
}

#[test]
fn proves_consensus_via_or_factor() {
    // (x ∧ y) ∨ (x ∧ ¬y) = x ∧ (y ∨ ¬y) = x ∧ ⊤ = x
    let decl = concat!(
        "\ntheorem target (x y: bool):\n",
        "  $ eq (or (and x y) (and x (not y))) x $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by or_factor"));
    assert!(auf.contains("by or_compl"));
    verify("stage8_bool_consensus_or_factor", decl, &auf);
}

#[test]
fn proves_consensus_via_and_factor() {
    // (x ∨ y) ∧ (x ∨ ¬y) = x ∨ (y ∧ ¬y) = x ∨ ⊥ = x
    let decl = concat!(
        "\ntheorem target (x y: bool):\n",
        "  $ eq (and (or x y) (or x (not y))) x $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by and_factor"));
    assert!(auf.contains("by and_compl"));
    verify("stage8_bool_consensus_and_factor", decl, &auf);
}

#[test]
fn proves_chained_de_morgan() {
    // ¬(x ∨ (y ∧ z)) = ¬x ∧ (¬y ∨ ¬z)
    let decl = concat!(
        "\ntheorem target (x y z: bool):\n",
        "  $ eq (not (or x (and y z))) (and (not x) (or (not y) (not z))) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by demorgan_or"));
    assert!(auf.contains("by demorgan_and"));
    verify("stage8_bool_chained_demorgan", decl, &auf);
}

#[test]
fn proves_shannon_expansion() {
    // x = (y ∧ x) ∨ (¬y ∧ x)
    // collapse to (x ∧ y) ∨ (x ∧ ¬y) via commutativity, then or_factor + or_compl + and_top.
    let decl = concat!(
        "\ntheorem target (x y: bool):\n",
        "  $ eq x (or (and y x) (and (not y) x)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by or_factor"));
    assert!(auf.contains("by or_compl"));
    verify("stage8_bool_shannon", decl, &auf);
}

#[test]
fn verifies_implicit_chained_de_morgan() {
    let decl = concat!(
        "\ntheorem target (x y z: bool):\n",
        "  $ eq (not (or x (and y z))) (and (not x) (or (not y) (not z))) $;\n",
    );
    let auf = prove_implicit_auf("stage8_bool_implicit_demorgan", decl);
    assert!(auf.contains("by demorgan_or"));
    assert!(auf.contains("by demorgan_and"));
    assert!(!auf.contains(":="));
    verify("stage8_bool_implicit_demorgan", decl, &auf);
}

#[test]
fn verifies_implicit_shannon_expansion() {
    let decl = concat!(
        "\ntheorem target (x y: bool):\n",
        "  $ eq x (or (and y x) (and (not y) x)) $;\n",
    );
    let auf = prove_implicit_auf("stage8_bool_implicit_shannon", decl);
    assert!(auf.contains("by or_factor"));
    assert!(auf.contains("by or_compl"));
    assert!(!auf.contains(":="));
    verify("stage8_bool_implicit_shannon", decl, &auf);
}

#[test]
fn proves_complement_of_compound() {
    // ¬(x ∨ y) ∧ (x ∨ y) = ⊥ — generic complement instance on a compound expression.
    let decl = concat!(
        "\ntheorem target (x y: bool):\n",
        "  $ eq (and (not (or x y)) (or x y)) bot $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by and_compl") || auf.contains("by and_comm"));
    verify("stage8_bool_compound_compl", decl, &auf);
}

fn verify_with_external_tools(name: &str, mm0: &str, auf: &str) {
    if !tool_available("abc") || !tool_available("mm0-zig") {
        eprintln!("skipping {name}: abc or mm0-zig is not on PATH");
        return;
    }

    let dir = temp_test_dir(name);
    fs::create_dir_all(&dir).unwrap();
    let mm0_path = dir.join("input.mm0");
    let auf_path = dir.join("generated.auf");
    let mmb_path = dir.join("generated.mmb");
    fs::write(&mm0_path, mm0).unwrap();
    fs::write(&auf_path, auf).unwrap();

    let abc = Command::new("abc")
        .arg("compile")
        .arg(&mm0_path)
        .arg(&auf_path)
        .arg(&mmb_path)
        .output()
        .unwrap();
    assert!(
        abc.status.success(),
        "abc failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&abc.stdout),
        String::from_utf8_lossy(&abc.stderr)
    );

    let mm0_zig = Command::new("mm0-zig")
        .arg(&mmb_path)
        .stdin(fs::File::open(&mm0_path).unwrap())
        .output()
        .unwrap();
    assert!(
        mm0_zig.status.success(),
        "mm0-zig failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&mm0_zig.stdout),
        String::from_utf8_lossy(&mm0_zig.stderr)
    );
}

fn tool_available(name: &str) -> bool {
    Command::new(name)
        .arg("--help")
        .output()
        .map(|_| true)
        .unwrap_or(false)
}

fn temp_test_dir(name: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "eggbau_{}_{}_{}",
        name,
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    path
}
