use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const AXIOMS: &str = r#"
delimiter $ ( ) $;
sort regex;
provable sort wff;
term eq (x y: regex): wff;
term rzero: regex;
term rone: regex;
term plus (x y: regex): regex;
term seq (x y: regex): regex;
term star (x: regex): regex;

--| @relation regex eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: regex): $ eq x x $;
axiom eq_trans (x y z: regex): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: regex): $ eq x y $ > $ eq y x $;

--| @congr
axiom plus_congr (a b c d: regex):
  $ eq a b $ > $ eq c d $ > $ eq (plus a c) (plus b d) $;
--| @congr
axiom seq_congr (a b c d: regex):
  $ eq a b $ > $ eq c d $ > $ eq (seq a c) (seq b d) $;
--| @congr
axiom star_congr (a b: regex): $ eq a b $ > $ eq (star a) (star b) $;

-- + is idempotent, commutative, associative; rzero is the unit.
--| @saturation ltr
axiom plus_zero_l (x: regex): $ eq (plus rzero x) x $;
--| @saturation ltr
axiom plus_zero_r (x: regex): $ eq (plus x rzero) x $;
--| @saturation ltr
axiom plus_comm (x y: regex): $ eq (plus x y) (plus y x) $;
--| @saturation ltr
axiom plus_assoc (x y z: regex):
  $ eq (plus (plus x y) z) (plus x (plus y z)) $;
--| @saturation ltr
axiom plus_idem (x: regex): $ eq (plus x x) x $;

-- · is a monoid with rone as unit and rzero as annihilator.
--| @saturation ltr
axiom seq_one_l (x: regex): $ eq (seq rone x) x $;
--| @saturation ltr
axiom seq_one_r (x: regex): $ eq (seq x rone) x $;
--| @saturation ltr
axiom seq_zero_l (x: regex): $ eq (seq rzero x) rzero $;
--| @saturation ltr
axiom seq_zero_r (x: regex): $ eq (seq x rzero) rzero $;
--| @saturation ltr
axiom seq_assoc (x y z: regex):
  $ eq (seq (seq x y) z) (seq x (seq y z)) $;

-- · distributes over +. Oriented in the factoring direction only — same
-- choice the boolean fixture makes for and/or, which keeps the e-graph
-- bounded while still letting both sides of a distributive equation be
-- normalised toward the same factored form.
--| @saturation ltr
axiom seq_dist_l (x y z: regex):
  $ eq (plus (seq x y) (seq x z)) (seq x (plus y z)) $;
--| @saturation ltr
axiom seq_dist_r (x y z: regex):
  $ eq (plus (seq x z) (seq y z)) (seq (plus x y) z) $;

-- Star: the equational fragment that is shrinking under ltr.
--| @saturation ltr
axiom star_zero: $ eq (star rzero) rone $;
--| @saturation ltr
axiom star_one: $ eq (star rone) rone $;
--| @saturation ltr
axiom star_star (x: regex): $ eq (star (star x)) (star x) $;
--| @saturation ltr
axiom star_seq_idem (x: regex):
  $ eq (seq (star x) (star x)) (star x) $;
--| @saturation ltr
axiom star_unfold_l (x: regex):
  $ eq (plus rone (seq x (star x))) (star x) $;
--| @saturation ltr
axiom star_unfold_r (x: regex):
  $ eq (plus rone (seq (star x) x)) (star x) $;
--| @saturation ltr
axiom one_plus_star (x: regex):
  $ eq (plus rone (star x)) (star x) $;
--| @saturation ltr
axiom one_plus_into_star (x: regex):
  $ eq (star (plus rone x)) (star x) $;
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
fn proves_star_of_zero_is_one() {
    let decl = "\ntheorem target: $ eq (star rzero) rone $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by star_zero"));
    verify("domain_kleene_star_zero", decl, &auf);
}

#[test]
fn proves_star_star_collapses() {
    let decl = "\ntheorem target (x: regex): $ eq (star (star x)) (star x) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by star_star"));
    verify("domain_kleene_star_star", decl, &auf);
}

#[test]
fn proves_star_self_concat_idempotent() {
    // x* · x* = x*  — the closure absorbs concatenation with itself.
    let decl = "\ntheorem target (x: regex): $ eq (seq (star x) (star x)) (star x) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by star_seq_idem"));
    verify("domain_kleene_star_seq_idem", decl, &auf);
}

#[test]
fn proves_one_plus_pattern_under_star() {
    // (1 + x)* = x*  — adding the empty word doesn't change the closure.
    let decl = "\ntheorem target (x: regex): $ eq (star (plus rone x)) (star x) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by one_plus_into_star"));
    verify("domain_kleene_one_plus_into_star", decl, &auf);
}

#[test]
fn proves_zero_extension_under_star() {
    // (0 + x)* = x*  — adding the empty language doesn't change the closure.
    let decl = "\ntheorem target (x: regex): $ eq (star (plus rzero x)) (star x) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by plus_zero_l") || auf.contains("by plus_zero_r"));
    verify("domain_kleene_zero_under_star", decl, &auf);
}

#[test]
fn proves_zero_kills_concat_chain() {
    // x · 0 · y = 0  — the empty language is absorbing under concatenation.
    let decl = concat!(
        "\ntheorem target (x y: regex):\n",
        "  $ eq (seq (seq x rzero) y) rzero $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by seq_zero_l") || auf.contains("by seq_zero_r"));
    verify("domain_kleene_zero_kills_chain", decl, &auf);
}

#[test]
fn proves_foil_distribution() {
    // (a + b) · (c + d) = a·c + a·d + b·c + b·d — full FOIL.
    let decl = concat!(
        "\ntheorem target (a b c d: regex):\n",
        "  $ eq (seq (plus a b) (plus c d))\n",
        "       (plus (plus (plus (seq a c) (seq a d)) (seq b c)) (seq b d)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by seq_dist_l") || auf.contains("by seq_dist_r"));
    verify("domain_kleene_foil", decl, &auf);
}

#[test]
fn proves_plus_idempotent_chain_collapses() {
    // (a + b) + (a + b) + 0 = a + b  — repeated alternations collapse.
    let decl = concat!(
        "\ntheorem target (a b: regex):\n",
        "  $ eq (plus (plus (plus a b) (plus a b)) rzero) (plus a b) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by plus_idem"));
    verify("domain_kleene_plus_idem_chain", decl, &auf);
}

#[test]
fn proves_compound_star_self_concat() {
    // (a + b)* · (a + b)* = (a + b)* — star_seq_idem on a compound expression.
    let decl = concat!(
        "\ntheorem target (a b: regex):\n",
        "  $ eq (seq (star (plus a b)) (star (plus a b))) (star (plus a b)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by star_seq_idem"));
    verify("domain_kleene_compound_star_self_concat", decl, &auf);
}

#[test]
fn proves_star_zero_acts_as_one_under_concat() {
    // 0* · x = x  — because 0* rewrites to 1 and 1 is the left unit of ·.
    let decl = "\ntheorem target (x: regex): $ eq (seq (star rzero) x) x $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by star_zero"));
    assert!(auf.contains("by seq_one_l"));
    verify("domain_kleene_star_zero_concat", decl, &auf);
}

#[test]
fn proves_one_plus_star_collapses() {
    // 1 + x* = x*  — the empty word is already in x*'s language.
    let decl = "\ntheorem target (x: regex): $ eq (plus rone (star x)) (star x) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by one_plus_star"));
    verify("domain_kleene_one_plus_star", decl, &auf);
}

#[test]
fn verifies_implicit_foil() {
    let decl = concat!(
        "\ntheorem target (a b c d: regex):\n",
        "  $ eq (seq (plus a b) (plus c d))\n",
        "       (plus (plus (plus (seq a c) (seq a d)) (seq b c)) (seq b d)) $;\n",
    );
    let auf = prove_implicit_auf("domain_kleene_implicit_foil", decl);
    assert!(auf.contains("by seq_dist_l") || auf.contains("by seq_dist_r"));
    assert!(!auf.contains(":="));
    verify("domain_kleene_implicit_foil", decl, &auf);
}

#[test]
fn fixture_file_axioms_match_embedded_axioms() {
    let fixture = include_str!("fixtures/domain_kleene.mm0");
    for axiom_name in [
        "plus_idem",
        "plus_comm",
        "seq_assoc",
        "seq_dist_l",
        "seq_dist_r",
        "star_zero",
        "star_star",
        "star_seq_idem",
        "star_unfold_l",
        "one_plus_into_star",
    ] {
        assert!(
            fixture.contains(axiom_name) && AXIOMS.contains(axiom_name),
            "expected fixture and embedded axioms to both mention {axiom_name}"
        );
    }
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
