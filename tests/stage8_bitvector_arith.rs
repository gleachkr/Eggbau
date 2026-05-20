use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const AXIOMS: &str = r#"
delimiter $ ( ) $;
sort bv;
provable sort wff;
term bv_eq (x y: bv): wff;
term bv0: bv;
term bv_ones: bv;
term bv_add (x y: bv): bv;
term bv_neg (x: bv): bv;
term bv_sub (x y: bv): bv;
term bv_and (x y: bv): bv;
term bv_or (x y: bv): bv;
term bv_xor (x y: bv): bv;
term bv_not (x: bv): bv;
term bv_shl_one (x: bv): bv;

--| @relation bv bv_eq bv_eq_refl bv_eq_trans bv_eq_sym _
axiom bv_eq_refl (x: bv): $ bv_eq x x $;
axiom bv_eq_trans (x y z: bv):
  $ bv_eq x y $ > $ bv_eq y z $ > $ bv_eq x z $;
axiom bv_eq_sym (x y: bv): $ bv_eq x y $ > $ bv_eq y x $;

--| @congr
axiom bv_add_congr (a b c d: bv):
  $ bv_eq a b $ > $ bv_eq c d $ > $ bv_eq (bv_add a c) (bv_add b d) $;
--| @congr
axiom bv_neg_congr (a b: bv):
  $ bv_eq a b $ > $ bv_eq (bv_neg a) (bv_neg b) $;
--| @congr
axiom bv_sub_congr (a b c d: bv):
  $ bv_eq a b $ > $ bv_eq c d $ > $ bv_eq (bv_sub a c) (bv_sub b d) $;
--| @congr
axiom bv_and_congr (a b c d: bv):
  $ bv_eq a b $ > $ bv_eq c d $ > $ bv_eq (bv_and a c) (bv_and b d) $;
--| @congr
axiom bv_or_congr (a b c d: bv):
  $ bv_eq a b $ > $ bv_eq c d $ > $ bv_eq (bv_or a c) (bv_or b d) $;
--| @congr
axiom bv_xor_congr (a b c d: bv):
  $ bv_eq a b $ > $ bv_eq c d $ > $ bv_eq (bv_xor a c) (bv_xor b d) $;
--| @congr
axiom bv_not_congr (a b: bv):
  $ bv_eq a b $ > $ bv_eq (bv_not a) (bv_not b) $;
--| @congr
axiom bv_shl_one_congr (a b: bv):
  $ bv_eq a b $ > $ bv_eq (bv_shl_one a) (bv_shl_one b) $;

--| @saturation ltr
axiom bv_add_comm (x y: bv): $ bv_eq (bv_add x y) (bv_add y x) $;
--| @saturation ltr
axiom bv_add_assoc (x y z: bv):
  $ bv_eq (bv_add (bv_add x y) z) (bv_add x (bv_add y z)) $;
--| @saturation ltr
axiom bv_add_zero (x: bv): $ bv_eq (bv_add x bv0) x $;
--| @saturation ltr
axiom bv_add_neg (x: bv): $ bv_eq (bv_add x (bv_neg x)) bv0 $;
--| @saturation ltr
axiom bv_neg_neg (x: bv): $ bv_eq (bv_neg (bv_neg x)) x $;
--| @saturation ltr
axiom bv_neg_zero: $ bv_eq (bv_neg bv0) bv0 $;
--| @saturation ltr
axiom bv_sub_def (x y: bv):
  $ bv_eq (bv_sub x y) (bv_add x (bv_neg y)) $;

--| @saturation ltr
axiom bv_xor_comm (x y: bv): $ bv_eq (bv_xor x y) (bv_xor y x) $;
--| @saturation ltr
axiom bv_xor_assoc (x y z: bv):
  $ bv_eq (bv_xor (bv_xor x y) z) (bv_xor x (bv_xor y z)) $;
--| @saturation ltr
axiom bv_xor_zero (x: bv): $ bv_eq (bv_xor x bv0) x $;
--| @saturation ltr
axiom bv_xor_self (x: bv): $ bv_eq (bv_xor x x) bv0 $;

--| @saturation ltr
axiom bv_and_comm (x y: bv): $ bv_eq (bv_and x y) (bv_and y x) $;
--| @saturation ltr
axiom bv_and_assoc (x y z: bv):
  $ bv_eq (bv_and (bv_and x y) z) (bv_and x (bv_and y z)) $;
--| @saturation ltr
axiom bv_and_idem (x: bv): $ bv_eq (bv_and x x) x $;
--| @saturation ltr
axiom bv_and_zero (x: bv): $ bv_eq (bv_and x bv0) bv0 $;
--| @saturation ltr
axiom bv_and_ones (x: bv): $ bv_eq (bv_and x bv_ones) x $;
--| @saturation ltr
axiom bv_or_comm (x y: bv): $ bv_eq (bv_or x y) (bv_or y x) $;
--| @saturation ltr
axiom bv_or_assoc (x y z: bv):
  $ bv_eq (bv_or (bv_or x y) z) (bv_or x (bv_or y z)) $;
--| @saturation ltr
axiom bv_or_idem (x: bv): $ bv_eq (bv_or x x) x $;
--| @saturation ltr
axiom bv_or_zero (x: bv): $ bv_eq (bv_or x bv0) x $;
--| @saturation ltr
axiom bv_or_ones (x: bv): $ bv_eq (bv_or x bv_ones) bv_ones $;

--| @saturation ltr
axiom bv_not_not (x: bv): $ bv_eq (bv_not (bv_not x)) x $;
--| @saturation ltr
axiom bv_not_zero: $ bv_eq (bv_not bv0) bv_ones $;
--| @saturation ltr
axiom bv_not_ones: $ bv_eq (bv_not bv_ones) bv0 $;

--| @saturation ltr
axiom bv_shl_one_def (x: bv): $ bv_eq (bv_shl_one x) (bv_add x x) $;
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

fn verify(name: &str, theorem_decl: &str, auf: &str) {
    let mm0 = format!("{AXIOMS}{theorem_decl}");
    verify_with_external_tools(name, &mm0, auf);
}

#[test]
fn proves_sub_self_via_sub_def_and_add_neg() {
    let decl = "\ntheorem target (x: bv): $ bv_eq (bv_sub x x) bv0 $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_sub_def"));
    assert!(auf.contains("by bv_add_neg"));
    verify("stage8_bv_sub_self", decl, &auf);
}

#[test]
fn proves_sub_zero_via_neg_zero_and_add_zero() {
    let decl = "\ntheorem target (x: bv): $ bv_eq (bv_sub x bv0) x $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_sub_def"));
    assert!(auf.contains("by bv_neg_zero"));
    assert!(auf.contains("by bv_add_zero"));
    verify("stage8_bv_sub_zero", decl, &auf);
}

#[test]
fn proves_add_sub_cancel() {
    let decl = "\ntheorem target (x y: bv): $ bv_eq (bv_add x (bv_sub y x)) y $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_sub_def"));
    assert!(auf.contains("by bv_add_assoc") || auf.contains("by bv_add_comm"));
    verify("stage8_bv_add_sub_cancel", decl, &auf);
}

#[test]
fn proves_xor_cancel() {
    let decl = "\ntheorem target (x y: bv): $ bv_eq (bv_xor (bv_xor x y) y) x $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_xor_assoc"));
    assert!(auf.contains("by bv_xor_self"));
    assert!(auf.contains("by bv_xor_zero"));
    verify("stage8_bv_xor_cancel", decl, &auf);
}

#[test]
fn proves_xor_cancel_chain() {
    // (x XOR y) XOR (y XOR z) = x XOR z
    let decl = concat!(
        "\ntheorem target (x y z: bv):\n",
        "  $ bv_eq (bv_xor (bv_xor x y) (bv_xor y z)) (bv_xor x z) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_xor_assoc") || auf.contains("by bv_xor_comm"));
    assert!(auf.contains("by bv_xor_self"));
    verify("stage8_bv_xor_cancel_chain", decl, &auf);
}

#[test]
fn proves_shl_one_zero() {
    let decl = "\ntheorem target: $ bv_eq (bv_shl_one bv0) bv0 $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_shl_one_def"));
    assert!(auf.contains("by bv_add_zero"));
    verify("stage8_bv_shl_one_zero", decl, &auf);
}

#[test]
fn proves_mask_with_complement() {
    // (x AND ones) OR (x AND 0) = x  via and_ones, and_zero, or_zero
    let decl = concat!(
        "\ntheorem target (x: bv):\n",
        "  $ bv_eq (bv_or (bv_and x bv_ones) (bv_and x bv0)) x $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_and_ones"));
    assert!(auf.contains("by bv_and_zero"));
    assert!(auf.contains("by bv_or_zero"));
    verify("stage8_bv_mask_with_complement", decl, &auf);
}

#[test]
fn proves_neg_of_xor_self() {
    // neg (x XOR x) = neg 0 = 0
    let decl = "\ntheorem target (x: bv): $ bv_eq (bv_neg (bv_xor x x)) bv0 $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_xor_self"));
    assert!(auf.contains("by bv_neg_zero"));
    verify("stage8_bv_neg_xor_self", decl, &auf);
}

#[test]
fn proves_double_negation_under_shift() {
    // neg(neg(shl_one x)) = shl_one x
    let decl = concat!(
        "\ntheorem target (x: bv):\n",
        "  $ bv_eq (bv_neg (bv_neg (bv_shl_one x))) (bv_shl_one x) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by bv_neg_neg"));
    verify("stage8_bv_neg_neg_shl", decl, &auf);
}

#[test]
fn fixture_file_axioms_match_embedded_axioms() {
    let fixture = include_str!("fixtures/stage8_bitvector_arith.mm0");
    for axiom_name in [
        "bv_add_comm",
        "bv_xor_self",
        "bv_sub_def",
        "bv_and_ones",
        "bv_shl_one_def",
        "bv_not_zero",
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
