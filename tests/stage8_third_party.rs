use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const LEIBNIZ_SUM_RULE_CORE_INPUT: &str = r#"
delimiter $ ( ) $;
sort real;
provable sort wff;
term eq (x y: real): wff;
term add (x y: real): real;
term sub (x y: real): real;
term div (x y: real): real;
term lim (x: real): real;
--| @relation real eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: real): $ eq x x $;
axiom eq_trans (x y z: real): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: real): $ eq x y $ > $ eq y x $;
--| @congr
axiom add_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (add a c) (add b d) $;
--| @congr
axiom sub_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (sub a c) (sub b d) $;
--| @congr
axiom div_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (div a c) (div b d) $;
--| @congr
axiom lim_congr (a b: real): $ eq a b $ > $ eq (lim a) (lim b) $;
--| @saturation ltr
axiom sub_add (a b c d: real):
  $ eq (sub (add a b) (add c d)) (add (sub a c) (sub b d)) $;
--| @saturation ltr
axiom div_add (a b c: real):
  $ eq (div (add a b) c) (add (div a c) (div b c)) $;
--| @saturation ltr
axiom lim_add (a b: real):
  $ eq (lim (add a b)) (add (lim a) (lim b)) $;
theorem target (f g df dg fh gh h: real):
  $ eq (lim (div (sub fh f) h)) df $ >
  $ eq (lim (div (sub gh g) h)) dg $ >
  $ eq (lim (div (sub (add fh gh) (add f g)) h)) (add df dg) $;
"#;

const LEIBNIZ_CONST_MUL_CORE_INPUT: &str = r#"
delimiter $ ( ) $;
sort real;
provable sort wff;
term eq (x y: real): wff;
term const (x: real): real;
term mul (x y: real): real;
term sub (x y: real): real;
term div (x y: real): real;
term lim (x: real): real;
--| @relation real eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: real): $ eq x x $;
axiom eq_trans (x y z: real): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: real): $ eq x y $ > $ eq y x $;
--| @congr
axiom const_congr (a b: real): $ eq a b $ > $ eq (const a) (const b) $;
--| @congr
axiom mul_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (mul a c) (mul b d) $;
--| @congr
axiom sub_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (sub a c) (sub b d) $;
--| @congr
axiom div_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (div a c) (div b d) $;
--| @congr
axiom lim_congr (a b: real): $ eq a b $ > $ eq (lim a) (lim b) $;
--| @saturation ltr
axiom mul_sub (a b c: real):
  $ eq (sub (mul a b) (mul a c)) (mul a (sub b c)) $;
--| @saturation ltr
axiom div_mul (a b c: real):
  $ eq (div (mul a b) c) (mul a (div b c)) $;
--| @saturation ltr
axiom lim_mul (a b: real):
  $ eq (lim (mul a b)) (mul (lim a) (lim b)) $;
--| @saturation ltr
axiom lim_const (a: real): $ eq (lim (const a)) a $;
theorem target (c f df fh h: real):
  $ eq (lim (div (sub fh f) h)) df $ >
  $ eq
      (lim (div (sub (mul (const c) fh) (mul (const c) f)) h))
      (mul c df) $;
"#;

const LEIBNIZ_PRODUCT_BODY_CORE_INPUT: &str = r#"
delimiter $ ( ) $;
sort real;
provable sort wff;
term eq (x y: real): wff;
term add (x y: real): real;
term sub (x y: real): real;
term mul (x y: real): real;
term div (x y: real): real;
--| @relation real eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: real): $ eq x x $;
axiom eq_trans (x y z: real): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: real): $ eq x y $ > $ eq y x $;
--| @congr
axiom add_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (add a c) (add b d) $;
--| @congr
axiom sub_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (sub a c) (sub b d) $;
--| @congr
axiom mul_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (mul a c) (mul b d) $;
--| @congr
axiom div_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (div a c) (div b d) $;
--| @saturation ltr
axiom factor (a b c d: real):
  $ eq (sub (mul a b) (mul c d))
       (add (mul a (sub b d)) (mul d (sub a c))) $;
--| @saturation ltr
axiom div_add (a b c: real):
  $ eq (div (add a b) c) (add (div a c) (div b c)) $;
--| @saturation ltr
axiom div_mul (a b c: real):
  $ eq (div (mul a b) c) (mul a (div b c)) $;
theorem target (f g fh gh h: real):
  $ eq
      (div (sub (mul fh gh) (mul f g)) h)
      (add (mul fh (div (sub gh g) h))
           (mul g (div (sub fh f) h))) $;
"#;

const LEIBNIZ_PRODUCT_LIMIT_CORE_INPUT: &str = r#"
delimiter $ ( ) $;
sort real;
provable sort wff;
term eq (x y: real): wff;
term add (x y: real): real;
term sub (x y: real): real;
term mul (x y: real): real;
term div (x y: real): real;
term lim (x: real): real;
--| @relation real eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: real): $ eq x x $;
axiom eq_trans (x y z: real): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: real): $ eq x y $ > $ eq y x $;
--| @congr
axiom add_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (add a c) (add b d) $;
--| @congr
axiom sub_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (sub a c) (sub b d) $;
--| @congr
axiom mul_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (mul a c) (mul b d) $;
--| @congr
axiom div_congr (a b c d: real):
  $ eq a b $ > $ eq c d $ > $ eq (div a c) (div b d) $;
--| @congr
axiom lim_congr (a b: real): $ eq a b $ > $ eq (lim a) (lim b) $;
--| @saturation ltr
axiom factor (a b c d: real):
  $ eq (sub (mul a b) (mul c d))
       (add (mul a (sub b d)) (mul d (sub a c))) $;
--| @saturation ltr
axiom div_add (a b c: real):
  $ eq (div (add a b) c) (add (div a c) (div b c)) $;
--| @saturation ltr
axiom div_mul (a b c: real):
  $ eq (div (mul a b) c) (mul a (div b c)) $;
--| @saturation ltr
axiom lim_add (a b: real):
  $ eq (lim (add a b)) (add (lim a) (lim b)) $;
--| @saturation ltr
axiom lim_mul (a b: real):
  $ eq (lim (mul a b)) (mul (lim a) (lim b)) $;
theorem target (f g fh gh h: real):
  $ eq
      (lim (div (sub (mul fh gh) (mul f g)) h))
      (add
        (mul (lim fh) (lim (div (sub gh g) h)))
        (mul (lim g) (lim (div (sub fh f) h)))) $;
"#;

const ACUI_ANNOTATED_CTX_INPUT: &str = r#"
delimiter $ ( ) $;
sort ctx;
provable sort wff;
term ctx_eq (x y: ctx): wff;
term emp: ctx;
--| @acui ctx_assoc ctx_comm emp ctx_idem
term join (x y: ctx): ctx;
--| @relation ctx ctx_eq ctx_refl ctx_trans ctx_sym _
axiom ctx_refl (x: ctx): $ ctx_eq x x $;
axiom ctx_trans (x y z: ctx):
  $ ctx_eq x y $ > $ ctx_eq y z $ > $ ctx_eq x z $;
axiom ctx_sym (x y: ctx): $ ctx_eq x y $ > $ ctx_eq y x $;
axiom ctx_assoc (x y z: ctx):
  $ ctx_eq (join (join x y) z) (join x (join y z)) $;
axiom ctx_comm (x y: ctx): $ ctx_eq (join x y) (join y x) $;
--| @saturation ltr
axiom ctx_idem (x: ctx): $ ctx_eq (join x x) x $;
axiom ctx_unit (x: ctx): $ ctx_eq (join emp x) x $;
--| @congr
axiom join_congr (x y z w: ctx):
  $ ctx_eq x y $ > $ ctx_eq z w $ > $ ctx_eq (join x z) (join y w) $;
theorem target (x: ctx): $ ctx_eq (join (join x x) x) x $;
"#;

fn prove_auf(input: &str) -> String {
    eggbau::prove_theorem(
        input,
        EggbauConfig {
            theorem: Some("target".to_owned()),
            output_mode: OutputMode::Fragment,
            allow_synthetic_discovery: false,
        },
    )
    .unwrap()
    .auf
}

#[test]
fn proves_leibniz_sum_rule_core() {
    let auf = prove_auf(LEIBNIZ_SUM_RULE_CORE_INPUT);

    assert!(auf.contains("by sub_add"));
    assert!(auf.contains("by div_add"));
    assert!(auf.contains("by lim_add"));
    assert!(auf.contains("by add_congr"));
    assert!(auf.contains("["));
    verify_with_external_tools("stage8_leibniz_sum", LEIBNIZ_SUM_RULE_CORE_INPUT, &auf);
}

#[test]
fn proves_leibniz_constant_multiple_rule_core() {
    let auf = prove_auf(LEIBNIZ_CONST_MUL_CORE_INPUT);

    assert!(auf.contains("by mul_sub"));
    assert!(auf.contains("by div_mul"));
    assert!(auf.contains("by lim_mul"));
    assert!(auf.contains("by lim_const"));
    verify_with_external_tools(
        "stage8_leibniz_const_mul",
        LEIBNIZ_CONST_MUL_CORE_INPUT,
        &auf,
    );
}

#[test]
fn proves_leibniz_product_rule_body_core() {
    let auf = prove_auf(LEIBNIZ_PRODUCT_BODY_CORE_INPUT);

    assert!(auf.contains("by factor"));
    assert!(auf.contains("by div_add"));
    assert!(auf.contains("by div_mul"));
    assert!(auf.contains("by add_congr"));
    verify_with_external_tools(
        "stage8_leibniz_product_body",
        LEIBNIZ_PRODUCT_BODY_CORE_INPUT,
        &auf,
    );
}

#[test]
fn proves_leibniz_product_rule_limit_distribution_core() {
    let auf = prove_auf(LEIBNIZ_PRODUCT_LIMIT_CORE_INPUT);

    assert!(auf.contains("by lim_add"));
    assert!(auf.contains("by lim_mul"));
    assert!(auf.contains("by lim_congr"));
    assert!(auf.contains("by eq_refl"));
    assert!(auf.contains("$ eq (lim (div (mul fh (sub gh g)) h))"));
    verify_with_external_tools(
        "stage8_leibniz_product_limit",
        LEIBNIZ_PRODUCT_LIMIT_CORE_INPUT,
        &auf,
    );
}

#[test]
fn proves_theory_with_acui_term_annotation() {
    let auf = prove_auf(ACUI_ANNOTATED_CTX_INPUT);

    assert!(auf.contains("by ctx_idem"));
    assert!(auf.contains("by join_congr"));
    verify_with_external_tools("stage8_acui_annotated", ACUI_ANNOTATED_CTX_INPUT, &auf);
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
