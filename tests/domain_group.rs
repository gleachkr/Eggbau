use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const AXIOMS: &str = r#"
delimiter $ ( ) $;
sort G;
provable sort wff;
term eq (x y: G): wff;
term e: G;
term gmul (x y: G): G;
term ginv (x: G): G;

--| @relation G eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: G): $ eq x x $;
axiom eq_trans (x y z: G): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: G): $ eq x y $ > $ eq y x $;

--| @congr
axiom gmul_congr (a b c d: G):
  $ eq a b $ > $ eq c d $ > $ eq (gmul a c) (gmul b d) $;
--| @congr
axiom ginv_congr (a b: G): $ eq a b $ > $ eq (ginv a) (ginv b) $;

-- Group axioms.
--| @saturation ltr
axiom id_l (x: G): $ eq (gmul e x) x $;
--| @saturation ltr
axiom id_r (x: G): $ eq (gmul x e) x $;
--| @saturation ltr
axiom inv_l (x: G): $ eq (gmul (ginv x) x) e $;
--| @saturation ltr
axiom inv_r (x: G): $ eq (gmul x (ginv x)) e $;
-- `both` is needed because the group is non-commutative: without it the
-- e-graph cannot re-associate `(inv x · x · y)` so that the `inv_l` pattern
-- on the leading pair fires.
--| @saturation both
axiom gmul_assoc (x y z: G):
  $ eq (gmul (gmul x y) z) (gmul x (gmul y z)) $;

-- Derived but useful equational facts (shrinking or neutral).
--| @saturation ltr
axiom inv_inv (x: G): $ eq (ginv (ginv x)) x $;
--| @saturation ltr
axiom inv_id: $ eq (ginv e) e $;
--| @saturation ltr
axiom inv_gmul (x y: G):
  $ eq (ginv (gmul x y)) (gmul (ginv y) (ginv x)) $;
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
fn proves_inv_inv_directly() {
    let decl = "\ntheorem target (x: G): $ eq (ginv (ginv x)) x $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by inv_inv"));
    verify("domain_group_inv_inv", decl, &auf);
}

#[test]
fn proves_inv_of_identity_is_identity() {
    let decl = "\ntheorem target: $ eq (ginv e) e $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by inv_id"));
    verify("domain_group_inv_id", decl, &auf);
}

#[test]
fn proves_socks_and_shoes() {
    // (x * y)^-1 = y^-1 * x^-1 — the classic non-commutative "socks and shoes" identity.
    let decl = concat!(
        "\ntheorem target (x y: G):\n",
        "  $ eq (ginv (gmul x y)) (gmul (ginv y) (ginv x)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by inv_gmul"));
    verify("domain_group_socks_shoes", decl, &auf);
}

#[test]
fn proves_inv_kills_self_product() {
    // inv(x * inv x) = e — both sides collapse through inv_r and inv_id.
    let decl = "\ntheorem target (x: G): $ eq (ginv (gmul x (ginv x))) e $;\n";
    let auf = prove_auf(decl);
    // The e-graph has `x` and `ginv (ginv x)` in the same class, so egglog
    // can route through inv_l (on `(ginv inv x · ginv x)`) or via inv_r/inv_id
    // on the original product. Accept any inverse-collapse rule.
    assert!(auf.contains("by inv_l") || auf.contains("by inv_r"));
    assert!(auf.contains("by inv_gmul") || auf.contains("by inv_id"));
    verify("domain_group_inv_self_product", decl, &auf);
}

#[test]
fn proves_right_multiplication_cancels() {
    // (x * y) * inv y = x  via associativity + inv_r + id_r.
    let decl = concat!(
        "\ntheorem target (x y: G):\n",
        "  $ eq (gmul (gmul x y) (ginv y)) x $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by gmul_assoc"));
    assert!(auf.contains("by inv_r"));
    assert!(auf.contains("by id_r"));
    verify("domain_group_right_cancel", decl, &auf);
}

#[test]
fn proves_left_multiplication_cancels() {
    // inv x * (x * y) = y  via associativity (reversed) + inv_l + id_l.
    let decl = concat!(
        "\ntheorem target (x y: G):\n",
        "  $ eq (gmul (ginv x) (gmul x y)) y $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by inv_l"));
    assert!(auf.contains("by id_l") || auf.contains("by id_r"));
    verify("domain_group_left_cancel", decl, &auf);
}

#[test]
fn proves_compound_inverse_collapse() {
    // inv(x * y) * (x * y) = e — generic inv_l instance on a compound product.
    let decl = concat!(
        "\ntheorem target (x y: G):\n",
        "  $ eq (gmul (ginv (gmul x y)) (gmul x y)) e $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by inv_l"));
    verify("domain_group_compound_inv_l", decl, &auf);
}

#[test]
fn proves_three_factor_inverse() {
    // inv(x * y * z) = inv z * inv y * inv x — chained socks-and-shoes.
    let decl = concat!(
        "\ntheorem target (x y z: G):\n",
        "  $ eq (ginv (gmul (gmul x y) z))\n",
        "       (gmul (gmul (ginv z) (ginv y)) (ginv x)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by inv_gmul"));
    verify("domain_group_three_factor_inv", decl, &auf);
}

#[test]
fn proves_conjugation_normalises_to_self() {
    // x * y * inv x * x = x * y — collapsing a left conjugation tail.
    let decl = concat!(
        "\ntheorem target (x y: G):\n",
        "  $ eq (gmul (gmul (gmul x y) (ginv x)) x) (gmul x y) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by gmul_assoc"));
    assert!(auf.contains("by inv_l"));
    assert!(auf.contains("by id_r"));
    verify("domain_group_conjugation_tail", decl, &auf);
}

#[test]
fn verifies_implicit_socks_and_shoes() {
    let decl = concat!(
        "\ntheorem target (x y: G):\n",
        "  $ eq (ginv (gmul x y)) (gmul (ginv y) (ginv x)) $;\n",
    );
    let auf = prove_implicit_auf("domain_group_implicit_socks_shoes", decl);
    assert!(auf.contains("by inv_gmul"));
    assert!(!auf.contains(":="));
    verify("domain_group_implicit_socks_shoes", decl, &auf);
}

#[test]
fn fixture_file_axioms_match_embedded_axioms() {
    let fixture = include_str!("fixtures/domain_group.mm0");
    for axiom_name in [
        "id_l",
        "id_r",
        "inv_l",
        "inv_r",
        "inv_inv",
        "inv_id",
        "inv_gmul",
        "gmul_assoc",
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
