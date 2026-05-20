use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const AXIOMS: &str = r#"
delimiter $ ( ) $;
sort addr;
sort size;
provable sort wff;
term addr_eq (a b: addr): wff;
term size_eq (n m: size): wff;
term bi (x y: wff): wff;

term zero_size: size;
term offset (a: addr) (n: size): addr;

term in_frame (a: addr) (n: size): wff;
term aligned (a: addr) (n: size): wff;
term writable (a: addr) (n: size): wff;
term readable (a: addr) (n: size): wff;

--| @relation addr addr_eq addr_refl addr_trans addr_sym _
axiom addr_refl (a: addr): $ addr_eq a a $;
axiom addr_trans (a b c: addr):
  $ addr_eq a b $ > $ addr_eq b c $ > $ addr_eq a c $;
axiom addr_sym (a b: addr): $ addr_eq a b $ > $ addr_eq b a $;

--| @relation size size_eq size_refl size_trans size_sym _
axiom size_refl (n: size): $ size_eq n n $;
axiom size_trans (n m p: size):
  $ size_eq n m $ > $ size_eq m p $ > $ size_eq n p $;
axiom size_sym (n m: size): $ size_eq n m $ > $ size_eq m n $;

--| @relation wff bi bi_refl bi_trans bi_sym bi_mp
axiom bi_refl (x: wff): $ bi x x $;
axiom bi_trans (x y z: wff): $ bi x y $ > $ bi y z $ > $ bi x z $;
axiom bi_sym (x y: wff): $ bi x y $ > $ bi y x $;
axiom bi_mp (x y: wff): $ bi x y $ > $ x $ > $ y $;

--| @congr
axiom offset_congr (a b: addr) (n m: size):
  $ addr_eq a b $ > $ size_eq n m $ > $ addr_eq (offset a n) (offset b m) $;

--| @congr
axiom in_frame_congr (a b: addr) (n m: size):
  $ addr_eq a b $ > $ size_eq n m $ > $ bi (in_frame a n) (in_frame b m) $;
--| @congr
axiom aligned_congr (a b: addr) (n m: size):
  $ addr_eq a b $ > $ size_eq n m $ > $ bi (aligned a n) (aligned b m) $;
--| @congr
axiom writable_congr (a b: addr) (n m: size):
  $ addr_eq a b $ > $ size_eq n m $ > $ bi (writable a n) (writable b m) $;
--| @congr
axiom readable_congr (a b: addr) (n m: size):
  $ addr_eq a b $ > $ size_eq n m $ > $ bi (readable a n) (readable b m) $;

--| @saturation ltr
axiom offset_zero (a: addr): $ addr_eq (offset a zero_size) a $;

--| @saturation horn
axiom writable_from_frame_aligned (a: addr) (n: size):
  $ in_frame a n $ > $ aligned a n $ > $ writable a n $;

--| @saturation horn
axiom readable_from_writable (a: addr) (n: size):
  $ writable a n $ > $ readable a n $;
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
fn proves_writable_directly_from_horn() {
    let decl = concat!(
        "\ntheorem target (a: addr) (n: size):\n",
        "  $ in_frame a n $ > $ aligned a n $ > $ writable a n $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by writable_from_frame_aligned"));
    verify("stage8_mem_writable_direct", decl, &auf);
}

#[test]
fn proves_readable_via_horn_chain() {
    let decl = concat!(
        "\ntheorem target (a: addr) (n: size):\n",
        "  $ in_frame a n $ > $ aligned a n $ > $ readable a n $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by writable_from_frame_aligned"));
    assert!(auf.contains("by readable_from_writable"));
    verify("stage8_mem_readable_chain", decl, &auf);
}

#[test]
fn proves_writable_modulo_addr_eq() {
    let decl = concat!(
        "\ntheorem target (a b: addr) (n: size):\n",
        "  $ addr_eq a b $ > $ in_frame a n $ > $ aligned a n $ > $ writable b n $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by writable_from_frame_aligned"));
    assert!(auf.contains("by writable_congr"));
    assert!(auf.contains("by bi_mp"));
    verify("stage8_mem_writable_modulo_eq", decl, &auf);
}

#[test]
fn proves_writable_with_offset_zero_normalisation() {
    let decl = concat!(
        "\ntheorem target (a: addr) (n: size):\n",
        "  $ in_frame (offset a zero_size) n $ >\n",
        "  $ aligned (offset a zero_size) n $ >\n",
        "  $ writable a n $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by offset_zero"));
    assert!(auf.contains("by writable_from_frame_aligned"));
    verify("stage8_mem_writable_offset_zero", decl, &auf);
}

#[test]
fn proves_readable_chain_modulo_addr_and_size_eq() {
    let decl = concat!(
        "\ntheorem target (a b: addr) (n m: size):\n",
        "  $ addr_eq a b $ > $ size_eq n m $ >\n",
        "  $ in_frame a n $ > $ aligned a n $ >\n",
        "  $ readable b m $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by writable_from_frame_aligned"));
    assert!(auf.contains("by readable_from_writable"));
    assert!(auf.contains("by readable_congr"));
    assert!(auf.contains("by bi_mp"));
    verify("stage8_mem_readable_modulo_eq", decl, &auf);
}

#[test]
fn proves_writable_through_nested_offset_zeros() {
    let decl = concat!(
        "\ntheorem target (a: addr) (n: size):\n",
        "  $ in_frame (offset (offset a zero_size) zero_size) n $ >\n",
        "  $ aligned (offset (offset a zero_size) zero_size) n $ >\n",
        "  $ writable a n $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by offset_zero"));
    assert!(auf.contains("by writable_from_frame_aligned"));
    verify("stage8_mem_writable_nested_offsets", decl, &auf);
}

#[test]
fn fixture_file_axioms_match_embedded_axioms() {
    let fixture = include_str!("fixtures/stage8_memory_safety.mm0");
    for axiom_name in [
        "writable_from_frame_aligned",
        "readable_from_writable",
        "writable_congr",
        "offset_zero",
        "bi_mp",
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
