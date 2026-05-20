use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const AXIOMS: &str = r#"
delimiter $ ( ) $;
sort elem;
sort list;
sort nat;
provable sort wff;

term list_eq (xs ys: list): wff;
term nat_eq (n m: nat): wff;

term nil: list;
term cons (h: elem) (t: list): list;
term app (xs ys: list): list;
term rev (xs: list): list;
term length (xs: list): nat;

term zero_nat: nat;
term succ (n: nat): nat;
term nat_add (n m: nat): nat;

--| @relation list list_eq list_refl list_trans list_sym _
axiom list_refl (xs: list): $ list_eq xs xs $;
axiom list_trans (xs ys zs: list):
  $ list_eq xs ys $ > $ list_eq ys zs $ > $ list_eq xs zs $;
axiom list_sym (xs ys: list): $ list_eq xs ys $ > $ list_eq ys xs $;

--| @relation nat nat_eq nat_refl nat_trans nat_sym _
axiom nat_refl (n: nat): $ nat_eq n n $;
axiom nat_trans (n m p: nat):
  $ nat_eq n m $ > $ nat_eq m p $ > $ nat_eq n p $;
axiom nat_sym (n m: nat): $ nat_eq n m $ > $ nat_eq m n $;

--| @congr
axiom app_congr (a b c d: list):
  $ list_eq a b $ > $ list_eq c d $ > $ list_eq (app a c) (app b d) $;
--| @congr
axiom rev_congr (a b: list):
  $ list_eq a b $ > $ list_eq (rev a) (rev b) $;
--| @congr
axiom length_congr (a b: list):
  $ list_eq a b $ > $ nat_eq (length a) (length b) $;
--| @congr
axiom succ_congr (n m: nat): $ nat_eq n m $ > $ nat_eq (succ n) (succ m) $;
--| @congr
axiom nat_add_congr (a b c d: nat):
  $ nat_eq a b $ > $ nat_eq c d $ > $ nat_eq (nat_add a c) (nat_add b d) $;

--| @saturation ltr
axiom app_nil_l (xs: list): $ list_eq (app nil xs) xs $;
--| @saturation ltr
axiom app_nil_r (xs: list): $ list_eq (app xs nil) xs $;
--| @saturation ltr
axiom app_assoc (xs ys zs: list):
  $ list_eq (app (app xs ys) zs) (app xs (app ys zs)) $;

--| @saturation ltr
axiom rev_nil: $ list_eq (rev nil) nil $;
--| @saturation ltr
axiom rev_rev (xs: list): $ list_eq (rev (rev xs)) xs $;
--| @saturation ltr
axiom rev_app (xs ys: list):
  $ list_eq (rev (app xs ys)) (app (rev ys) (rev xs)) $;

--| @saturation ltr
axiom length_nil: $ nat_eq (length nil) zero_nat $;
--| @saturation ltr
axiom length_cons (h: elem) (xs: list):
  $ nat_eq (length (cons h xs)) (succ (length xs)) $;
--| @saturation ltr
axiom length_app (xs ys: list):
  $ nat_eq (length (app xs ys)) (nat_add (length xs) (length ys)) $;
--| @saturation ltr
axiom length_rev (xs: list): $ nat_eq (length (rev xs)) (length xs) $;

--| @saturation ltr
axiom nat_add_zero_l (n: nat): $ nat_eq (nat_add zero_nat n) n $;
--| @saturation ltr
axiom nat_add_zero_r (n: nat): $ nat_eq (nat_add n zero_nat) n $;
--| @saturation ltr
axiom nat_add_comm (n m: nat): $ nat_eq (nat_add n m) (nat_add m n) $;
--| @saturation ltr
axiom nat_add_assoc (n m p: nat):
  $ nat_eq (nat_add (nat_add n m) p) (nat_add n (nat_add m p)) $;
--| @saturation ltr
axiom succ_nat_add_l (n m: nat):
  $ nat_eq (nat_add (succ n) m) (succ (nat_add n m)) $;
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
fn proves_app_nil_right_collapse() {
    let decl = "\ntheorem target (xs: list): $ list_eq (app xs nil) xs $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by app_nil_r"));
    verify("stage8_list_app_nil_r", decl, &auf);
}

#[test]
fn proves_rev_rev_under_app() {
    let decl = concat!(
        "\ntheorem target (xs ys: list):\n",
        "  $ list_eq (app (rev (rev xs)) ys) (app xs ys) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by rev_rev"));
    assert!(auf.contains("by app_congr"));
    verify("stage8_list_rev_rev_app", decl, &auf);
}

#[test]
fn proves_rev_app_swap_direct() {
    let decl = concat!(
        "\ntheorem target (xs ys: list):\n",
        "  $ list_eq (rev (app xs ys)) (app (rev ys) (rev xs)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by rev_app"));
    verify("stage8_list_rev_app_swap", decl, &auf);
}

#[test]
fn proves_length_app_nil_right_via_cross_sort_congr() {
    let decl = concat!(
        "\ntheorem target (xs: list):\n",
        "  $ nat_eq (length (app xs nil)) (length xs) $;\n",
    );
    let auf = prove_auf(decl);
    // cross-sort: list_eq fact about app xs nil → nat_eq about length
    assert!(auf.contains("by length_congr") || auf.contains("by length_app"));
    assert!(auf.contains("by app_nil_r") || auf.contains("by length_nil"));
    verify("stage8_list_length_app_nil", decl, &auf);
}

#[test]
fn proves_length_rev_app_combined() {
    // length(rev(app(xs,ys))) = length(xs) + length(ys)
    // using rev_app + length_app + length_rev + nat_add_comm
    let decl = concat!(
        "\ntheorem target (xs ys: list):\n",
        "  $ nat_eq (length (rev (app xs ys)))\n",
        "           (nat_add (length xs) (length ys)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by length_app"));
    assert!(auf.contains("by length_rev"));
    verify("stage8_list_length_rev_app", decl, &auf);
}

#[test]
fn proves_length_two_cons_is_two() {
    // length(cons h (cons k nil)) = succ(succ zero_nat)
    let decl = concat!(
        "\ntheorem target (h k: elem):\n",
        "  $ nat_eq (length (cons h (cons k nil))) (succ (succ zero_nat)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by length_cons"));
    assert!(auf.contains("by length_nil"));
    verify("stage8_list_length_two_cons", decl, &auf);
}

#[test]
fn proves_length_cons_app() {
    let decl = concat!(
        "\ntheorem target (h: elem) (xs ys: list):\n",
        "  $ nat_eq (length (app (cons h xs) ys))\n",
        "           (succ (nat_add (length xs) (length ys))) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by length_app"));
    assert!(auf.contains("by length_cons"));
    verify("stage8_list_length_cons_app", decl, &auf);
}

#[test]
fn proves_rev_three_app_assoc() {
    // rev(app(app(xs,ys),zs)) = app(rev zs, app(rev ys, rev xs))
    let decl = concat!(
        "\ntheorem target (xs ys zs: list):\n",
        "  $ list_eq (rev (app (app xs ys) zs))\n",
        "           (app (rev zs) (app (rev ys) (rev xs))) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by rev_app"));
    verify("stage8_list_rev_three_app", decl, &auf);
}

#[test]
fn fixture_file_axioms_match_embedded_axioms() {
    let fixture = include_str!("fixtures/stage8_list_monoid.mm0");
    for axiom_name in [
        "app_nil_r",
        "rev_app",
        "rev_rev",
        "length_app",
        "length_rev",
        "length_cons",
        "length_congr",
        "nat_add_assoc",
        "succ_nat_add_l",
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
