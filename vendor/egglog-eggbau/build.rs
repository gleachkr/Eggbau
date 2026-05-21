use std::env;
use std::fs;
use std::path::{Path, PathBuf};

const LIB_MARKER: &str = "pub mod proof";
const TERM_DAG_MARKER: &str = "pub fn term_dag(&self) -> &TermDag";

fn main() {
    println!("cargo:rustc-env=FULL_VERSION=2.0.0_eggbau-patched");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../egglog-eggbau-proof-api.patch");
    println!("cargo:rerun-if-changed=../egglog/src/lib.rs");
    println!("cargo:rerun-if-changed=../egglog/src/proofs/proof_format.rs");

    let manifest_dir = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let egglog_dir = manifest_dir.join("../egglog");
    ensure_submodule_present(&egglog_dir);
    ensure_patch_applied(&egglog_dir);
}

fn ensure_submodule_present(egglog_dir: &Path) {
    let required = [
        egglog_dir.join("Cargo.toml"),
        egglog_dir.join("src/lib.rs"),
        egglog_dir.join("src/proofs/proof_format.rs"),
    ];

    if required.iter().all(|path| path.is_file()) {
        return;
    }

    panic!(
        "egglog submodule is not initialized.\n\
         Run `git submodule update --init --recursive` from the eggbau \
         repository root, then rerun Cargo.\n\
         Expected vendored egglog sources under `vendor/egglog`."
    );
}

// Keep these textual edits in sync with ../egglog-eggbau-proof-api.patch.
fn ensure_patch_applied(egglog_dir: &Path) {
    let lib_path = egglog_dir.join("src/lib.rs");
    let proof_format_path = egglog_dir.join("src/proofs/proof_format.rs");

    let mut lib = read_source(&lib_path);
    let mut proof_format = read_source(&proof_format_path);

    let lib_done = lib.contains(LIB_MARKER);
    let proof_done = proof_format.contains(TERM_DAG_MARKER);

    if lib_done && proof_done {
        return;
    }

    if lib_done != proof_done {
        panic!(
            "egglog proof API patch is only partially applied.\n\
             Reset `vendor/egglog` to the pinned submodule commit and rerun \
             Cargo so eggbau can apply `vendor/egglog-eggbau-proof-api.patch`."
        );
    }

    patch_lib_rs(&mut lib);
    patch_proof_format_rs(&mut proof_format);

    write_source(&lib_path, &lib);
    write_source(&proof_format_path, &proof_format);
}

fn patch_lib_rs(lib: &mut String) {
    const ANCHOR: &str = "pub use proofs::proof_encoding_helpers::{file_supports_proofs, program_supports_proofs};\n";
    const INSERTION: &str = "\n/// Read-only proof reconstruction API.\npub mod proof {\n    pub use crate::proofs::proof_format::{Justification, Proof, ProofId, ProofStore, Proposition};\n}\n";

    insert_after(lib, ANCHOR, INSERTION, "src/lib.rs");
}

fn patch_proof_format_rs(proof_format: &mut String) {
    const ANCHOR: &str = "impl ProofStore {\n";
    const INSERTION: &str = "    /// Get the term DAG used by this proof store.\n    pub fn term_dag(&self) -> &TermDag {\n        &self.term_dag\n    }\n\n";

    insert_after(
        proof_format,
        ANCHOR,
        INSERTION,
        "src/proofs/proof_format.rs",
    );
}

fn insert_after(source: &mut String, anchor: &str, insertion: &str, path: &str) {
    let Some(index) = source.find(anchor) else {
        panic!(
            "could not apply egglog proof API patch: anchor not found in \
             `vendor/egglog/{path}`.\n\
             The submodule is probably not at eggbau's pinned egglog commit."
        );
    };

    source.insert_str(index + anchor.len(), insertion);
}

fn read_source(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|err| {
        panic!(
            "could not read `{}` while applying the egglog proof API patch: \
             {err}",
            path.display()
        )
    })
}

fn write_source(path: &Path, source: &str) {
    fs::write(path, source).unwrap_or_else(|err| {
        panic!(
            "could not write `{}` while applying the egglog proof API patch: \
             {err}",
            path.display()
        )
    });
}
