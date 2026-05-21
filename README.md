# eggbau

`eggbau` is a Rust library and CLI for proof search over selected MM0/Aufbau
assertions. It is not a verifier extension and it is not part of the trusted
MM0 kernel.

The intended boundary is:

```text
.mm0 source with Aufbau and eggbau metadata
  -> eggbau proof search
  -> generated ordinary .auf proof script
  -> abc compile
  -> .mmb
  -> mm0-zig or mm0-c verification
```

`eggbau`, egglog, and Aufbau proof-script elaboration are untrusted proof
producers. The generated MMB must still be checked by an MM0 verifier.

## Metadata policy

`eggbau` uses assertion-level `@saturation` metadata to decide which theorems
may be exported into egglog saturation:

```text
--| @saturation ltr
--| @saturation rtl
--| @saturation both
--| @saturation horn
```

It also reuses Aufbau's existing `@relation` and `@congr` metadata. It does
not treat `@rewrite` as an eggbau contract. `@rewrite` belongs to the Aufbau
normalizer; a theorem marked only with `@rewrite` is not exported to egglog by
eggbau.

## CLI

Current public commands are:

```sh
eggbau --version
eggbau discover INPUT.mm0 [--suggest-annotations]
eggbau list INPUT.mm0
eggbau prove INPUT.mm0 [OPTIONS]
eggbau script emit INPUT.mm0 [OPTIONS]
eggbau script prove INPUT.mm0 [OPTIONS]
eggbau script check INPUT.mm0 [OPTIONS]
```

`prove` is the main command. It accepts one or more public theorem targets and
writes generated `.auf` to stdout unless `--out` is supplied:

```sh
eggbau prove tests/fixtures/cli_e2e.mm0 \
  --theorem target \
  --out generated.auf
```

Useful target and output options:

```text
-t, --theorem NAME       Prove a public theorem from INPUT.mm0
    --lemma HEADER       Prove and emit a proof-local Aufbau lemma
    --targets FILE       Read theorem/lemma targets, one per line
-o, --out FILE           Write generated .auf to FILE
    --base FILE          Splice generated proofs into an existing .auf
    --format FORMAT      Formatting dimension value: explicit, implicit,
                         compact, nocompact, kernel, or notation
```

Multiple `--format` values may be supplied. `explicit` and `implicit`,
`compact` and `nocompact`, and `kernel` and `notation` are independent
formatting dimensions; the last value in each dimension wins. `kernel` is the
current default math renderer. `notation` asks the `.auf` renderer to use the
last printable MM0 notation declared for each constructor.

A target file is line-oriented:

```text
-- comments and blank lines are ignored
theorem target
lemma local_id (x: s): $ eq (f x) x $
```

`list` prints script-friendly public theorem targets in MM0 declaration order:

```sh
eggbau list tests/fixtures/cli_multi.mm0
```

Editable egglog scripts live under the `script` namespace:

```sh
eggbau script emit tests/fixtures/cli_e2e.mm0 \
  --theorem target > target.egg

eggbau script prove tests/fixtures/cli_e2e.mm0 \
  --theorem target \
  --script target.egg \
  --out generated.auf
```

`script check` runs an egglog script and validates the reconstructed proof
without rendering `.auf`.

## Library API

Rust callers can keep a parsed proof-search session in memory and prove public
or generated theorem obligations without invoking `abc`:

```rust
use eggbau::{EggbauSession, GoalSpec};

let mut session = EggbauSession::from_mm0(mm0_text)?;
let proof = session.prove_theorem("target")?;
let cert = session.prove_to_cert("target")?;
let auf = session.render_auf_for_theorem("target", &cert)?;

let generated = GoalSpec::generated_theorem(
    "downstream_target (x: s): $ eq (f x) x $",
);
let generated_proof = session.prove_goal(generated)?;
```

`ProofResult` contains the theorem name, rendered `.auf` block, optional
editable egglog program text, certificate IR, and diagnostics. The stable API
uses eggbau certificate types, not egglog `ProofStore` or `ProofId` internals.

## End-to-end verification

A generated proof is checked by the ordinary Aufbau/MM0 pipeline:

```sh
eggbau prove tests/fixtures/cli_e2e.mm0 \
  --theorem target \
  --out generated.auf
abc compile tests/fixtures/cli_e2e.mm0 generated.auf generated.mmb
mm0-zig generated.mmb < tests/fixtures/cli_e2e.mm0
```

The end-to-end CLI tests look for `abc` and `mm0-zig` on `PATH`. You can also
set explicit tool paths:

```sh
EGGBAU_ABC=/path/to/abc \
EGGBAU_MM0_ZIG=/path/to/mm0-zig \
CARGO_HOME="$PWD/.cargo_home" cargo test --test cli_e2e
```

If the tools are unavailable, those tests print a skip message and return.

## Development commands

The vendored egglog dependency needs to be patched to expose some needed egglog 
internals. After submodule initialization, `vendor/egglog-eggbau/build.rs` 
applies the patch automatically before compiling proof-related code. If the 
submodule is not initialized at all, Cargo may fail while resolving the path 
dependency before the wrapper build script can run; initialize it with:

```sh
git submodule update --init --recursive
```

Useful validation commands:

```sh
CARGO_HOME="$PWD/.cargo_home" cargo fmt --all -- --check
CARGO_HOME="$PWD/.cargo_home" cargo build --all-targets --all-features
CARGO_HOME="$PWD/.cargo_home" cargo test --all-targets --all-features
CARGO_HOME="$PWD/.cargo_home" cargo clippy --all-targets --all-features -- \
  -D warnings
```
