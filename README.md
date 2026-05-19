# eggbau

`eggbau` is planned as a Rust library and CLI for proof search over selected
MM0/Aufbau declarations.  It is not a verifier extension and it is not part of
the trusted MM0 kernel.

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
producers.  The generated MMB must still be checked by an MM0 verifier.

## Metadata policy

`eggbau` uses assertion-level `@saturation` metadata to decide which theorems
may be exported into egglog saturation:

```text
--| @saturation ltr
--| @saturation rtl
--| @saturation both
--| @saturation horn
```

It also plans to reuse Aufbau's existing `@relation` and `@congr` metadata.
It does not treat `@rewrite` as an eggbau contract.  `@rewrite` belongs to the
Aufbau normalizer; a theorem marked only with `@rewrite` must not be exported
to egglog by eggbau.

## Stage 1 status

This repository currently contains the Rust crate skeleton, a small CLI, a
fixture harness, and a conservative MM0 declaration parser.  The parser extracts
sorts, terms, assertion binders, hypotheses, conclusions, `@relation`,
`@congr`, and `@saturation` metadata for the supported prefix fragment.  It
fails closed for unsupported declaration forms and reports clear diagnostics for
unsupported notation.  Export validation, proof search, egglog-proof
translation, and `.auf` rendering are later stages.

Useful commands:

```sh
cargo test
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
eggbau --version
eggbau discover tests/fixtures/empty/input.mm0
eggbau dump-env tests/fixtures/stage1/input.mm0
eggbau dump-env tests/fixtures/stage1/input.mm0 --theorem bv_add_zero
```

The crate uses a vendored egglog `2.0.0` checkout with the temporary eggbau
read-only proof API patch described in `AGENTS.md`.  The stage-0 proof API
spike checks that `CommandOutput::ProveExists`, `ProofStore`,
`Justification`, propositions, and proof terms are visible through that patched
API.
