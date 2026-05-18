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

## Stage 0 status

This repository currently contains the Rust crate skeleton, a small CLI, and a
fixture harness.  Serious MM0 parsing, export validation, proof search,
egglog-proof translation, and `.auf` rendering are later stages.

Useful commands:

```sh
cargo test
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
eggbau --version
eggbau discover tests/fixtures/empty/input.mm0
```

The crate is pinned to egglog `2.0.0`.  A stage-0 proof API spike records that
this public crate exposes term encoding, but not the structured
`ProofStore`/`Justification` inspection API needed by the full design.  Later
work should either move to an egglog pin with that API or carry a small
read-only proof API patch.
