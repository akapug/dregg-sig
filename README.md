# dregg-sig

Post-quantum signing in Rust: standard and threshold hash-based signatures, quorum switching for stateful keys, and succinct aggregation of many signatures into one proof. No elliptic-curve pairings, no trusted setup, and no `crates.io` dependencies in the library crates.

Research prototype. No external audit.

## What is here

| Crate | Directory | What it provides |
| --- | --- | --- |
| `dregg-sig-core` | `crates/core` | FIPS 205 SLH-DSA (all six SHAKE parameter sets), the native formats `Baggy` (stateless) and `Jorts` / `JortsPoseidon2` (stateful), and the MPC engines that threshold-sign them: only the secret hashes run under MPC, the public Merkle layers are computed in the clear. Dealerless key generation, the `BeltLatch` one-time-leaf latch, crash-atomic journals and rollback anchors. |
| `dregg-sig-quorum` | `crates/quorum` | Isolated one-party-per-value custodians over a framed, encrypted wire transport; quorum-switching `Jorts` (disjoint committees, or certified `(t, n)` release); threshold signing of `JortsPoseidon2` keys that Hem can aggregate. |
| `dregg-sig-fts` | `crates/fts` | Compact few-time signatures (`Compact1122`: 1,122 bytes) for single-use votes, single-signer and threshold, with a durable burn journal. |
| `dregg-sig-agg` | `crates/agg` | Hem: proves that a batch of `JortsPoseidon2` signatures verifies, using Goldilocks sumcheck and WHIR polynomial commitments; merges and recursive composition of those proofs; the zero-knowledge protocol the recursion is built on. |
| `dregg-sig-accel` | `crates/accel` | Hash and field kernels behind one backend trait, a CPU reference backend, and a Vulkan compute prover (feature `vulkan`, Linux). |
| `dregg-sig-asm` | `crates/asm` | Constant-time SIMD and assembly kernels (x86-64 and AArch64) with portable fallbacks, secret wiping, durable-file primitives. |
| `dregg-sig-verified`, `dregg-sig-whir-verified` | `crates/verified`, `crates/whir-verified` | Small `no_std` kernels (field arithmetic, Keccak, release guards, WHIR fold steps) that the crates above call. They were written to be extracted to Lean; the proofs are not in this repository. |

Library crates are `no_std` + `alloc`; storage, anchors and transports need the `std` feature.

## Try it

The toolchain is pinned to Rust 1.99.1 (`rust-toolchain.toml`).

```sh
# FIPS 205 sign and verify, and dealerless 2-of-3 key shares.
cargo run --release -p dregg-sig-core --features std --example slh_dsa_quickstart

# Threshold SLH-DSA: 2-of-3, and with `-- --cnf-rss-3of5` an isolated 3-of-5 ceremony.
cargo run --release -p dregg-sig-quorum --features std --example threshold_slh_dsa_quickstart

# Aggregate eight signatures in two shards, merge, verify.
cargo run --release -p dregg-sig-agg --example succinct_k_to_1_aggregation
```

`crates/agg/examples/mock_ethereum_beam.rs` and `mock_solana_alpenglow.rs` are single-host consensus harnesses with explicit network models. The GPU prover is selected with `--features vulkan` and `DREGG_SIG_ACCEL=vulkan`.

## Tests

Run a filtered set: the full suites take hours of CPU and tens of GB.

```sh
cargo test --release -p dregg-sig-core --features std fips205::
cargo test --release -p dregg-sig-agg --test cshake_proof_bytes_kat
```

`fuzz/` holds five libFuzzer targets for the wire decoders and verifiers (`cargo fuzz run <target>` from that directory; it is a separate workspace with its own dependencies).

## Provenance

Extracted from `qsag` at commit `cf41f1c` plus that tree's uncommitted crate edits. What changed on the way:

- Crates, Rust identifiers, assembly symbols and environment variables were renamed (`qsag-*` to `dregg-sig-*`, `QSAG_*` to `DREGG_SIG_*`).
- Wire formats are unchanged. Domain-separation tags and wire magics still read `QSAG.…`; changing them would change every signature, proof and known-answer vector.
- Left in `qsag`: the Lean proof library and Aeneas extraction, the hardware projects, the paper, the CLI, and the wallet, migration, credential and policy crates (`qsag-hd`, `qsag-addr`, `qsag-migrate`, `qsag-cred`, `qsag-policy`).
- Removed from the kept crates: the credential, capability and private-multisignature relations in `agg`, their guards in `verified`, and the in-process CNF coordinator prototype in `core` that its own documentation quarantined.

Doc comments that cite `lean/Qsag/…` or `Qsag.<name>` point at the proofs in `qsag`. Those proofs, the constant-time archive screen and the assembly byte fixtures were recorded against `qsag`'s sources and symbol names; none of them has been re-run on this tree.

## License

Authored by ember arlynx (`<ember@lunar.town>`). Licensed under either [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
