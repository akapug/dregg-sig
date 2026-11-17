# dregg-sig

Post-quantum signing in Rust: standard and threshold hash-based signatures, quorum switching for stateful keys, and succinct aggregation of many signatures into one proof. No elliptic-curve pairings, no trusted setup, and no `crates.io` dependencies in the library crates.

Research prototype. No external audit.

## What is here

| Crate | Directory | What it provides |
| --- | --- | --- |
| `dregg-sig-core` | `crates/core` | FIPS 205 SLH-DSA (all six SHAKE parameter sets), the native formats `Baggy` (stateless) and `Jorts` / `JortsPoseidon2` (stateful), and the MPC engines that threshold-sign them: only the secret hashes run under MPC, the public Merkle layers are computed in the clear. Dealerless key generation, the `BeltLatch` one-time-leaf latch, crash-atomic journals and rollback anchors. |
| `dregg-sig-quorum` | `crates/quorum` | Isolated one-party-per-value custodians over a framed, encrypted wire transport; quorum-switching `Jorts` (disjoint committees, or certified `(t, n)` release); threshold signing of `JortsPoseidon2` keys that Hem can aggregate. |
| `dregg-sig-fts` | `crates/fts` | Compact few-time signatures (`Compact1122`: 1,122 bytes) for single-use votes, single-signer and threshold, with a durable burn journal. |
| `dregg-sig-agg` | `crates/agg` | Hem: proves that a batch of `JortsPoseidon2` signatures verifies, using Goldilocks sumcheck and WHIR polynomial commitments; merges and recursive composition of those proofs; committed-mask zk-Hem for full-shard and credential relations, with composed privacy and concrete knowledge-soundness bounds still unestablished (see `crates/agg/src/zk_hem/protocol.rs`, `prove`). Other recursion modes are non-hiding. |
| `dregg-sig-cred` | `crates/cred` | Threshold ML-DSA-44/65/87, custom symmetric Poseidon2 threshold OPRFs with participant checks, and `BlindVC` presentations of issuer-managed accumulator membership. Issuance attributes are visible to the issuer; credential tokens are not independently publicly verifiable signatures. zk-Hem proves presentation relations against trusted issuer roots; network orchestration of the exact-threshold SPDZ OPRF remains unimplemented. |
| `dregg-sig-policy` | `crates/policy` | Velocity, allowlist and window rules checked before custodians release shares; reusable `SpongeMacaroon` bearer grants and attenuable `PqBiscuit` chains. Biscuit V2 seals optionally bind the complete intent and require a consumption store for one-use acceptance; the local disk store survives crashes, not adversarial rollback or independent replicas. |
| `dregg-sig-addr` | `crates/addr` | Bech32m post-quantum addresses, hybrid keys, and the canonical 128-byte signing intent. |
| `dregg-sig-hd` | `crates/hd` | Dealerless module-lattice key hierarchies and committed watch-only inventories. |
| `dregg-sig-migrate` | `crates/migrate` | Zero-knowledge ownership proofs for secp256k1, Ed25519, Pallas and BLS12-381 keys, local or threshold, bound to a post-quantum address. Read `crates/migrate/SECURITY.md` before relying on it. |
| `dregg-sig-cli` | `crates/cli` | The `dregg-sig` command-line tool and the runnable examples. |
| `dregg-sig-accel` | `crates/accel` | Hash and field kernels behind one backend trait, a CPU reference backend, and a Vulkan compute prover (feature `vulkan`, Linux). |
| `dregg-sig-asm` | `crates/asm` | Constant-time SIMD and assembly kernels (x86-64 and AArch64) with portable fallbacks, secret wiping, durable-file primitives. |
| `dregg-sig-verified`, `dregg-sig-whir-verified` | `crates/verified`, `crates/whir-verified` | Small `no_std` kernels (field arithmetic, Keccak, release guards, WHIR fold steps) that the crates above call. They were written to be extracted to Lean; the proofs are not in this repository. |

Library crates are `no_std` + `alloc`; storage, anchors and transports need the `std` feature.

## Try it

The toolchain is pinned to Rust 1.99.1 (`rust-toolchain.toml`).

```sh
# Known-answer tests and supported formats.
cargo run --release -p dregg-sig-cli -- kat
cargo run --release -p dregg-sig-cli -- info

# Generate an SLH-DSA key, sign a file, verify it.
umask 077 && D=$(mktemp -d /tmp/dregg-sig.XXXXXX) && printf 'hello\n' > "$D/msg"
cargo run --release -p dregg-sig-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$D/sk.json" --public-out "$D/pk.json"
cargo run --release -p dregg-sig-cli -- sign --secret "$D/sk.json" --in "$D/msg" --out "$D/sig.json"
cargo run --release -p dregg-sig-cli -- verify --public "$D/pk.json" --in "$D/msg" --sig "$D/sig.json"

# Examples.
cargo run --release -p dregg-sig-cli --example threshold_slh_dsa_quickstart
cargo run --release -p dregg-sig-cli --example succinct_k_to_1_aggregation
cargo run --release -p dregg-sig-cli --example pq_address_and_policy
```

`crates/agg/examples/mock_ethereum_beam.rs` and `mock_solana_alpenglow.rs` are single-host consensus harnesses with explicit network models. The GPU prover is selected with `--features vulkan` and `DREGG_SIG_ACCEL=vulkan`. Stateful CLI vaults require `--anchor-dir <dir>` on a disjoint device, `--anchor-tpm-nv <index>` or `--anchor-vmgenid`; use `--ephemeral-unanchored` for disposable test keys.

## Tests

Run a filtered set: the full suites take hours of CPU and tens of GB.

```sh
cargo test --release -p dregg-sig-core --features std fips205::
cargo test --release -p dregg-sig-agg --test cshake_proof_bytes_kat
```

`fuzz/` holds eight libFuzzer targets for the wire decoders and verifiers (`cargo fuzz run <target>` from that directory; it is a separate workspace with its own dependencies).

## Origin

dregg-sig started from the Rust crates of `qsag` (commit `cf41f1c` plus that tree's uncommitted crate edits) and is developed independently of it.

- Crates, Rust identifiers, assembly symbols, environment variables and the CLI binary carry the `dregg-sig` name. Data-format identifiers do not: domain-separation tags, wire magics and JSON format strings still read `QSAG.…` / `qsag-…-v1`, because changing them changes every signature, proof, known-answer vector and the precomputed hash midstates in the GPU shaders.
- Not carried over: the Lean proof library and Aeneas extraction, the hardware projects and the paper.
- Removed: the in-process CNF coordinator prototype in `dregg-sig-core` that its own documentation quarantined.

Doc comments that cite `lean/Qsag/…`, `Qsag.<name>` or `paper/qsag.typ` point at material in `qsag`. Those proofs, the constant-time archive screen and the source-hash pins were recorded against `qsag`'s sources and symbol names; none has been re-run on this tree.

## License

Authored by ember arlynx (`<ember@lunar.town>`). Licensed under either [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
