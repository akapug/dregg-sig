# Aggregation security scope

`zk_hem::protocol::prove` implements committed masking intended for witness privacy.
Its name and the Lean lemmas for individual masking ingredients are not a completed
security argument for this Rust protocol. The following work remains outstanding:

- A composed simulator for this exact cell layout and transcript.
- A bound for hiding unopened salted Stage-0 leaves, beyond the existing coupling.
- The proximity loss of scalar companion batching under the chosen WHIR schedule.
- A concrete knowledge-soundness bound for the complete composition.

These obligations apply to full-shard, blind-credential, multisig and capability
relations using this backend. No proof of these obligations is supplied by the
full-shard change described below. Public Hem and hologram paths are non-hiding.

## Full-shard witness leak and repair

The original parent used `prove_public_hologram`. Its serialized `eval_z` is an
unmasked multilinear evaluation of the parent assignment. Given two complete
candidate child-proof sets with the same committee, message and signer count, an
observer can construct both assignments, replay Fiat–Shamir to recover `ry`, and
compare the two evaluations with `eval_z`. This distinguishes the candidates; it
is not an algorithm for recovering arbitrary signer sets without auxiliary input.

`zk_hem::full_shard::tests::full_shard_candidate_witness_distinguisher` reproduces
this with one child, two committee keys and one signer. Two slots and one child
are the smallest supported full-shard geometry. The pre-fix test required neither
candidate to match and failed with `[false, true]`. The final test retains the
public hologram attack as a positive control and applies the terminal-evaluation
comparison to the committed-mask parent. It reconstructs candidate-consistent
row-mask cells from the public row values first, so random row masks alone cannot
make the comparison appear protected. It then compares the candidate's unmasked
column claim with the transmitted masked terminal claim.

This is regression evidence for that distinguisher on this deterministic fixture,
not a proof of zero knowledge or witness indistinguishability. The final test also
roundtrips both full-shard carriers and rejects their old wire versions.

The relation is compatible with the existing committed-mask path without changing
its constraint semantics:

1. `ConstraintSystem::finish`, including its hologram-aligned layout, appends
   twelve fresh variables and twelve rows of the forms `r * 1 = r`, `1 * r = r`,
   and `r * 2 = 2r`. The other constraints do not reference these variables.
2. `protocol::prove` overwrites these cells. Its rank check certifies the local
   map from these pads to the three disclosed row evaluations at the sampled
   point. The row sumcheck itself also receives a committed separable mask.
3. The column sumcheck receives its own committed mask. Its final claim is
   `M(rx, ry) Z(ry) + rho2 g2(ry)`; neither `Z(ry)` nor `g2(ry)` is sent.
4. The mask checks, public inputs and terminal claim are batched into a linear
   functional. Four companion tables, opening blinders and salted leaves use the
   existing `protocol::prove` machinery. Their composed analysis remains subject
   to the obligations above.

The public hologram's verifier expects an unmasked terminal claim and standalone
`eval_z` opening. Merely randomizing its assignment or hiding the `eval_z` field
would not implement the masked checks. The selected repair uses the existing
full-shape masked verifier instead: verification scans the relation matrices,
and no hologram is compiled or retained during full-shard setup. A sublinear
masked hologram verifier would require an additional protocol design.

Compatibility changes: the parent payload is now `ZkHemProof`; inner wire magic
is `QSAGFSM2`, outer wire magic is `QSAGFSA2`, and the parent statement label is
`QSAG.FULL.SHARD.MERGE/v2`. Old non-hiding carriers are rejected. The full-shard
relation's obsolete `hologram()` and `verifier_key()` accessors were removed;
`shape()` supplies the verifier relation. Other hologram APIs remain available
and explicitly non-hiding. A rank-deficient mask challenge is reported as
`FullShardError::MaskRankDeficient`, allowing retry with a fresh secret seed.

## Smallest-fixture measurement and validation

One real child, two committee slots, one signer, JortsPoseidon2 height 6, using
`Poseidon2Cdhz25ZeroPowQrom128` (107 nominal Grover bits, `Q + 1 <= 2^40`). The
relation has 1,719,058 variables and 2,097,152 padded rows. Measurements are single
runs on hbox under `SWARM_MEM_MAX=16G swarm-build`, release Rust 1.99.1; they are
not general performance bounds. Both rows below come from the same final test run.
Proof sizes include the eight-byte parent framing. Proving timings include
serialization, exclude relation/hologram setup, and the masked wrapper also
reconstructs its assignment.

| Parent path | Serialized bytes | Prove seconds | Verify seconds |
| --- | ---: | ---: | ---: |
| Public hologram control | 1,368,818 | 47.210 | 0.020 |
| Committed-mask full-shard parent | 780,091 | 6.864 | 0.127 |

Full-shard setup without compiling a hologram took 1.843 seconds. The original
pre-fix run, including hologram setup, took 16.126 seconds to set up and produced
1,367,922 bytes in 51.982 seconds. Its evaluation test failed with `[false, true]`;
the final test passes, including the public positive control and both versioned
wire roundtrips. The public control in the final run uses the new statement label,
so its Fiat–Shamir points and Merkle proof size differ slightly from the pre-fix run.

The exact red/green command was:

```sh
SWARM_MEM_MAX=16G swarm-build cargo test --release -p dregg-sig-agg --lib \
  zk_hem::full_shard::tests::full_shard_candidate_witness_distinguisher -- --exact --nocapture
```

Logs: `/var/tmp/dregg-sig-astra-aggclaims-red.log` and
`/var/tmp/dregg-sig-astra-aggclaims-green.log` on hbox. The test was written and
executed against the original non-hiding prover before changing its production
path. Its observer adapter was then updated for the masked wire transcript, with
the original observer retained as a positive control. No other new unit test was
introduced in this change.

## WHIR profile policy

`WhirSecurityRegime::is_accepted_aggregate_profile()` reports verifier policy
membership. It is not a 128-bit security floor. The historically named CDHZ25
`Qrom128` profiles have these nominal single-round Grover work estimates:

| Profiles (wire tags) | Nominal work bits | Bounded-query assumption |
| --- | ---: | --- |
| CDHZ25 with 16-bit PoW (5, 7, 10) | 108 | `Q <= 2^38` |
| CDHZ25 without PoW (6, 8) | 107 | `Q + 1 <= 2^40` |

The former combines 200 query-target bits with 16 PoW bits, then divides by two;
the latter divides 214 by two. `is_bounded_query_profile()` identifies these
profiles; `qrom_grover_round_bits()` returns their nominal estimates. Acceptance
is unchanged by the rename. Existing `pcs::pcs_unit_tests::exact_regime_ladder`
asserts the estimates and policy decisions together. None of these per-round
estimates establishes a composed authorization-security bound.

## Claims corrected in this audit

| Location | Correction |
| --- | --- |
| Root `README.md`, aggregation row and credential row’s aggregation reference | Removed unqualified zero-knowledge claim and the implication that all recursion uses masking; described witnessed policies rather than guaranteed policy privacy. |
| `src/lib.rs`, committed-mask relations section | Qualified privacy/security status and corrected the list of backend users. |
| `src/zk_hem.rs`, module documentation | Distinguished Lean masking ingredients from the unproved composition. |
| `src/zk_hem/protocol.rs`, module and `ZkHemProof` documentation | Qualified zero-knowledge wording and scoped uniformity claims to ideal ingredient sampling. |
| `src/zk_hem/protocol.rs`, `prove_public_hologram` | Explicitly documented the unmasked row values and `eval_z` disclosure. |
| `src/zk_hem/full_shard.rs`, module, relation, proof and prover documentation | Described committed masks, full-relation verification, secret-seed requirement and remaining bounds. |
| `src/recursive.rs`, `SuccinctFullShardAggregate` and its prover | Replaced unconditional signer hiding with the actual masking/security scope and seed requirement. |
| `src/zk_hem/recursive_whir.rs`, `FixedPathWhirProof` and `commit_for_recursion` | Distinguished omitted witness serialization from hiding; public merge remains non-hiding. |
| `src/zk_hem/blind_vc.rs`, module documentation | Bounded selective-disclosure expectations by backend limitations. |
| `src/zk_hem/multisig.rs`, module documentation | Described witnessed policy/active bits rather than guaranteed secrecy. |
| `src/zk_hem/capability.rs`, module, presentation-tag function and proof documentation | Removed unconditional hiding, zero-knowledge and unlinkability claims; specified deterministic per-context tags. |
| `src/zk_hem/capability/offline.rs`, delegated relation documentation | Qualified the presentation's masking/security scope. |
| `src/pcs.rs`, regime, bounded variants and policy predicates | Gave 108/107-bit estimates and query caps; renamed policy membership predicates. |
| `src/lib.rs`, `src/arithmetize.rs`, `AFFINE_PROTOCOL.md`, profile-policy descriptions | Replaced generic QROM-128-floor language with the actual acceptance policy. |
| `src/sponge.rs`, `keccak_p1600_12` | Removed unsupported implication of composed WHIR QROM security from the permutation description. |

## Validation commands

The following existing tests also passed on hbox using the same release binary.
Each was run separately with
`SWARM_MEM_MAX=16G swarm-build cargo test --release -p dregg-sig-agg --lib <name> -- --exact --nocapture`:

- `zk_hem::full_shard::tests::full_shard_merge_end_to_end_and_tamper_rejection`
- `recursive::tests::succinct_full_shard_aggregate_needs_no_child_and_binds_its_statement`
- `zk_hem::full_shard::tests::variable_height_jorts_recursive_shard_and_masked_merge`
- `pcs::pcs_unit_tests::exact_regime_ladder` (also passed on pre-fix source,
  establishing the old predicate's accepted 107/108-bit profiles)

Local checks passed:

```sh
cargo check -p dregg-sig-agg --all-features
cargo check -p dregg-sig-agg --no-default-features
cargo check -p dregg-sig-agg --tests --all-features
cargo check --manifest-path fuzz/Cargo.toml --bin fuzz_hologram_and_subtree_decode --bin fuzz_whir_agg_verify
cargo doc -p dregg-sig-agg --no-deps
```

Rustdoc completed with existing unresolved/private intra-doc-link warnings. No
fuzz campaign was run; the fuzz targets were adapted and compile-checked.
No CLI or quorum callers required changes. Source edits stay within `crates/agg`,
the two affected fuzz targets, and root README aggregation-related text.
