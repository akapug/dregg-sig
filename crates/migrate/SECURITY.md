# Migration security scope

`dregg-sig-migrate` lets the holder of a legacy credential state "this post-quantum
address is mine" in a way a verifier can check without learning the legacy secret. It
has three parts: ownership statements and their proofs (`hem::relations`), a durable
one-way registry of accepted migrations (`hem::registry`), and work towards proving
from a secret-shared witness (`hem::collab`).

The earlier proof system of this crate (438-repetition ZKBoo, with a replicated and an
authenticated distributed prover, and Pallas and BLS12-381 relations) has been removed.
Its proofs (`qsag-migration-proof-v1`) are not accepted by anything in this tree.

## What a proof shows, and what it does not

A valid proof shows that whoever made it knew a secret behind the legacy credential and
chose the target address, the migration domain and the epoch of the statement.

It does not show that the prover is the rightful owner: anyone who holds the secret can
prove. It does not disable the legacy key: a migrated Bitcoin or Ethereum key still
signs valid legacy transactions until the chain itself stops accepting them. It does not
prevent a second migration of the same credential to another address: two proofs for
two targets are both valid. Disabling legacy spending is the chain's job; refusing the
second migration is the job of whatever records migrations, here the registry. A
verifier that only checks proofs and keeps no state has neither property.

## Statements

A statement (`OwnershipStatement`) is a lock, a key source, the on-chain credential, a
commitment to the target address (`registry::pq_commitment`: prefix, version, suite,
key kind and key commitment), a 32-byte migration domain, an epoch and a nullifier. The
credential, the nullifier and a SHA-256 chaining value carrying the domain and the
credential identifier are public inputs of the relation. The target commitment and the
epoch are not inside the relation; they are bound through the proof transcript, which
absorbs the whole canonical statement encoding and the regime. A proof for one target,
domain or epoch does not verify for another.

The lock says how the chain derives the credential from a public key:

| Lock | Credential |
| --- | --- |
| `P2pkh` | `HASH160(compressed key)` (P2PKH, P2WPKH) |
| `P2pkhUncompressed` | `HASH160(04 \|\| x \|\| y)` |
| `P2shP2wpkh` | `HASH160(00 14 \|\| HASH160(compressed key))` |
| `Ethereum` | `Keccak256(x \|\| y)[12..]` |
| `TaprootKeyPath` | x of `lift_x(P) + H_TapTweak(x(P)) G` (BIP-86) |
| `TaprootScriptTree` | x of `lift_x(P) + H_TapTweak(x(P) \|\| root) G`, the merkle root in the witness |
| `Ed25519` | the public key |
| `BlsWithdrawal` | `00 \|\| SHA256(compressed G1 key)[1..]` |

The key source says what the prover knows:

| Source | Witness | Mode |
| --- | --- | --- |
| `Secp256k1Key`, `Bls12381Key` | the secret key, in `1..n` | hidden |
| `Ed25519Seed` | the RFC 8032 seed | revealed |
| `Bip32`, seed root | master seed of 16 to 64 bytes (length hidden), path of at most 10 steps | revealed |
| `Bip32`, extended-key root | a private key and its chain code, path | revealed, see below |
| `Slip10` | SLIP-0010 master seed, all-hardened path | revealed |
| `Bip32Ed25519` | a Khovratovich-Law extended private key (96 bytes), public path | revealed, see below |

Any lock of a curve combines with any source of that curve. A path is public, or
hidden up to a public maximum depth (indices, hardened flags and depth in the
witness). `BatchStatement` proves many credentials below one BIP-32 node in one proof;
each entry is the same claim as the corresponding single statement.

### Hidden-key statements

The key-source statements prove knowledge of the signing scalar. They mean something
only while the public key is not known to an attacker who can compute discrete
logarithms: once the key has appeared on chain (any spend from the address, or address
reuse), such an attacker computes `k` and can produce the same proof. These statements
are for credentials whose public key has never been published.

A Taproot output key is always public. The hidden-key Taproot statement is knowledge
of an internal key `k` with `Q = lift_x([k]G) + H_TapTweak(..) G`; the internal key is
under the hash, so the logarithm of `Q` does not give a witness. That statement fails
once the internal key has been published (a script-path spend, an exported extended
public key). With a script tree, the witness also holds the merkle root, which is not
checked against any script.

The 20-byte credentials commit to a 160-bit value. Finding some key whose public key
hashes to a given 160-bit address is a preimage search of about `2^160` classical and
about `2^80` quantum (Grover) evaluations of a scalar multiplication and a hash. No
proof system raises that ceiling: it belongs to the address format.

### Revealed-key statements

The other sources take a hash preimage as the witness. An attacker who computes the
signing scalar from the public key still has to invert SHA-512, or HMAC-SHA512 along
the derivation path, to satisfy them. They apply only to keys that were derived this
way and whose seed the holder still has.

A seed-rooted statement is sound whatever has been published. A statement rooted at an
extended private key (`Bip32Root::ExtendedKey`, and every `Bip32Ed25519` statement) is
sound only while no extended public key at or above its root node has been exported:
the chain code from such an export and the discrete logarithm of the node's public key
are the whole witness. This is the unsoundness of last-step proofs of ePrint 2026/1508
(Proposition 6.1). For the BIP-32 master node the condition is the usual state of a
wallet, and the statement is 87,000 rows smaller. BIP32-Ed25519 has no seed-rooted
form because its deployed root derivations (Cardano Icarus: PBKDF2 with 4096
iterations) are not provable at a usable size.

EIP-2333 seed provenance for BLS keys is not offered: one `derive_child_SK` measures
30.8 million rows and the EIP-2334 withdrawal path has four (123 million rows), beyond
the largest supported commitment.

BIP-39 is outside the relation. The witness is the master seed, which for a BIP-39
wallet is the 64-byte output of PBKDF2 over the mnemonic and passphrase
(`relations::bip39_seed`). Proving that step (about 180 million rows) would add
nothing: the seed is already a secret no public value determines, and whoever holds
the mnemonic holds the seed.

### Nullifier and credential identifier

The registry keeps the credential identifier unique (`Credential::identifier`, a digest
of the credential type and its on-chain bytes), so one on-chain credential migrates
once, whichever statement kind proves it. Two credentials of one key (its `HASH160`
and its Ethereum address) are two identifiers and migrate independently.

The nullifier is `SHA256(tag || kind || 00 00 || domain || identifier || 0^32 ||
secret)`. The secret is the signing key for a hidden-key statement, and seed material
for a revealed-key statement: the inner digest of the master HMAC (BIP-32 from a seed),
the leaf's RFC 8032 seed (Ed25519, SLIP-0010), the leaf's `k_R` (BIP32-Ed25519), the
root chain code (extended-key root). For a revealed key it is therefore not computable
from public keys and discrete logarithms, so an attacker cannot predict or pre-register
it. It cannot also be the same value for a hidden-key statement and a seed statement of
one key: a hidden-key witness is the scalar alone, so a common nullifier would be a
function of the scalar. Those two statements of one credential have different
nullifiers and the same identifier, and the registry refuses the second by the
identifier. The nullifier of a hidden key lets anyone test a guessed key, exactly as
the address does.

## Proof system

Proofs are zk-Hem proofs (`dregg_sig_agg::zk_hem::protocol`) of a relation with
multiplication rows only, over the Hem WHIR commitment, under the regime
`BciksJohnsonQrom128` (wire tag 4): 258, 130, 88 and 66 queries at blowups 4, 16, 64
and 256, a 16-bit proof of work, cSHAKE256 Merkle trees and transcript. The regime's
nominal figure is 272 bits of per-round Fiat-Shamir soundness, 136 bits of single-round
Grover work. That is a per-round query budget, not a composed security bound.

The security status is the one stated in `crates/agg/SECURITY.md` and on
`zk_hem::protocol::prove`, and it applies here without change. Not established:

- a composed simulator for the cell layout and transcript: zero knowledge of the
  complete protocol is argued from masking ingredients, not proved;
- a bound for hiding the unopened salted Stage-0 leaves;
- the proximity loss of the scalar companion batching under the regime's query schedule;
- a concrete knowledge-soundness bound for the composition (masked sumchecks, linear
  batching, companion challenge, WHIR).

In addition, the relations of this crate (the SHA-256, SHA-512, HMAC, RIPEMD-160 and
Keccak gadgets of `hem::hash` and the non-native secp256k1 and Ed25519 arithmetic of
`hem::curve`) are tested against the native references and standard vectors and have
not been formally verified or independently reviewed. Proving is not claimed to be
constant-time; run the prover on a host that is trusted with the secret. The proof
randomness must be uniform and secret: it determines every mask and blinder.

Measured with `hem::relations::tests::measure_ownership_proofs` (22-core x86-64 Linux
host, release profile, regime `BciksJohnsonQrom128`; verification with the relation's
shape cached):

| Statement | Rows | Proof bytes | Prove | Verify |
| --- | ---: | ---: | ---: | ---: |
| P2PKH / P2WPKH, key | 82,107 | 514,348 | 0.5 s | 15 ms |
| P2SH-P2WPKH, key | 114,798 | 514,380 | 0.5 s | 16 ms |
| Ethereum address, key | 141,040 | 532,492 | 0.9 s | 24 ms |
| Taproot key path, key | 99,116 | 513,324 | 0.6 s | 19 ms |
| BLS `0x00` withdrawal credential, key | 87,043 | 512,204 | 0.7 s | 18 ms |
| Ed25519, RFC 8032 seed | 92,598 | 515,340 | 0.5 s | 15 ms |
| Ed25519, SLIP-0010 `m/44'/501'/0'/0'` | 874,274 | 881,076 | 3.3 s | 85 ms |
| Ed25519, BIP32-Ed25519 `m/1852'/1815'/0'/0/0` | 1,423,383 | 925,052 | 6.8 s | 133 ms |
| P2PKH, BIP-32 seed `m/44'/0'/0'/0/0` | 1,103,291 | 923,548 | 6.5 s | 132 ms |
| P2PKH, BIP-32 master extended key, same path | 1,016,363 | 881,236 | 3.8 s | 118 ms |
| P2PKH, BIP-32 seed, hidden path of at most 5 steps | 1,202,820 | 922,652 | 7.2 s | 179 ms |
| Batch of 10, P2PKH, `m/44'/0'/0'/0/i` | 2,628,926 | 949,949 | 14.6 s | 389 ms |

A batch of 100 such addresses is 17,885,276 rows; proving it needs more than 32 GB.

Proof length varies by a few hundred bytes with the Fiat-Shamir queries.

## Registry

`NullifierRegistry` records bindings (nullifier, domain, legacy identifier, target
commitment, epoch, exposure mode) in an append-only authenticated log. It does not
verify proofs; the command line submits a binding only after the proof verified, in the
same process, and submits the verified statement's own binding.

Guarantees, for one registry and one writer at a time:

- A nullifier, once recorded, stays bound to exactly that record. A different binding
  under it is refused (`NullifierConflict`).
- A legacy identifier, once recorded, cannot be recorded under another nullifier, so
  the same credential in another domain, or through another statement kind, is refused
  (`LegacyConflict`). The identifier is per on-chain credential: the P2PKH hash, the
  P2SH script hash, the Ethereum address, the Taproot output key, the Ed25519 key and
  the BLS withdrawal credential of a key are different identifiers and migrate
  independently.
- An identical submission is accepted again and writes nothing. An enrolment reserves
  the binding; the first durable enrolment wins.
- An accepted submission is on disk when the call returns.
- On open, with or without an anchor: any changed byte in a committed record or in the
  header, reordered or substituted records, a log cut below its high-water mark, a log
  copied to another inode and a log under another key are detected.

Not detected without an anchor or a retained checkpoint: the whole log replaced by an
earlier state of itself, and the log deleted and created anew. Both forget migrations
and so reopen the double migration. With an anchor (`--anchor-dir` or a TPM counter in
the command line, an `ExternalMonotoneAnchor` in the library) every append advances an
independent monotone record of the log's length and tip, and a log behind it does not
open. Without one, the checkpoint printed by every registry command, kept outside the
registry's storage and passed back as `--min-checkpoint`, gives the same refusal for
states older than that checkpoint. An anchor on the same device as the registry
protects against restoring the registry directory, not against restoring the device.

The registry is a local store. It is not a consensus system: two registries know
nothing of each other, and a deployment with more than one verifier has to make them
agree by its own means. The legacy chain does not consult it.

In the command line the log key, the anchor key and the registry identifier derive
from one seed in `registry.json`, optionally sealed with a passphrase. Someone who
reads that seed can forge the log. The log key depends on whether the registry was created with an anchor, so editing the
root file to drop the anchor requirement leaves a log that does not authenticate.

## Proving from shares

`hem::collab` is a threshold prover for the zk-Hem relations: a quorum of custodians
holding MAC-authenticated additive shares of an assignment produces a proof
(`ZkHemSplitProof`, one Stage-0 commitment per custodian) that
`hem::collab::verify_threshold_ownership` checks with the ordinary verifier steps. Its
module documentation states the protocol, the corruption bound (all but one member of
the proving quorum, with abort), the argument that a deviating custodian learns only
the abort, which parts of that argument are from the literature and which are claims of
the module, and measured costs. `hem::collab::prep` is its dealerless preprocessing
ceremony; the soundness arguments there are written out, not machine-checked and not
independently reviewed.

Not in this tree: computing the shared assignment from shares of the legacy secret.
`hem::collab::custody` turns `(k, n)` Shamir or XOR custody shares into authenticated
shares of the secret's bits; the remaining variables of a relation (hash and curve
intermediates and their hint variables) have no secure computation here. Until that
exists, a legacy secret held as shares has to be reconstructed in one place to
produce the assignment.
