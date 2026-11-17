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

A statement (`OwnershipStatement`) is a legacy claim, a commitment to the target
address (`registry::pq_commitment`: prefix, version, suite, key kind and key
commitment), a 32-byte migration domain, an epoch and a nullifier. The claim, the
nullifier and a SHA-256 chaining value carrying the domain are public inputs of the
relation. The target commitment and the epoch are not inside the relation; they are
bound through the proof transcript, which absorbs the whole canonical statement
encoding and the regime. A proof for one target, domain or epoch does not verify for
another.

| Claim | Witness | Relation | Legacy key |
| --- | --- | --- | --- |
| Bitcoin `HASH160` (P2WPKH, P2PKH with a compressed key) | secp256k1 key `k` | `1 <= k < n`, `HASH160(compressed([k]G)) = h` | hidden |
| Ethereum address | secp256k1 key `k` | `1 <= k < n`, `Keccak256(x \|\| y)[12..] = a` | hidden |
| Ed25519 public key | RFC 8032 seed | `[clamp(SHA512(seed)[..32])]B = A` | revealed |
| BIP-32 secp256k1 public key | master seed, 16 to 64 bytes | the key at `m / path` has public key `P`; at most 10 levels | revealed |

The nullifier is `SHA256(tag || 00 00 || curve || domain || scalar)` with the signing
scalar of the legacy key, so one legacy key has one nullifier per domain whichever
statement migrates it.

### Hidden-key statements

The Bitcoin and Ethereum statements prove knowledge of the signing scalar. They mean
something only while the public key is not known to an attacker who can compute
discrete logarithms: once the key has appeared on chain (any spend from the address, or
address reuse), such an attacker computes `k` and can produce the same proof. These
statements are for credentials whose public key has never been published.

Both commit to a 160-bit value. Finding some key whose public key hashes to a given
160-bit address is a preimage search of about `2^160` classical and about `2^80`
quantum (Grover) evaluations of a scalar multiplication and a hash. No proof system
raises that ceiling: it belongs to the address format. A second key found this way
satisfies the relation, with a different nullifier.

The nullifier of a hidden key is a deterministic function of the key and the public
domain. It lets anyone test a guessed key, exactly as the address does.

### Revealed-key statements

The Ed25519 and BIP-32 statements take a hash preimage as the witness: the RFC 8032
seed, or the BIP-32 master seed. An attacker who computes the signing scalar from the
public key still has to invert SHA-512, or HMAC-SHA512 along the derivation path, to
satisfy them. They apply only to keys that were derived this way and whose seed the
holder still has: an Ed25519 key that was generated as a bare scalar, or a secp256k1
key that did not come from a BIP-32 seed, has no such witness.

What they establish is provenance from a seed, not secrecy of anything public. The
nullifier of a revealed key is computable by anyone who can compute its discrete
logarithm; it is an identifier, and registering it still needs a proof.

BIP-39 is outside the relation. The witness is the BIP-32 master seed, which for a
BIP-39 wallet is the 64-byte output of PBKDF2 over the mnemonic and passphrase. That
derivation is not proved: the holder computes the seed first, and anyone who holds the
seed can prove without knowing the mnemonic. The seed length and the derivation path
are public; chain codes and every key along the path stay in the witness.

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

Measured with `dregg-sig migrate` (Apple M-series laptop, development profile; `prove`
includes verifying the proof before it is written):

| Statement | Proof bytes | Prove | Verify |
| --- | ---: | ---: | ---: |
| Bitcoin `HASH160` | 512,717 | 1.6 s | 0.4 s |
| Ethereum address | 530,765 | 1.5 s | 0.4 s |
| Ed25519 seed | 513,197 | 1.2 s | 0.3 s |
| BIP-32, `m/0'` | 551,245 | 2.7 s | 0.6 s |
| BIP-32, `m/44'/0'/0'/0/0` | 922,301 | 9.5 s | 1.8 s |
| BIP-32, ten unhardened levels | 949,726 | 22.6 s | 4.2 s |

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
  the same credential in another domain is refused (`LegacyConflict`). A BIP-32 public
  key is indexed under its `HASH160`, the identifier of the hidden-key Bitcoin statement
  for that key. Identifiers are per commitment kind: the Ethereum address and the
  Bitcoin `HASH160` of one secp256k1 key are different identifiers, and it is their
  common nullifier that stops a second migration in the same domain. In two different
  domains they are not connected.
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
