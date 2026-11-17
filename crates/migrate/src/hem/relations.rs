//! Ownership statements over zk-Hem and their proofs.
//!
//! A statement says: the prover knows the secret behind a legacy credential, and binds
//! that knowledge to a post-quantum address commitment, a migration domain and an epoch.
//! Four legacy claims are supported ([`LegacyClaim`]):
//!
//! | claim | secret | relation |
//! |---|---|---|
//! | Bitcoin `HASH160` (hidden key) | scalar `k` | `1 <= k < n`, `HASH160(compressed([k]G)) = h` |
//! | Ethereum address (hidden key) | scalar `k` | `1 <= k < n`, `Keccak256(x \|\| y)[12..] = a` |
//! | Ed25519 public key (revealed) | RFC 8032 seed | `[clamp(SHA512(seed)[..32])]B = A` |
//! | BIP-32 secp256k1 public key (revealed) | master seed | `m / path` has public key `P` |
//!
//! The two revealed-key relations take a hash preimage as their witness (the seed), so a
//! party that can compute discrete logarithms of the public key still cannot satisfy them.
//!
//! # What is public
//!
//! The legacy value, the nullifier and a SHA-256 chaining value that carries the migration
//! domain are public inputs of the relation, one input per bit (public inputs are Boolean
//! because the verifier supplies them, so they cost no row). The post-quantum commitment
//! and the epoch are not used inside the relation; they are bound through the transcript,
//! which absorbs [`OwnershipStatement::to_bytes`] and the regime. For the BIP-32 claim the
//! seed length and the derivation path are public and select the relation; chain codes and
//! all keys along the path stay secret.
//!
//! # Nullifier
//!
//! `SHA256(tag || 00 00 || curve || domain || secret)` with the 29-byte tag
//! `QSAG.MIGRATE.HEM.NULLIFIER/v1`, so that `tag .. domain` is exactly one block. The
//! verifier computes the chaining value after that block ([`nullifier_midstate`]) and the
//! relation runs the one remaining compression. `secret` is the signing scalar: the
//! 32-byte big-endian secp256k1 key, or the 32-byte little-endian clamped Ed25519 scalar.
//! Both are unique for their public key, so one legacy key has one nullifier per domain
//! whichever statement is used to migrate it. For a revealed key the nullifier is
//! computable by anyone who can compute the discrete logarithm; it is an identifier, not a
//! secret, and registering it still needs a proof.
//!
//! # Relations contain multiplication rows only
//!
//! No S-box rows and no Poseidon2, so the collaborative prover of [`super::collab`] can
//! run them; [`synthesize_ownership`] is its entry point.

use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;

use dregg_sig_accel::keccak::keccak256 as keccak256_native;
use dregg_sig_accel::sha2 as sha2_native;
use dregg_sig_agg::field::Goldilocks;
use dregg_sig_agg::pcs::WhirSecurityRegime;
use dregg_sig_agg::zk_hem::protocol::{self, ZkHemError, ZkHemProof};
use dregg_sig_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape};

use super::curve::{
    Element, Lazy, Modulus, ed25519_clamp, ed25519_fixed_base_mul, secp256k1_enforce_scalar_range,
    secp256k1_fixed_base_mul,
};
use super::hash::{
    Word, alloc_bits, const_bits, hash160, hmac_sha512, keccak256, pack_bits, sha256_from_midstate,
    sha256_midstate, sha512,
};
use crate::ed25519_ct::public_key_from_clamped_scalar;
use crate::legacy::LegacyCommitmentKind;
use crate::secp256k1_ct::{
    SecpPoint, secp_scalar_add_mod_n, secp_scalar_is_canonical, secp_scalar_is_valid_nonzero,
};

type F = Goldilocks;

const NULLIFIER_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.NULLIFIER/v1";
const STATEMENT_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.OWNERSHIP/v1";
const PROOF_MAGIC: &[u8; 8] = b"QSHEMOW1";

/// First hardened child index.
pub const BIP32_HARDENED: u32 = 0x8000_0000;
/// Longest derivation path a statement may carry.
pub const MAX_BIP32_DEPTH: usize = 10;
/// Master seed lengths BIP-32 admits, in bytes.
pub const BIP32_SEED_BYTES: core::ops::RangeInclusive<usize> = 16..=64;

fn wipe(bytes: &mut [u8]) {
    dregg_sig_asm::volatile_fill(bytes, 0);
}

// ============================================================================
// Native reference functions
// ============================================================================

/// The curve of the signing scalar a nullifier is derived from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum NullifierCurve {
    Secp256k1 = 1,
    Ed25519 = 2,
}

/// The one-block prefix `tag || 00 00 || curve || domain` of the nullifier preimage.
pub fn nullifier_prefix(curve: NullifierCurve, migration_domain: &[u8; 32]) -> [u8; 64] {
    let mut out = [0u8; 64];
    out[..29].copy_from_slice(NULLIFIER_TAG);
    out[31] = curve as u8;
    out[32..].copy_from_slice(migration_domain);
    out
}

/// SHA-256 chaining value after [`nullifier_prefix`]: the public input through which the
/// migration domain enters a relation.
pub fn nullifier_midstate(curve: NullifierCurve, migration_domain: &[u8; 32]) -> [u32; 8] {
    sha256_midstate(&nullifier_prefix(curve, migration_domain))
}

/// The nullifier of a signing scalar (big-endian for secp256k1, the little-endian clamped
/// scalar for Ed25519) in a migration domain.
pub fn migration_nullifier(
    curve: NullifierCurve,
    scalar: &[u8; 32],
    migration_domain: &[u8; 32],
) -> [u8; 32] {
    let mut preimage = [0u8; 96];
    preimage[..64].copy_from_slice(&nullifier_prefix(curve, migration_domain));
    preimage[64..].copy_from_slice(scalar);
    let out = sha2_native::sha256(&preimage);
    wipe(&mut preimage);
    out
}

/// SEC1 compressed public key of a big-endian secp256k1 secret key; `None` unless
/// `1 <= k < n`.
pub fn secp256k1_public_key(key_be: &[u8; 32]) -> Option<[u8; 33]> {
    secp_scalar_is_valid_nonzero(key_be)
        .then(|| SecpPoint::generator_mul_ct(key_be).to_compressed_bytes())
        .flatten()
}

/// `HASH160` of the compressed public key (P2PKH and P2WPKH).
pub fn bitcoin_hash160(key_be: &[u8; 32]) -> Option<[u8; 20]> {
    secp256k1_public_key(key_be).map(|pk| sha2_native::hash160(&pk))
}

/// Ethereum address: the last 20 bytes of `Keccak256(x || y)`.
pub fn ethereum_address(key_be: &[u8; 32]) -> Option<[u8; 20]> {
    if !secp_scalar_is_valid_nonzero(key_be) {
        return None;
    }
    let xy = SecpPoint::generator_mul_ct(key_be).to_uncompressed_64()?;
    let digest = keccak256_native(&xy);
    digest[12..].try_into().ok()
}

/// RFC 8032 secret scalar of a seed: the clamped first half of `SHA512(seed)`,
/// little-endian.
pub fn ed25519_clamped_scalar(seed: &[u8; 32]) -> [u8; 32] {
    let mut digest = sha2_native::sha512(seed);
    let mut scalar = [0u8; 32];
    scalar.copy_from_slice(&digest[..32]);
    wipe(&mut digest);
    scalar[0] &= 0xf8;
    scalar[31] &= 0x7f;
    scalar[31] |= 0x40;
    scalar
}

/// RFC 8032 public key of a seed.
pub fn ed25519_public_key(seed: &[u8; 32]) -> [u8; 32] {
    let mut scalar = ed25519_clamped_scalar(seed);
    let out = public_key_from_clamped_scalar(&scalar);
    wipe(&mut scalar);
    out
}

/// A BIP-32 extended private key without its metadata. Erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub struct Bip32Node {
    pub private_key: [u8; 32],
    pub chain_code: [u8; 32],
}

impl Drop for Bip32Node {
    fn drop(&mut self) {
        wipe(&mut self.private_key);
        wipe(&mut self.chain_code);
    }
}

impl Bip32Node {
    fn split(mut i: [u8; 64]) -> ([u8; 32], [u8; 32]) {
        let (mut left, mut right) = ([0u8; 32], [0u8; 32]);
        left.copy_from_slice(&i[..32]);
        right.copy_from_slice(&i[32..]);
        wipe(&mut i);
        (left, right)
    }

    /// The compressed public key of this node.
    pub fn public_key(&self) -> [u8; 33] {
        secp256k1_public_key(&self.private_key).expect("node keys are valid scalars")
    }
}

/// BIP-32 master key of a seed; `None` when `I_L` is zero or not below the group order.
pub fn bip32_master(seed: &[u8]) -> Option<Bip32Node> {
    let (private_key, chain_code) =
        Bip32Node::split(sha2_native::hmac_sha512(b"Bitcoin seed", seed));
    let node = Bip32Node {
        private_key,
        chain_code,
    };
    secp_scalar_is_valid_nonzero(&node.private_key).then_some(node)
}

/// BIP-32 private child derivation (`CKDpriv`); `None` when `I_L` is not below the group
/// order or the child key is zero.
pub fn bip32_child(parent: &Bip32Node, index: u32) -> Option<Bip32Node> {
    let mut data = [0u8; 37];
    if index >= BIP32_HARDENED {
        data[1..33].copy_from_slice(&parent.private_key);
    } else {
        data[..33].copy_from_slice(&parent.public_key());
    }
    data[33..].copy_from_slice(&index.to_be_bytes());
    let (mut tweak, chain_code) =
        Bip32Node::split(sha2_native::hmac_sha512(&parent.chain_code, &data));
    wipe(&mut data);
    let in_range = secp_scalar_is_canonical(&tweak);
    let node = Bip32Node {
        private_key: secp_scalar_add_mod_n(&tweak, &parent.private_key),
        chain_code,
    };
    wipe(&mut tweak);
    (in_range && secp_scalar_is_valid_nonzero(&node.private_key)).then_some(node)
}

/// The node at `m / path`.
pub fn bip32_derive(seed: &[u8], path: &[u32]) -> Option<Bip32Node> {
    path.iter()
        .try_fold(bip32_master(seed)?, |node, &index| bip32_child(&node, index))
}

// ============================================================================
// Statements
// ============================================================================

/// What a statement claims about a legacy credential.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LegacyClaim {
    /// Hidden key: `HASH160` of the compressed secp256k1 public key.
    BitcoinHash160([u8; 20]),
    /// Hidden key: Ethereum address of the secp256k1 public key.
    EthereumAddress([u8; 20]),
    /// Revealed key: an Ed25519 public key whose RFC 8032 seed the prover knows.
    Ed25519Seed { public_key: [u8; 32] },
    /// Revealed key: the compressed secp256k1 public key at `m / path` of a master seed of
    /// `seed_len` bytes that the prover knows.
    Bip32Secp256k1 {
        public_key: [u8; 33],
        seed_len: u8,
        path: Vec<u32>,
    },
}

/// The kind of claim to derive from a witness (see [`OwnershipStatement::derive`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClaimKind {
    BitcoinHash160,
    EthereumAddress,
    Ed25519Seed,
    Bip32Secp256k1 { path: Vec<u32> },
}

/// What selects a relation: the claim without its values.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Relation {
    BitcoinHash160,
    EthereumAddress,
    Ed25519Seed,
    Bip32Secp256k1 { seed_len: usize, path: Vec<u32> },
}

impl Relation {
    fn claim_bytes(&self) -> usize {
        match self {
            Self::BitcoinHash160 | Self::EthereumAddress => 20,
            Self::Ed25519Seed => 32,
            Self::Bip32Secp256k1 { .. } => 33,
        }
    }

    fn secret_bytes(&self) -> usize {
        match self {
            Self::Bip32Secp256k1 { seed_len, .. } => *seed_len,
            _ => 32,
        }
    }

    fn curve(&self) -> NullifierCurve {
        match self {
            Self::Ed25519Seed => NullifierCurve::Ed25519,
            _ => NullifierCurve::Secp256k1,
        }
    }

    /// A valid secret of the right length, for building the shape without a witness.
    fn placeholder_secret(&self) -> Vec<u8> {
        let mut secret = vec![0u8; self.secret_bytes()];
        if matches!(self, Self::BitcoinHash160 | Self::EthereumAddress) {
            secret[31] = 1;
        }
        secret
    }
}

impl LegacyClaim {
    /// Wire tag of the claim kind.
    pub fn tag(&self) -> u8 {
        match self {
            Self::BitcoinHash160(_) => 1,
            Self::EthereumAddress(_) => 2,
            Self::Ed25519Seed { .. } => 3,
            Self::Bip32Secp256k1 { .. } => 4,
        }
    }

    /// Whether the legacy public key itself is public (`KeyExposure::Revealed`).
    pub fn key_is_revealed(&self) -> bool {
        matches!(self, Self::Ed25519Seed { .. } | Self::Bip32Secp256k1 { .. })
    }

    /// The legacy commitment the registry indexes. A BIP-32 public key is recorded under
    /// its Bitcoin `HASH160`, the same identifier as a hidden-key migration of that key.
    pub fn legacy_commitment(&self) -> LegacyCommitmentKind {
        match self {
            Self::BitcoinHash160(h) => LegacyCommitmentKind::BitcoinHash160(*h),
            Self::EthereumAddress(a) => LegacyCommitmentKind::EthereumKeccak20(*a),
            Self::Ed25519Seed { public_key } => LegacyCommitmentKind::Slip0010Ed25519(*public_key),
            Self::Bip32Secp256k1 { public_key, .. } => {
                LegacyCommitmentKind::BitcoinHash160(sha2_native::hash160(public_key))
            }
        }
    }

    fn value(&self) -> &[u8] {
        match self {
            Self::BitcoinHash160(v) | Self::EthereumAddress(v) => v,
            Self::Ed25519Seed { public_key } => public_key,
            Self::Bip32Secp256k1 { public_key, .. } => public_key,
        }
    }

    fn relation(&self) -> Option<Relation> {
        Some(match self {
            Self::BitcoinHash160(_) => Relation::BitcoinHash160,
            Self::EthereumAddress(_) => Relation::EthereumAddress,
            Self::Ed25519Seed { .. } => Relation::Ed25519Seed,
            Self::Bip32Secp256k1 {
                public_key,
                seed_len,
                path,
            } => {
                let seed_len = usize::from(*seed_len);
                if !BIP32_SEED_BYTES.contains(&seed_len)
                    || path.len() > MAX_BIP32_DEPTH
                    || !matches!(public_key[0], 2 | 3)
                {
                    return None;
                }
                Relation::Bip32Secp256k1 {
                    seed_len,
                    path: path.clone(),
                }
            }
        })
    }
}

/// The secret behind a legacy credential. Erased on drop.
#[derive(Clone, PartialEq, Eq)]
pub enum OwnershipWitness {
    /// Big-endian secp256k1 secret key.
    Secp256k1Key([u8; 32]),
    /// RFC 8032 Ed25519 seed.
    Ed25519Seed([u8; 32]),
    /// BIP-32 master seed, 16 to 64 bytes.
    Bip32Seed(Vec<u8>),
}

impl OwnershipWitness {
    fn secret(&self) -> &[u8] {
        match self {
            Self::Secp256k1Key(k) => k,
            Self::Ed25519Seed(s) => s,
            Self::Bip32Seed(s) => s,
        }
    }
}

impl Drop for OwnershipWitness {
    fn drop(&mut self) {
        match self {
            Self::Secp256k1Key(k) => wipe(k),
            Self::Ed25519Seed(s) => wipe(s),
            Self::Bip32Seed(s) => wipe(s),
        }
    }
}

/// The claim a witness supports and the signing scalar its nullifier is derived from.
/// `None` when the witness is of the wrong type or is not a valid secret for `kind`.
fn evaluate(kind: &ClaimKind, witness: &OwnershipWitness) -> Option<(LegacyClaim, [u8; 32])> {
    match (kind, witness) {
        (ClaimKind::BitcoinHash160, OwnershipWitness::Secp256k1Key(k)) => {
            Some((LegacyClaim::BitcoinHash160(bitcoin_hash160(k)?), *k))
        }
        (ClaimKind::EthereumAddress, OwnershipWitness::Secp256k1Key(k)) => {
            Some((LegacyClaim::EthereumAddress(ethereum_address(k)?), *k))
        }
        (ClaimKind::Ed25519Seed, OwnershipWitness::Ed25519Seed(seed)) => Some((
            LegacyClaim::Ed25519Seed {
                public_key: ed25519_public_key(seed),
            },
            ed25519_clamped_scalar(seed),
        )),
        (ClaimKind::Bip32Secp256k1 { path }, OwnershipWitness::Bip32Seed(seed)) => {
            if !BIP32_SEED_BYTES.contains(&seed.len()) || path.len() > MAX_BIP32_DEPTH {
                return None;
            }
            let node = bip32_derive(seed, path)?;
            Some((
                LegacyClaim::Bip32Secp256k1 {
                    public_key: node.public_key(),
                    seed_len: seed.len() as u8,
                    path: path.clone(),
                },
                node.private_key,
            ))
        }
        _ => None,
    }
}

/// Public statement of an ownership proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnershipStatement {
    pub claim: LegacyClaim,
    /// Commitment to the post-quantum address the credential migrates to
    /// (`registry::pq_commitment`). Chosen by the caller; not derived from the secret.
    pub pq_commitment: [u8; 32],
    /// Replay domain of the migration campaign.
    pub migration_domain: [u8; 32],
    pub epoch: u64,
    /// [`migration_nullifier`] of the signing scalar in `migration_domain`.
    pub nullifier: [u8; 32],
}

impl OwnershipStatement {
    /// The statement a holder derives from its secret. `None` when the witness does not
    /// fit `kind` or is not a valid secret (a scalar outside `1..n`, a seed of the wrong
    /// length, a path BIP-32 rejects or one longer than [`MAX_BIP32_DEPTH`]).
    pub fn derive(
        kind: &ClaimKind,
        witness: &OwnershipWitness,
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        let (claim, mut scalar) = evaluate(kind, witness)?;
        let curve = claim.relation()?.curve();
        let nullifier = migration_nullifier(curve, &scalar, &migration_domain);
        wipe(&mut scalar);
        Some(Self {
            claim,
            pq_commitment,
            migration_domain,
            epoch,
            nullifier,
        })
    }

    /// Whether the claim's parameters are within the supported ranges.
    pub fn is_well_formed(&self) -> bool {
        self.claim.relation().is_some()
    }

    /// Canonical encoding; also the bytes the proof transcript absorbs.
    ///
    /// `tag(29) || kind || exposure || epoch(8, BE) || domain(32) || pq(32) || nullifier(32)
    /// || claim`, where the claim is its 20, 32 or 33 value bytes, followed for BIP-32 by
    /// `seed_len || depth || depth * index(4, BE)`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(200);
        out.extend_from_slice(STATEMENT_TAG);
        out.push(self.claim.tag());
        out.push(u8::from(self.claim.key_is_revealed()));
        out.extend_from_slice(&self.epoch.to_be_bytes());
        out.extend_from_slice(&self.migration_domain);
        out.extend_from_slice(&self.pq_commitment);
        out.extend_from_slice(&self.nullifier);
        out.extend_from_slice(self.claim.value());
        if let LegacyClaim::Bip32Secp256k1 { seed_len, path, .. } = &self.claim {
            out.push(*seed_len);
            out.push(path.len() as u8);
            for index in path {
                out.extend_from_slice(&index.to_be_bytes());
            }
        }
        out
    }

    /// Strict inverse of [`Self::to_bytes`]: rejects unknown kinds, an exposure byte that
    /// does not match the kind, parameters outside the supported ranges and any byte
    /// missing or left over.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut rest = bytes.strip_prefix(STATEMENT_TAG.as_slice())?;
        let mut take = |n: usize| -> Option<&[u8]> {
            let (head, tail) = rest.split_at_checked(n)?;
            rest = tail;
            Some(head)
        };
        let (kind, exposure) = (take(1)?[0], take(1)?[0]);
        let epoch = u64::from_be_bytes(take(8)?.try_into().ok()?);
        let migration_domain: [u8; 32] = take(32)?.try_into().ok()?;
        let pq_commitment: [u8; 32] = take(32)?.try_into().ok()?;
        let nullifier: [u8; 32] = take(32)?.try_into().ok()?;
        let claim = match kind {
            1 => LegacyClaim::BitcoinHash160(take(20)?.try_into().ok()?),
            2 => LegacyClaim::EthereumAddress(take(20)?.try_into().ok()?),
            3 => LegacyClaim::Ed25519Seed {
                public_key: take(32)?.try_into().ok()?,
            },
            4 => {
                let public_key: [u8; 33] = take(33)?.try_into().ok()?;
                let (seed_len, depth) = (take(1)?[0], take(1)?[0]);
                let path = take(4 * usize::from(depth))?
                    .chunks_exact(4)
                    .map(|c| u32::from_be_bytes([c[0], c[1], c[2], c[3]]))
                    .collect();
                LegacyClaim::Bip32Secp256k1 {
                    public_key,
                    seed_len,
                    path,
                }
            }
            _ => return None,
        };
        let statement = Self {
            claim,
            pq_commitment,
            migration_domain,
            epoch,
            nullifier,
        };
        (rest.is_empty()
            && exposure == u8::from(statement.claim.key_is_revealed())
            && statement.is_well_formed())
        .then_some(statement)
    }

    /// The relation's public inputs, one per bit: the claim value, the nullifier chaining
    /// value (eight words, each least significant bit first), the nullifier. Bytes are
    /// least significant bit first. `None` for a malformed statement.
    pub fn public_inputs(&self) -> Option<Vec<F>> {
        let relation = self.claim.relation()?;
        Some(
            self.public_bits(&relation)
                .into_iter()
                .map(|b| F::from_u64_reduced(u64::from(b)))
                .collect(),
        )
    }

    fn public_bits(&self, relation: &Relation) -> Vec<bool> {
        let byte_bits = |bytes: &[u8]| -> Vec<bool> {
            bytes
                .iter()
                .flat_map(|&b| (0..8).map(move |i| (b >> i) & 1 == 1))
                .collect()
        };
        let mut out = byte_bits(self.claim.value());
        for word in nullifier_midstate(relation.curve(), &self.migration_domain) {
            out.extend((0..32).map(|i| (word >> i) & 1 == 1));
        }
        out.extend(byte_bits(&self.nullifier));
        out
    }

    /// The bytes absorbed by the proof transcript.
    fn transcript(&self, regime: WhirSecurityRegime) -> Vec<u8> {
        let mut out = self.to_bytes();
        out.push(regime as u8);
        out
    }

    /// The exposure mode the registry records for this statement.
    #[cfg(feature = "std")]
    pub fn exposure(&self) -> super::registry::KeyExposure {
        if self.claim.key_is_revealed() {
            super::registry::KeyExposure::Revealed
        } else {
            super::registry::KeyExposure::Hidden
        }
    }

    /// The binding a verified statement asks the registry to record.
    #[cfg(feature = "std")]
    pub fn binding(&self) -> super::registry::MigrationBinding {
        super::registry::MigrationBinding {
            nullifier: self.nullifier,
            migration_domain: self.migration_domain,
            legacy_id: super::registry::legacy_identifier(&self.claim.legacy_commitment()),
            pq_commitment: self.pq_commitment,
            epoch: self.epoch,
            exposure: self.exposure(),
        }
    }
}

// ============================================================================
// Relations
// ============================================================================

/// Reverse the byte order of a byte string: a big-endian integer's bytes become its
/// little-endian bits and back.
fn reverse_bytes(bits: &[Lc]) -> Vec<Lc> {
    bits.chunks(8).rev().flatten().cloned().collect()
}

/// `got = want` for Boolean bit strings, 60 bits per row.
fn pin(cs: &mut ConstraintSystem, got: &[Lc], want: &[Lc]) {
    assert_eq!(got.len(), want.len());
    for (g, w) in got.chunks(60).zip(want.chunks(60)) {
        cs.enforce_equal(&pack_bits(g), &pack_bits(w));
    }
}

/// BIP-32 `k_child = (I_L + k_par) mod n` on little-endian bits, with the rejection rules
/// as constraints: `I_L <= n - 1` and `1 <= k_child <= n - 1`.
fn bip32_child_key(
    cs: &mut ConstraintSystem,
    order: &Modulus,
    tweak_le: &[Lc],
    parent_le: &[Lc],
) -> Vec<Lc> {
    let tweak = Element {
        bytes_le: tweak_le.chunks(8).map(pack_bits).collect(),
        bits_le: tweak_le.to_vec(),
    };
    order.enforce_canonical(cs, &tweak);
    let child = order.reduce(cs, &tweak.lazy().add(&Lazy::from_bits(parent_le)));
    secp256k1_enforce_scalar_range(cs, &child.bits_le);
    child.bits_le
}

/// The key at `m / path` as little-endian bits, from the master seed's byte string.
fn bip32_key(cs: &mut ConstraintSystem, seed: &[Lc], path: &[u32]) -> Vec<Lc> {
    let order = Modulus::secp256k1_order();
    let i = hmac_sha512(cs, &const_bits(b"Bitcoin seed"), seed);
    let mut key = reverse_bytes(&i[..256]);
    secp256k1_enforce_scalar_range(cs, &key);
    let mut chain_code = i[256..].to_vec();
    for &index in path {
        let mut data: Vec<Lc> = if index >= BIP32_HARDENED {
            let mut data = const_bits(&[0]);
            data.extend(reverse_bytes(&key));
            data
        } else {
            let parent = secp256k1_fixed_base_mul(cs, &key);
            parent.compressed_bits().into_iter().flatten().collect()
        };
        data.extend(const_bits(&index.to_be_bytes()));
        let i = hmac_sha512(cs, &chain_code, &data);
        key = bip32_child_key(cs, &order, &reverse_bytes(&i[..256]), &key);
        chain_code = i[256..].to_vec();
    }
    key
}

/// The relation with its assignment, and the number of rows before padding.
fn build(relation: &Relation, public_bits: &[bool], secret: &[u8]) -> (Shape, Vec<F>, usize) {
    assert_eq!(secret.len(), relation.secret_bytes());
    assert_eq!(public_bits.len(), 8 * relation.claim_bytes() + 512);
    let mut cs = ConstraintSystem::new();
    let public: Vec<Lc> = public_bits
        .iter()
        .map(|&b| cs.public_input(F::from_u64_reduced(u64::from(b))).into())
        .collect();
    let (claim, rest) = public.split_at(8 * relation.claim_bytes());
    let (midstate, nullifier) = rest.split_at(256);
    let secret = alloc_bits(&mut cs, secret);

    // The signing scalar as the byte string the nullifier hashes.
    let scalar_bytes = match relation {
        Relation::BitcoinHash160 | Relation::EthereumAddress => {
            let key = reverse_bytes(&secret);
            secp256k1_enforce_scalar_range(&mut cs, &key);
            let public_key = secp256k1_fixed_base_mul(&mut cs, &key);
            if matches!(relation, Relation::BitcoinHash160) {
                let encoding: Vec<Lc> =
                    public_key.compressed_bits().into_iter().flatten().collect();
                let digest = hash160(&mut cs, &encoding);
                pin(&mut cs, &digest, claim);
            } else {
                let encoding: Vec<Lc> = public_key
                    .uncompressed_bits()
                    .into_iter()
                    .flatten()
                    .collect();
                let digest = keccak256(&mut cs, &encoding);
                pin(&mut cs, &digest[96..], claim);
            }
            secret
        }
        Relation::Ed25519Seed => {
            let digest = sha512(&mut cs, &secret);
            let scalar = ed25519_clamp(&digest[..256]);
            let public_key = ed25519_fixed_base_mul(&mut cs, &scalar);
            pin(&mut cs, &public_key.encoding_bits(), claim);
            scalar
        }
        Relation::Bip32Secp256k1 { path, .. } => {
            let key = bip32_key(&mut cs, &secret, path);
            let public_key = secp256k1_fixed_base_mul(&mut cs, &key);
            let encoding: Vec<Lc> = public_key.compressed_bits().into_iter().flatten().collect();
            pin(&mut cs, &encoding, claim);
            reverse_bytes(&key)
        }
    };

    let midstate: Vec<Word> = midstate
        .chunks(32)
        .map(|w| Word::from_bits(w.to_vec()))
        .collect();
    let midstate: &[Word; 8] = midstate.as_slice().try_into().expect("eight words");
    let digest = sha256_from_midstate(&mut cs, midstate, 64, &scalar_bytes);
    pin(&mut cs, &digest, nullifier);

    let rows = cs.num_rows();
    let (shape, assignment) = cs.finish();
    (shape, assignment, rows)
}

fn build_shape(relation: &Relation) -> Shape {
    let public = vec![false; 8 * relation.claim_bytes() + 512];
    let mut secret = relation.placeholder_secret();
    let (shape, mut assignment, _) = build(relation, &public, &secret);
    wipe(&mut secret);
    dregg_sig_asm::volatile_fill(&mut assignment, F::ZERO);
    shape
}

/// Shapes are a pure function of the relation; with `std` the most recent ones are kept.
#[cfg(feature = "std")]
fn shape_of(relation: &Relation) -> Arc<Shape> {
    use std::sync::{Mutex, PoisonError};
    const KEEP: usize = 8;
    static CACHE: Mutex<Vec<(Relation, Arc<Shape>)>> = Mutex::new(Vec::new());
    let find = |cache: &[(Relation, Arc<Shape>)]| {
        cache
            .iter()
            .find(|(r, _)| r == relation)
            .map(|(_, shape)| shape.clone())
    };
    if let Some(hit) = find(&CACHE.lock().unwrap_or_else(PoisonError::into_inner)) {
        return hit;
    }
    let shape = Arc::new(build_shape(relation));
    let mut cache = CACHE.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(hit) = find(&cache) {
        return hit;
    }
    if cache.len() == KEEP {
        cache.remove(0);
    }
    cache.push((relation.clone(), shape.clone()));
    shape
}

#[cfg(not(feature = "std"))]
fn shape_of(relation: &Relation) -> Arc<Shape> {
    Arc::new(build_shape(relation))
}

/// The public relation of a statement: it depends on the claim kind and, for BIP-32, on
/// the seed length and the path, and on nothing else. `None` for a malformed statement.
pub fn ownership_shape(statement: &OwnershipStatement) -> Option<Arc<Shape>> {
    statement.claim.relation().map(|r| shape_of(&r))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnershipError {
    /// The statement's parameters are outside the supported ranges.
    MalformedStatement,
    /// The witness does not produce the statement's claim and nullifier.
    WitnessMismatch,
    Proof(ZkHemError),
}

fn checked_relation(
    statement: &OwnershipStatement,
    witness: &OwnershipWitness,
) -> Result<Relation, OwnershipError> {
    let relation = statement
        .claim
        .relation()
        .ok_or(OwnershipError::MalformedStatement)?;
    let kind = match &statement.claim {
        LegacyClaim::BitcoinHash160(_) => ClaimKind::BitcoinHash160,
        LegacyClaim::EthereumAddress(_) => ClaimKind::EthereumAddress,
        LegacyClaim::Ed25519Seed { .. } => ClaimKind::Ed25519Seed,
        LegacyClaim::Bip32Secp256k1 { path, .. } => ClaimKind::Bip32Secp256k1 { path: path.clone() },
    };
    let (claim, mut scalar) = evaluate(&kind, witness).ok_or(OwnershipError::WitnessMismatch)?;
    let nullifier = migration_nullifier(relation.curve(), &scalar, &statement.migration_domain);
    wipe(&mut scalar);
    if claim != statement.claim || nullifier != statement.nullifier {
        return Err(OwnershipError::WitnessMismatch);
    }
    Ok(relation)
}

/// The relation of `statement` with the assignment for `witness`, after checking natively
/// that the witness produces the statement. The assignment is secret. This is what a
/// prover that does not go through [`prove_ownership`] (the collaborative one) starts from;
/// its transcript statement must be the one [`prove_ownership`] uses.
pub fn synthesize_ownership(
    statement: &OwnershipStatement,
    witness: &OwnershipWitness,
) -> Result<(Shape, Vec<F>), OwnershipError> {
    let relation = checked_relation(statement, witness)?;
    let (shape, assignment, _) = build(
        &relation,
        &statement.public_bits(&relation),
        witness.secret(),
    );
    Ok((shape, assignment))
}

/// The statement bytes [`prove_ownership`] and [`verify_ownership`] hand to zk-Hem.
pub fn ownership_transcript(statement: &OwnershipStatement, regime: WhirSecurityRegime) -> Vec<u8> {
    statement.transcript(regime)
}

// ============================================================================
// Proofs
// ============================================================================

/// An ownership proof for one claim kind under one regime.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnershipProof {
    claim_tag: u8,
    pub regime: WhirSecurityRegime,
    pub proof: ZkHemProof,
}

impl OwnershipProof {
    /// `magic(8) || claim kind || regime || zk-Hem proof`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = PROOF_MAGIC.to_vec();
        out.push(self.claim_tag);
        out.push(self.regime as u8);
        out.extend_from_slice(&self.proof.to_bytes());
        out
    }

    /// Strict decoding against the statement the proof is for: the claim kind must be the
    /// statement's, the regime a known one, and the zk-Hem part canonical for the
    /// statement's relation with no byte left over.
    pub fn from_bytes(bytes: &[u8], statement: &OwnershipStatement) -> Option<Self> {
        let rest = bytes.strip_prefix(PROOF_MAGIC.as_slice())?;
        let (&claim_tag, rest) = rest.split_first()?;
        let (&regime, rest) = rest.split_first()?;
        if claim_tag != statement.claim.tag() {
            return None;
        }
        let regime = WhirSecurityRegime::from_u8(regime)?;
        let shape = ownership_shape(statement)?;
        Some(Self {
            claim_tag,
            regime,
            proof: ZkHemProof::from_bytes(rest, &shape, regime)?,
        })
    }
}

/// Prove a statement. `seed` must be uniform and secret; it drives every mask and blinder
/// of the proof.
pub fn prove_ownership(
    statement: &OwnershipStatement,
    witness: &OwnershipWitness,
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
) -> Result<OwnershipProof, OwnershipError> {
    let (shape, assignment) = synthesize_ownership(statement, witness)?;
    let proof = protocol::prove(
        &shape,
        assignment,
        &statement.transcript(regime),
        regime,
        seed,
    )
    .map_err(OwnershipError::Proof)?;
    Ok(OwnershipProof {
        claim_tag: statement.claim.tag(),
        regime,
        proof,
    })
}

/// Verify a proof against a statement under the regime the verifier requires. On `true`,
/// [`OwnershipStatement::binding`] is what the registry should record.
pub fn verify_ownership(
    statement: &OwnershipStatement,
    regime: WhirSecurityRegime,
    proof: &OwnershipProof,
) -> bool {
    if proof.regime != regime || proof.claim_tag != statement.claim.tag() {
        return false;
    }
    let (Some(shape), Some(public_inputs)) =
        (ownership_shape(statement), statement.public_inputs())
    else {
        return false;
    };
    protocol::verify(
        &shape,
        &public_inputs,
        &statement.transcript(regime),
        regime,
        &proof.proof,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::println;
    use std::string::String;
    use std::sync::OnceLock;

    const REGIME: WhirSecurityRegime = WhirSecurityRegime::BciksJohnsonQrom128;
    const PQ: [u8; 32] = [0x51; 32];
    const DOMAIN: [u8; 32] = [0xd0; 32];
    const EPOCH: u64 = 7;

    fn hex(s: &str) -> Vec<u8> {
        let digits: Vec<u8> = s
            .bytes()
            .filter(|b| !b.is_ascii_whitespace())
            .map(|b| (b as char).to_digit(16).expect("hex digit") as u8)
            .collect();
        assert!(digits.len() % 2 == 0);
        digits.chunks(2).map(|p| (p[0] << 4) | p[1]).collect()
    }

    fn arr<const N: usize>(s: &str) -> [u8; N] {
        hex(s).try_into().expect("length")
    }

    /// Base58Check payload (checksum verified and removed).
    fn base58check(s: &str) -> Vec<u8> {
        const ALPHABET: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
        let mut out: Vec<u8> = Vec::new();
        for c in s.bytes() {
            let mut carry = ALPHABET.iter().position(|&a| a == c).expect("base58") as u32;
            for byte in out.iter_mut().rev() {
                carry += 58 * u32::from(*byte);
                *byte = carry as u8;
                carry >>= 8;
            }
            while carry > 0 {
                out.insert(0, carry as u8);
                carry >>= 8;
            }
        }
        let (payload, checksum) = out.split_at(out.len() - 4);
        let digest = sha2_native::sha256(&sha2_native::sha256(payload));
        assert_eq!(checksum, &digest[..4], "base58check checksum");
        payload.to_vec()
    }

    const KEY: [u8; 32] = [
        0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x0f, 0xed, 0xcb, 0xa9, 0x87, 0x65, 0x43,
        0x21, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x01,
    ];

    fn seed64() -> Vec<u8> {
        (0..64u8).map(|i| i.wrapping_mul(37) ^ 0x5a).collect()
    }

    fn case(index: usize) -> (ClaimKind, OwnershipWitness) {
        match index {
            0 => (
                ClaimKind::BitcoinHash160,
                OwnershipWitness::Secp256k1Key(KEY),
            ),
            1 => (
                ClaimKind::EthereumAddress,
                OwnershipWitness::Secp256k1Key(KEY),
            ),
            2 => (ClaimKind::Ed25519Seed, OwnershipWitness::Ed25519Seed(KEY)),
            _ => (
                ClaimKind::Bip32Secp256k1 {
                    path: vec![BIP32_HARDENED + 44],
                },
                OwnershipWitness::Bip32Seed(seed64()),
            ),
        }
    }

    fn statement(index: usize) -> (OwnershipStatement, OwnershipWitness) {
        let (kind, witness) = case(index);
        let st = OwnershipStatement::derive(&kind, &witness, PQ, DOMAIN, EPOCH).expect("valid");
        (st, witness)
    }

    /// One honest proof per claim kind, shared by the tests below.
    fn proven(index: usize) -> &'static (OwnershipStatement, OwnershipProof) {
        static PROOFS: [OnceLock<(OwnershipStatement, OwnershipProof)>; 4] =
            [const { OnceLock::new() }; 4];
        PROOFS[index].get_or_init(|| {
            let (st, witness) = statement(index);
            let proof = prove_ownership(&st, &witness, REGIME, &[index as u8 + 1; 32]).unwrap();
            (st, proof)
        })
    }

    #[test]
    fn bip32_matches_test_vector_1() {
        // BIP-32, "Test vector 1": (path, ext pub, ext prv).
        let seed = hex("000102030405060708090a0b0c0d0e0f");
        let h = BIP32_HARDENED;
        let chain: [(&[u32], &str, &str); 6] = [
            (
                &[],
                "xpub661MyMwAqRbcFtXgS5sYJABqqG9YLmC4Q1Rdap9gSE8NqtwybGhePY2gZ29ESFjqJoCu1Rupje8YtGqsefD265TMg7usUDFdp6W1EGMcet8",
                "xprv9s21ZrQH143K3QTDL4LXw2F7HEK3wJUD2nW2nRk4stbPy6cq3jPPqjiChkVvvNKmPGJxWUtg6LnF5kejMRNNU3TGtRBeJgk33yuGBxrMPHi",
            ),
            (
                &[h],
                "xpub68Gmy5EdvgibQVfPdqkBBCHxA5htiqg55crXYuXoQRKfDBFA1WEjWgP6LHhwBZeNK1VTsfTFUHCdrfp1bgwQ9xv5ski8PX9rL2dZXvgGDnw",
                "xprv9uHRZZhk6KAJC1avXpDAp4MDc3sQKNxDiPvvkX8Br5ngLNv1TxvUxt4cV1rGL5hj6KCesnDYUhd7oWgT11eZG7XnxHrnYeSvkzY7d2bhkJ7",
            ),
            (
                &[h, 1],
                "xpub6ASuArnXKPbfEwhqN6e3mwBcDTgzisQN1wXN9BJcM47sSikHjJf3UFHKkNAWbWMiGj7Wf5uMash7SyYq527Hqck2AxYysAA7xmALppuCkwQ",
                "xprv9wTYmMFdV23N2TdNG573QoEsfRrWKQgWeibmLntzniatZvR9BmLnvSxqu53Kw1UmYPxLgboyZQaXwTCg8MSY3H2EU4pWcQDnRnrVA1xe8fs",
            ),
            (
                &[h, 1, h + 2],
                "xpub6D4BDPcP2GT577Vvch3R8wDkScZWzQzMMUm3PWbmWvVJrZwQY4VUNgqFJPMM3No2dFDFGTsxxpG5uJh7n7epu4trkrX7x7DogT5Uv6fcLW5",
                "xprv9z4pot5VBttmtdRTWfWQmoH1taj2axGVzFqSb8C9xaxKymcFzXBDptWmT7FwuEzG3ryjH4ktypQSAewRiNMjANTtpgP4mLTj34bhnZX7UiM",
            ),
            (
                &[h, 1, h + 2, 2],
                "xpub6FHa3pjLCk84BayeJxFW2SP4XRrFd1JYnxeLeU8EqN3vDfZmbqBqaGJAyiLjTAwm6ZLRQUMv1ZACTj37sR62cfN7fe5JnJ7dh8zL4fiyLHV",
                "xprvA2JDeKCSNNZky6uBCviVfJSKyQ1mDYahRjijr5idH2WwLsEd4Hsb2Tyh8RfQMuPh7f7RtyzTtdrbdqqsunu5Mm3wDvUAKRHSC34sJ7in334",
            ),
            (
                &[h, 1, h + 2, 2, 1_000_000_000],
                "xpub6H1LXWLaKsWFhvm6RVpEL9P4KfRZSW7abD2ttkWP3SSQvnyA8FSVqNTEcYFgJS2UaFcxupHiYkro49S8yGasTvXEYBVPamhGW6cFJodrTHy",
                "xprvA41z7zogVVwxVSgdKUHDy1SKmdb533PjDz7J6N6mV6uS3ze1ai8FHa8kmHScGpWmj4WggLyQjgPie1rFSruoUihUZREPSL39UNdE3BBDu76",
            ),
        ];
        for (path, xpub, xprv) in chain {
            // version(4) depth(1) fingerprint(4) child(4) chain code(32) key(33).
            let (xpub, xprv) = (base58check(xpub), base58check(xprv));
            assert_eq!((xpub.len(), xprv.len()), (78, 78));
            assert_eq!(usize::from(xpub[4]), path.len());
            let node = bip32_derive(&seed, path).expect("valid derivation");
            assert_eq!(node.chain_code[..], xpub[13..45], "chain code at {path:?}");
            assert_eq!(node.public_key()[..], xpub[45..], "public key at {path:?}");
            assert_eq!(xprv[45], 0);
            assert_eq!(node.private_key[..], xprv[46..], "private key at {path:?}");
        }
    }

    #[test]
    fn ed25519_and_secp256k1_references_match_published_vectors() {
        // RFC 8032 section 7.1, tests 1 and 2.
        for (seed, public) in [
            (
                "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
                "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
            ),
            (
                "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
                "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
            ),
        ] {
            assert_eq!(ed25519_public_key(&arr(seed)), arr::<32>(public));
        }
        // Secret key 1: the generator.
        let mut one = [0u8; 32];
        one[31] = 1;
        assert_eq!(
            secp256k1_public_key(&one).unwrap(),
            arr::<33>("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
        );
        assert_eq!(
            bitcoin_hash160(&one).unwrap(),
            arr::<20>("751e76e8199196d454941c45d1b3a323f1433bd6")
        );
        assert_eq!(
            ethereum_address(&one).unwrap(),
            arr::<20>("7e5f4552091a69125d5dfcb7b8c2659029395bdf")
        );
        // Zero and the group order are not keys.
        let order = arr::<32>("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        assert_eq!(secp256k1_public_key(&[0; 32]), None);
        assert_eq!(bitcoin_hash160(&order), None);
        assert_eq!(ethereum_address(&order), None);
    }

    #[test]
    fn nullifier_separates_domains_and_curves_and_follows_the_key() {
        let n = migration_nullifier(NullifierCurve::Secp256k1, &KEY, &DOMAIN);
        let mut other_domain = DOMAIN;
        other_domain[31] ^= 1;
        assert_ne!(
            n,
            migration_nullifier(NullifierCurve::Secp256k1, &KEY, &other_domain)
        );
        assert_ne!(n, migration_nullifier(NullifierCurve::Ed25519, &KEY, &DOMAIN));
        let mut other_key = KEY;
        other_key[0] ^= 1;
        assert_ne!(
            n,
            migration_nullifier(NullifierCurve::Secp256k1, &other_key, &DOMAIN)
        );
        // It is plain SHA-256 of the documented preimage.
        let mut preimage = b"QSAG.MIGRATE.HEM.NULLIFIER/v1\0\0\x01".to_vec();
        preimage.extend_from_slice(&DOMAIN);
        preimage.extend_from_slice(&KEY);
        assert_eq!(n, sha2_native::sha256(&preimage));

        // The same key through three statements has one nullifier per domain.
        let (bitcoin, _) = statement(0);
        let (ethereum, _) = statement(1);
        assert_eq!(bitcoin.nullifier, n);
        assert_eq!(ethereum.nullifier, n);
        let path = vec![BIP32_HARDENED + 44, 5];
        let node = bip32_derive(&seed64(), &path).unwrap();
        let derive = |kind: &ClaimKind, w: &OwnershipWitness, domain: [u8; 32]| {
            OwnershipStatement::derive(kind, w, PQ, domain, EPOCH).unwrap()
        };
        let via_seed = derive(
            &ClaimKind::Bip32Secp256k1 { path },
            &OwnershipWitness::Bip32Seed(seed64()),
            DOMAIN,
        );
        let leaf = OwnershipWitness::Secp256k1Key(node.private_key);
        let via_key = derive(&ClaimKind::BitcoinHash160, &leaf, DOMAIN);
        assert_eq!(via_seed.nullifier, via_key.nullifier);
        assert_ne!(via_seed.nullifier, n);
        assert_ne!(
            derive(&ClaimKind::BitcoinHash160, &leaf, other_domain).nullifier,
            via_key.nullifier
        );
        // Both also name the same legacy credential.
        assert_eq!(
            via_seed.claim.legacy_commitment(),
            via_key.claim.legacy_commitment()
        );
        // The Ed25519 nullifier is over the clamped scalar, not the seed.
        let (ed, _) = statement(2);
        assert_eq!(
            ed.nullifier,
            migration_nullifier(
                NullifierCurve::Ed25519,
                &ed25519_clamped_scalar(&KEY),
                &DOMAIN
            )
        );
        assert_ne!(
            ed.nullifier,
            migration_nullifier(NullifierCurve::Ed25519, &KEY, &DOMAIN)
        );
    }

    #[test]
    fn derive_rejects_unusable_witnesses() {
        let derive = |kind: &ClaimKind, w: &OwnershipWitness| {
            OwnershipStatement::derive(kind, w, PQ, DOMAIN, EPOCH)
        };
        let order = arr::<32>("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let bip32 = |path: Vec<u32>| ClaimKind::Bip32Secp256k1 { path };
        assert!(derive(&ClaimKind::BitcoinHash160, &OwnershipWitness::Secp256k1Key([0; 32])).is_none());
        assert!(derive(&ClaimKind::EthereumAddress, &OwnershipWitness::Secp256k1Key(order)).is_none());
        assert!(derive(&ClaimKind::Ed25519Seed, &OwnershipWitness::Secp256k1Key(KEY)).is_none());
        assert!(derive(&ClaimKind::BitcoinHash160, &OwnershipWitness::Ed25519Seed(KEY)).is_none());
        assert!(derive(&bip32(vec![]), &OwnershipWitness::Bip32Seed(vec![1; 15])).is_none());
        assert!(derive(&bip32(vec![]), &OwnershipWitness::Bip32Seed(vec![1; 65])).is_none());
        assert!(derive(&bip32(vec![0; 11]), &OwnershipWitness::Bip32Seed(vec![1; 32])).is_none());
        assert!(derive(&bip32(vec![0; 10]), &OwnershipWitness::Bip32Seed(vec![1; 16])).is_some());
    }

    #[test]
    fn statement_encoding_is_canonical_and_strict() {
        for index in 0..4 {
            let (st, _) = statement(index);
            let bytes = st.to_bytes();
            assert_eq!(OwnershipStatement::from_bytes(&bytes), Some(st.clone()));
            assert_eq!(bytes[29], st.claim.tag());
            assert_eq!(bytes[30], u8::from(index >= 2));

            let mut longer = bytes.clone();
            longer.push(0);
            assert_eq!(OwnershipStatement::from_bytes(&longer), None);
            assert_eq!(OwnershipStatement::from_bytes(&bytes[..bytes.len() - 1]), None);
            // Tag, kind and exposure are checked; every later byte is a statement field.
            for at in 0..31 {
                let mut bad = bytes.clone();
                bad[at] ^= 1;
                assert_eq!(OwnershipStatement::from_bytes(&bad), None, "byte {at}");
            }
            for at in 31..bytes.len() {
                let mut other = bytes.clone();
                other[at] ^= 0x40;
                assert_ne!(OwnershipStatement::from_bytes(&other), Some(st.clone()), "byte {at}");
            }
        }
        // BIP-32 parameters outside the supported ranges do not decode.
        let (st, _) = statement(3);
        let with = |f: &dyn Fn(&mut LegacyClaim)| {
            let mut bad = st.clone();
            f(&mut bad.claim);
            (bad.is_well_formed(), OwnershipStatement::from_bytes(&bad.to_bytes()).is_some())
        };
        let seed_len = |v: u8| {
            move |c: &mut LegacyClaim| {
                if let LegacyClaim::Bip32Secp256k1 { seed_len, .. } = c {
                    *seed_len = v;
                }
            }
        };
        assert_eq!(with(&seed_len(15)), (false, false));
        assert_eq!(with(&seed_len(65)), (false, false));
        assert_eq!(with(&seed_len(16)), (true, true));
        assert_eq!(
            with(&|c| {
                if let LegacyClaim::Bip32Secp256k1 { path, .. } = c {
                    *path = vec![1; MAX_BIP32_DEPTH + 1];
                }
            }),
            (false, false)
        );
        assert_eq!(
            with(&|c| {
                if let LegacyClaim::Bip32Secp256k1 { public_key, .. } = c {
                    public_key[0] = 4;
                }
            }),
            (false, false)
        );
    }

    /// The relation itself, without a proof: satisfied by the honest assignment, and
    /// unsatisfied when any public region or the witness is wrong.
    #[test]
    fn relations_accept_the_honest_assignment_only() {
        for index in 0..4 {
            let (st, witness) = statement(index);
            let relation = st.claim.relation().unwrap();
            let public = st.public_bits(&relation);
            let (shape, z, rows) = build(&relation, &public, witness.secret());
            assert!(shape.is_satisfied(&z), "case {index}");
            assert_eq!(shape.num_sbox, 0, "the collaborative prover needs mul rows only");
            assert_eq!(shape.num_public, public.len());
            assert!(rows > 90_000 && rows + 12 <= shape.num_rows());
            assert_eq!(st.public_inputs().unwrap(), z[1..=public.len()]);

            // The shape does not depend on the witness or on public values.
            assert_eq!(shape.digest(), ownership_shape(&st).unwrap().digest());
            let other_secret = match index {
                0 | 1 => vec![0x77; 32],
                2 => vec![0xff; 32],
                _ => vec![0xff; 64],
            };
            let (other, _, _) = build(&relation, &vec![true; public.len()], &other_secret);
            assert_eq!(other.digest(), shape.digest());

            // One wrong bit in the claim, in the domain's chaining value, in the nullifier.
            let claim_bits = 8 * relation.claim_bytes();
            for at in [3, claim_bits - 1, claim_bits + 5, claim_bits + 255, claim_bits + 256, public.len() - 1] {
                let mut wrong = public.clone();
                wrong[at] ^= true;
                let (shape, z, _) = build(&relation, &wrong, witness.secret());
                assert!(!shape.is_satisfied(&z), "case {index}, public bit {at}");
            }
            // Another secret under the honest public values.
            let mut secret = witness.secret().to_vec();
            secret[7] ^= 0x20;
            let (shape, z, _) = build(&relation, &public, &secret);
            assert!(!shape.is_satisfied(&z), "case {index}, wrong secret");
        }

        // A BIP-32 statement is tied to its path and to hardened versus normal steps.
        let (st, witness) = statement(3);
        let public = st.public_bits(&st.claim.relation().unwrap());
        for path in [vec![BIP32_HARDENED + 45], vec![44], vec![]] {
            let relation = Relation::Bip32Secp256k1 { seed_len: 64, path };
            let (shape, z, _) = build(&relation, &public, witness.secret());
            assert!(!shape.is_satisfied(&z));
        }
    }

    #[test]
    fn bip32_relation_follows_normal_and_hardened_steps() {
        // One normal and one hardened step below a 16-byte seed.
        let seed = hex("000102030405060708090a0b0c0d0e0f");
        let path = vec![1, BIP32_HARDENED + 2];
        let witness = OwnershipWitness::Bip32Seed(seed);
        let kind = ClaimKind::Bip32Secp256k1 { path };
        let st = OwnershipStatement::derive(&kind, &witness, PQ, DOMAIN, EPOCH).unwrap();
        let relation = st.claim.relation().unwrap();
        let public = st.public_bits(&relation);
        let (shape, z, _) = build(&relation, &public, witness.secret());
        assert!(shape.is_satisfied(&z));
        // Swapping which step is hardened is a different relation that this key fails.
        let swapped = Relation::Bip32Secp256k1 {
            seed_len: 16,
            path: vec![BIP32_HARDENED + 1, 2],
        };
        let (shape, z, _) = build(&swapped, &public, witness.secret());
        assert!(!shape.is_satisfied(&z));
    }

    #[test]
    fn bip32_child_key_enforces_the_rejection_rules() {
        let order_be = arr::<32>("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141");
        let sub = |a: &[u8; 32], b: u8| {
            let mut out = *a;
            let mut borrow = u16::from(b);
            for byte in out.iter_mut().rev() {
                let v = u16::from(*byte).wrapping_sub(borrow);
                *byte = v as u8;
                borrow = (v >> 8) & 1;
            }
            out
        };
        let small = |v: u8| {
            let mut out = [0u8; 32];
            out[31] = v;
            out
        };
        // (I_L, parent key, expected child or `None` when BIP-32 rejects).
        type Case = ([u8; 32], [u8; 32], Option<[u8; 32]>);
        let cases: [Case; 7] = [
            (small(5), small(9), Some(small(14))),
            (small(0), small(9), Some(small(9))),
            (sub(&order_be, 1), small(2), Some(small(1))),
            (sub(&order_be, 1), small(1), None),
            (sub(&order_be, 9), small(9), None),
            (order_be, small(9), None),
            ([0xff; 32], small(9), None),
        ];
        for (tweak, parent, want) in cases {
            let native_ok = secp_scalar_is_canonical(&tweak)
                && secp_scalar_is_valid_nonzero(&secp_scalar_add_mod_n(&tweak, &parent));
            assert_eq!(native_ok, want.is_some());

            let mut cs = ConstraintSystem::new();
            let tweak_bits = reverse_bytes(&alloc_bits(&mut cs, &tweak));
            let parent_bits = reverse_bytes(&alloc_bits(&mut cs, &parent));
            let order = Modulus::secp256k1_order();
            let child = bip32_child_key(&mut cs, &order, &tweak_bits, &parent_bits);
            assert_eq!(child.len(), 256);
            let child_be = super::super::hash::bits_to_bytes(&cs, &reverse_bytes(&child));
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), want.is_some(), "I_L {tweak:02x?}");
            if let Some(want) = want {
                assert_eq!(child_be, want);
                assert_eq!(secp_scalar_add_mod_n(&tweak, &parent), want);
            }
        }
    }

    #[test]
    fn prover_refuses_a_witness_that_does_not_match() {
        let (st, witness) = statement(0);
        let mut wrong_key = KEY;
        wrong_key[3] ^= 1;
        let seed = [9; 32];
        assert_eq!(
            prove_ownership(&st, &OwnershipWitness::Secp256k1Key(wrong_key), REGIME, &seed),
            Err(OwnershipError::WitnessMismatch)
        );
        assert_eq!(
            prove_ownership(&st, &OwnershipWitness::Ed25519Seed(KEY), REGIME, &seed),
            Err(OwnershipError::WitnessMismatch)
        );
        // The right key cannot claim another nullifier, address or domain.
        for field in 0..3 {
            let mut other = st.clone();
            match field {
                0 => other.nullifier[0] ^= 1,
                1 => other.migration_domain[0] ^= 1,
                _ => other.claim = LegacyClaim::BitcoinHash160([7; 20]),
            }
            assert_eq!(
                prove_ownership(&other, &witness, REGIME, &seed),
                Err(OwnershipError::WitnessMismatch),
                "field {field}"
            );
        }
        let (mut st, witness) = statement(3);
        if let LegacyClaim::Bip32Secp256k1 { seed_len, .. } = &mut st.claim {
            *seed_len = 65;
        }
        assert_eq!(
            prove_ownership(&st, &witness, REGIME, &seed),
            Err(OwnershipError::MalformedStatement)
        );
    }

    /// Everything a verifier must reject, against one honest proof.
    fn check_proof(index: usize) {
        let (st, proof) = proven(index);
        assert!(verify_ownership(st, REGIME, proof), "honest proof, case {index}");

        // Each public field is bound.
        let mut variants: Vec<(&str, OwnershipStatement)> = Vec::new();
        let mut push = |name: &'static str, f: &dyn Fn(&mut OwnershipStatement)| {
            let mut other = st.clone();
            f(&mut other);
            assert_ne!(&other, st, "{name} must change the statement");
            variants.push((name, other));
        };
        push("pq commitment", &|s| s.pq_commitment[31] ^= 1);
        push("migration domain", &|s| s.migration_domain[0] ^= 0x80);
        push("epoch", &|s| s.epoch += 1);
        push("nullifier", &|s| s.nullifier[16] ^= 4);
        push("legacy value", &|s| match &mut s.claim {
            LegacyClaim::BitcoinHash160(v) | LegacyClaim::EthereumAddress(v) => v[19] ^= 1,
            LegacyClaim::Ed25519Seed { public_key } => public_key[0] ^= 1,
            LegacyClaim::Bip32Secp256k1 { public_key, .. } => public_key[32] ^= 1,
        });
        if matches!(st.claim, LegacyClaim::Bip32Secp256k1 { .. }) {
            push("path index", &|s| {
                if let LegacyClaim::Bip32Secp256k1 { path, .. } = &mut s.claim {
                    path[0] += 1;
                }
            });
            push("path hardening", &|s| {
                if let LegacyClaim::Bip32Secp256k1 { path, .. } = &mut s.claim {
                    path[0] -= BIP32_HARDENED;
                }
            });
            push("path length", &|s| {
                if let LegacyClaim::Bip32Secp256k1 { path, .. } = &mut s.claim {
                    path.push(0);
                }
            });
            push("seed length", &|s| {
                if let LegacyClaim::Bip32Secp256k1 { seed_len, .. } = &mut s.claim {
                    *seed_len -= 1;
                }
            });
            push("public key parity", &|s| {
                if let LegacyClaim::Bip32Secp256k1 { public_key, .. } = &mut s.claim {
                    public_key[0] ^= 1;
                }
            });
        }
        for (name, other) in &variants {
            assert!(!verify_ownership(other, REGIME, proof), "{name}, case {index}");
            // Not merely the tag check: also with the proof relabelled for that statement.
            let mut relabelled = proof.clone();
            relabelled.claim_tag = other.claim.tag();
            assert!(!verify_ownership(other, REGIME, &relabelled), "{name}, case {index}");
        }

        // The regime is the verifier's choice and is bound.
        let other_regime = WhirSecurityRegime::Cdhz25JohnsonQrom128;
        assert!(!verify_ownership(st, other_regime, proof));
        let mut relabelled = proof.clone();
        relabelled.regime = other_regime;
        assert!(!verify_ownership(st, other_regime, &relabelled));

        // Wire format: canonical, strict, and every sampled byte matters.
        let bytes = proof.to_bytes();
        let decoded = OwnershipProof::from_bytes(&bytes, st).expect("canonical");
        assert_eq!(&decoded, proof);
        assert!(verify_ownership(st, REGIME, &decoded));
        let mut longer = bytes.clone();
        longer.push(0);
        assert!(OwnershipProof::from_bytes(&longer, st).is_none());
        assert!(OwnershipProof::from_bytes(&bytes[..bytes.len() - 1], st).is_none());
        let accepted = |bytes: &[u8]| {
            OwnershipProof::from_bytes(bytes, st).is_some_and(|p| verify_ownership(st, REGIME, &p))
        };
        let mut tried = 0;
        for at in (0..10).chain((10..bytes.len()).step_by(bytes.len() / 61)) {
            let mut bad = bytes.clone();
            bad[at] ^= 1;
            assert!(!accepted(&bad), "byte {at} of {}, case {index}", bytes.len());
            tried += 1;
        }
        assert!(tried >= 60);
    }

    #[test]
    fn bitcoin_hash160_proof_verifies_and_binds_its_statement() {
        check_proof(0);
    }

    #[test]
    fn ethereum_address_proof_verifies_and_binds_its_statement() {
        check_proof(1);
    }

    #[test]
    fn ed25519_seed_proof_verifies_and_binds_its_statement() {
        check_proof(2);
    }

    #[test]
    fn bip32_proof_verifies_and_binds_its_statement() {
        check_proof(3);
    }

    #[test]
    fn a_proof_for_one_statement_kind_does_not_verify_as_another() {
        // Bitcoin and Ethereum statements over the same 20 bytes, key and nullifier.
        let (bitcoin, bitcoin_proof) = proven(0);
        let (ethereum, ethereum_proof) = proven(1);
        assert_eq!(bitcoin.nullifier, ethereum.nullifier);
        let as_ethereum = OwnershipStatement {
            claim: LegacyClaim::EthereumAddress(bitcoin.claim.value().try_into().unwrap()),
            ..bitcoin.clone()
        };
        let as_bitcoin = OwnershipStatement {
            claim: LegacyClaim::BitcoinHash160(ethereum.claim.value().try_into().unwrap()),
            ..ethereum.clone()
        };
        for (other, proof) in [(&as_ethereum, bitcoin_proof), (&as_bitcoin, ethereum_proof)] {
            assert!(!verify_ownership(other, REGIME, proof));
            assert!(OwnershipProof::from_bytes(&proof.to_bytes(), other).is_none());
            let mut relabelled = proof.clone();
            relabelled.claim_tag = other.claim.tag();
            assert!(!verify_ownership(other, REGIME, &relabelled));
        }
        // Every proof against every other honest statement.
        for i in 0..4 {
            for j in 0..4 {
                let (st, _) = proven(i);
                let (_, proof) = proven(j);
                let mut relabelled = proof.clone();
                relabelled.claim_tag = st.claim.tag();
                assert_eq!(verify_ownership(st, REGIME, &relabelled), i == j, "{j} as {i}");
            }
        }
    }

    #[cfg(feature = "std")]
    #[test]
    fn binding_is_what_the_registry_consumes() {
        use super::super::registry::{KeyExposure, legacy_identifier};
        for index in 0..4 {
            let (st, _) = statement(index);
            let binding = st.binding();
            assert_eq!(binding.nullifier, st.nullifier);
            assert_eq!(binding.migration_domain, DOMAIN);
            assert_eq!(binding.pq_commitment, PQ);
            assert_eq!(binding.epoch, EPOCH);
            let exposure = if index >= 2 { KeyExposure::Revealed } else { KeyExposure::Hidden };
            assert_eq!(binding.exposure, exposure);
            assert_eq!(binding.legacy_id, legacy_identifier(&st.claim.legacy_commitment()));
        }
        let (bitcoin, _) = statement(0);
        let (ethereum, _) = statement(1);
        assert_ne!(bitcoin.binding().legacy_id, ethereum.binding().legacy_id);
        assert_eq!(
            bitcoin.claim.legacy_commitment(),
            LegacyCommitmentKind::BitcoinHash160(bitcoin_hash160(&KEY).unwrap())
        );
    }

    fn peak_rss_mib() -> Option<u64> {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        let line = status.lines().find(|l| l.starts_with("VmHWM:"))?;
        let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
        Some(kib / 1024)
    }

    /// `cargo test --release -p dregg-sig-migrate --features std --lib hem::relations::tests::measure
    /// -- --ignored --nocapture --test-threads 1`
    #[test]
    #[ignore = "measurement"]
    fn measure_ownership_proofs() {
        let h = BIP32_HARDENED;
        let cases: Vec<(&str, ClaimKind, OwnershipWitness)> = vec![
            ("bitcoin-hash160", ClaimKind::BitcoinHash160, OwnershipWitness::Secp256k1Key(KEY)),
            ("ed25519-seed", ClaimKind::Ed25519Seed, OwnershipWitness::Ed25519Seed(KEY)),
            ("ethereum-address", ClaimKind::EthereumAddress, OwnershipWitness::Secp256k1Key(KEY)),
            (
                "bip32 m/44' (seed 64)",
                ClaimKind::Bip32Secp256k1 { path: vec![h + 44] },
                OwnershipWitness::Bip32Seed(seed64()),
            ),
            (
                "bip32 m/44'/0'/0'/0/0 (seed 64)",
                ClaimKind::Bip32Secp256k1 { path: vec![h + 44, h, h, 0, 0] },
                OwnershipWitness::Bip32Seed(seed64()),
            ),
        ];
        let only = std::env::var("HEM_MEASURE_ONLY").ok();
        let regimes: Vec<WhirSecurityRegime> = match std::env::var("HEM_MEASURE_REGIMES") {
            Ok(list) => list
                .split(',')
                .map(|t| WhirSecurityRegime::from_u8(t.trim().parse().unwrap()).unwrap())
                .collect(),
            Err(_) => vec![REGIME],
        };
        println!(
            "cpus={}",
            std::thread::available_parallelism().map_or(0, |n| n.get())
        );
        for (name, kind, witness) in &cases {
            if only.as_ref().is_some_and(|o| !name.contains(o.as_str())) {
                continue;
            }
            let st = OwnershipStatement::derive(kind, witness, PQ, DOMAIN, EPOCH).unwrap();
            let relation = st.claim.relation().unwrap();
            let t = std::time::Instant::now();
            let (shape, _, rows) = build(&relation, &st.public_bits(&relation), witness.secret());
            let synth_s = t.elapsed().as_secs_f64();
            for &regime in &regimes {
                let layout = protocol::Layout::new(&shape, regime).unwrap();
                let t = std::time::Instant::now();
                let proof = prove_ownership(&st, witness, regime, &[3; 32]).unwrap();
                let prove_s = t.elapsed().as_secs_f64();
                let bytes = proof.to_bytes();
                // The first verification also builds and caches the shape.
                let t = std::time::Instant::now();
                assert!(verify_ownership(&st, regime, &proof));
                let verify_cold_s = t.elapsed().as_secs_f64();
                let mut warm: Vec<f64> = (0..3)
                    .map(|_| {
                        let t = std::time::Instant::now();
                        let decoded = OwnershipProof::from_bytes(&bytes, &st).unwrap();
                        assert!(verify_ownership(&st, regime, &decoded));
                        t.elapsed().as_secs_f64()
                    })
                    .collect();
                warm.sort_by(f64::total_cmp);
                let sumcheck_bytes = 32
                    * (shape.log_rows * (protocol::ROW_DEGREE + 1)
                        + layout.var_bits * (protocol::COL_DEGREE + 1)
                        + 9);
                let stages: Vec<String> = layout
                    .schedule
                    .stages
                    .iter()
                    .map(|s| std::format!("{}q@x{}/2^{}", s.num_queries, s.blowup, s.step_vars))
                    .collect();
                println!(
                    "HEM_OWNERSHIP statement=\"{name}\" regime={} rows={rows} padded_rows=2^{} \
                     vars={} public_inputs={} cells=2^{} synth_s={synth_s:.2} prove_s={prove_s:.2} \
                     verify_cold_s={verify_cold_s:.2} verify_warm_ms={:.1} proof_bytes={} \
                     proof_kib={:.1} sumcheck_bytes={sumcheck_bytes} blind_cells={} stages=[{}] \
                     early_stop_vars={} peak_rss_mib={}",
                    regime as u8,
                    shape.log_rows,
                    shape.num_vars,
                    shape.num_public,
                    layout.log_cells,
                    warm[1] * 1e3,
                    bytes.len(),
                    bytes.len() as f64 / 1024.0,
                    layout.blind_cells,
                    stages.join(" "),
                    layout.schedule.early_stop_vars,
                    peak_rss_mib().map_or_else(|| String::from("n/a"), |m| std::format!("{m}")),
                );
            }
        }
    }
}
