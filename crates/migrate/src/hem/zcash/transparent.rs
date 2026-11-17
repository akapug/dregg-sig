//! Ownership of a Zcash transparent P2PKH address.
//!
//! A transparent address is the Bitcoin construction with Zcash's two-byte Base58Check
//! prefix (protocol specification 5.6.1.1): `t1...` on mainnet and `tm...` on testnet
//! carry `HASH160` of a compressed secp256k1 public key. Two statements are offered, both
//! over the relations of [`crate::hem::relations`]:
//!
//! * **Hidden key**: the prover knows `k` with `HASH160` of the encoding of `[k] G` equal
//!   to the address payload. The payload commits to one encoding of the key, so the
//!   statement names it ([`KeyEncoding`]): compressed (33 bytes, what every wallet has
//!   produced for years) or uncompressed (65 bytes, old imported keys). The public key
//!   stays hidden, so a party that can compute discrete logarithms learns nothing to
//!   attack from the statement; the address must never have been spent from (a spend
//!   reveals the key on chain). This is the P2PKH statement that the discussion of ZIP
//!   2007 (reserved; `zcash/zips` issue 1302) identifies as recoverable:
//!   `ZKPoK{(privkey): PubKeyHash = Hash160(PubKeyOf(privkey))}`.
//! * **Seed provenance**: the prover knows the BIP 32 seed whose key at the BIP 44 path
//!   `m / 44' / coin_type' / account' / change / index` (coin type 133 on mainnet, 1 on
//!   testnet; ZIP 32 "Transparent usage of BIP 44") has the stated public key, and the
//!   address is the `HASH160` of that key. The witness is a hash preimage, so this
//!   remains sound when the public key is known.
//!
//! The proof transcript is this module's own: it absorbs the network and the tag
//! `QSAG.MIGRATE.HEM.ZCASH.TADR/1`, so a proof for a Bitcoin statement over the same key
//! does not verify here, nor the reverse. The nullifier is the one of the underlying
//! relation (a hash of the signing scalar and the migration domain); a Zcash campaign
//! must use its own migration domain.
//!
//! P2SH addresses (`t3...`) are not covered: the hash commits to a redeem script, and a
//! statement has to rebuild the exact script bytes in the relation (issue 1302 lists the
//! wrapped P2PKH, wrapped P2PK and multisig forms). Nothing in this crate does that yet.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use dregg_sig_accel::sha2 as sha2_native;
use dregg_sig_agg::field::Goldilocks;
use dregg_sig_agg::pcs::WhirSecurityRegime;
use dregg_sig_agg::zk_hem::protocol::{self, ZkHemProof};
use dregg_sig_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape};

use super::encoding::{Network, TransparentKind, decode_transparent, encode_transparent};
use crate::hem::curve::{secp256k1_enforce_scalar_range, secp256k1_fixed_base_mul};
use crate::hem::hash::{Word, alloc_bits, const_bits, hash160, pack_bits, sha256_from_midstate};
use crate::hem::relations::{
    BIP32_HARDENED, ClaimKind, LegacyClaim, NullifierCurve, OwnershipError, OwnershipStatement,
    OwnershipWitness, migration_nullifier, ownership_shape, synthesize_ownership,
};
use crate::secp256k1_ct::{SecpPoint, secp_scalar_is_valid_nonzero};

type F = Goldilocks;

const STATEMENT_TAG: &[u8; 29] = b"QSAG.MIGRATE.HEM.ZCASH.TADR/1";
const PROOF_MAGIC: &[u8; 8] = b"QSHEMZT1";

/// Registry tag of a Zcash transparent P2PKH address (network byte, then the payload).
pub const LEGACY_TAG_TRANSPARENT_P2PKH: u8 = 18;

/// SLIP 44 coin type of a network.
pub fn coin_type(network: Network) -> u32 {
    match network {
        Network::Main => 133,
        Network::Test => 1,
    }
}

fn network_byte(network: Network) -> u8 {
    match network {
        Network::Main => 0,
        Network::Test => 1,
    }
}

/// The BIP 44 path `m / 44' / coin_type' / account' / change / index` of a transparent
/// address; `None` unless `account < 2^31`, `change <= 1` and `index < 2^31`.
pub fn bip44_path(network: Network, account: u32, change: u32, index: u32) -> Option<Vec<u32>> {
    (account < BIP32_HARDENED && change <= 1 && index < BIP32_HARDENED).then(|| {
        alloc::vec![
            44 | BIP32_HARDENED,
            coin_type(network) | BIP32_HARDENED,
            account | BIP32_HARDENED,
            change,
            index,
        ]
    })
}

/// The encoding of the public key that a P2PKH payload is the `HASH160` of.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeyEncoding {
    /// SEC1 compressed, 33 bytes.
    Compressed,
    /// SEC1 uncompressed, `04 || x || y`, 65 bytes.
    Uncompressed,
}

/// `HASH160(04 || x || y)` of a big-endian secp256k1 secret key; `None` unless
/// `1 <= k < n`.
pub fn uncompressed_hash160(key_be: &[u8; 32]) -> Option<[u8; 20]> {
    if !secp_scalar_is_valid_nonzero(key_be) {
        return None;
    }
    let mut encoding = [0u8; 65];
    encoding[0] = 0x04;
    encoding[1..].copy_from_slice(&SecpPoint::generator_mul_ct(key_be).to_uncompressed_64()?);
    Some(sha2_native::hash160(&encoding))
}

/// Public statement of ownership of a transparent P2PKH address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransparentStatement {
    pub network: Network,
    /// The key encoding behind the payload. Seed provenance is for compressed keys only.
    pub encoding: KeyEncoding,
    /// The underlying statement: a `HASH160` claim (hidden key) or a BIP 32 claim (seed
    /// provenance) with the path of [`bip44_path`].
    pub ownership: OwnershipStatement,
}

impl TransparentStatement {
    /// The hidden-key statement of a secp256k1 secret key whose public key the address
    /// hashes in the given encoding.
    pub fn derive_hidden(
        network: Network,
        encoding: KeyEncoding,
        witness: &OwnershipWitness,
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        let ownership = match (encoding, witness) {
            (KeyEncoding::Compressed, _) => OwnershipStatement::derive(
                &ClaimKind::BitcoinHash160,
                witness,
                pq_commitment,
                migration_domain,
                epoch,
            )?,
            (KeyEncoding::Uncompressed, OwnershipWitness::Secp256k1Key(key)) => {
                OwnershipStatement {
                    claim: LegacyClaim::BitcoinHash160(uncompressed_hash160(key)?),
                    pq_commitment,
                    migration_domain,
                    epoch,
                    nullifier: migration_nullifier(
                        NullifierCurve::Secp256k1,
                        key,
                        &migration_domain,
                    ),
                }
            }
            _ => return None,
        };
        Some(Self {
            network,
            encoding,
            ownership,
        })
    }

    /// The seed-provenance statement of a BIP 32 seed at a BIP 44 address path.
    #[allow(clippy::too_many_arguments)]
    pub fn derive_from_seed(
        network: Network,
        witness: &OwnershipWitness,
        account: u32,
        change: u32,
        index: u32,
        pq_commitment: [u8; 32],
        migration_domain: [u8; 32],
        epoch: u64,
    ) -> Option<Self> {
        Some(Self {
            network,
            encoding: KeyEncoding::Compressed,
            ownership: OwnershipStatement::derive(
                &ClaimKind::Bip32Secp256k1 {
                    path: bip44_path(network, account, change, index)?,
                },
                witness,
                pq_commitment,
                migration_domain,
                epoch,
            )?,
        })
    }

    /// The 20-byte payload of the address.
    pub fn hash160(&self) -> Option<[u8; 20]> {
        match &self.ownership.claim {
            LegacyClaim::BitcoinHash160(h) => Some(*h),
            LegacyClaim::Bip32Secp256k1 { public_key, .. } => {
                Some(sha2_native::hash160(public_key))
            }
            _ => None,
        }
    }

    /// The address string (`t1...` or `tm...`).
    pub fn address(&self) -> Option<String> {
        self.hash160()
            .map(|h| encode_transparent(self.network, TransparentKind::P2pkh, &h))
    }

    /// Whether this statement is about `address`: a P2PKH address of the statement's
    /// network with the statement's payload.
    pub fn is_for_address(&self, address: &str) -> bool {
        match (decode_transparent(address), self.hash160()) {
            (Ok((network, TransparentKind::P2pkh, payload)), Some(h)) => {
                network == self.network && payload == h
            }
            _ => false,
        }
    }

    /// Whether the underlying claim is one of the two this module admits; for seed
    /// provenance the path must be a BIP 44 address path of the statement's network.
    pub fn is_well_formed(&self) -> bool {
        if !self.ownership.is_well_formed() {
            return false;
        }
        match &self.ownership.claim {
            LegacyClaim::BitcoinHash160(_) => true,
            LegacyClaim::Bip32Secp256k1 { .. } if self.encoding != KeyEncoding::Compressed => false,
            LegacyClaim::Bip32Secp256k1 { path, .. } => match path.as_slice() {
                [purpose, coin, account, change, index] => {
                    *purpose == 44 | BIP32_HARDENED
                        && *coin == coin_type(self.network) | BIP32_HARDENED
                        && *account >= BIP32_HARDENED
                        && *change <= 1
                        && *index < BIP32_HARDENED
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// `tag(29) || network || key encoding || underlying statement`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = STATEMENT_TAG.to_vec();
        out.push(network_byte(self.network));
        out.push(self.encoding as u8);
        out.extend_from_slice(&self.ownership.to_bytes());
        out
    }

    /// The kind byte of a proof for this statement: the underlying claim kind, with the
    /// top bit set for an uncompressed key.
    fn proof_tag(&self) -> u8 {
        self.ownership.claim.tag() | ((self.encoding as u8) << 7)
    }

    /// The public relation: that of the underlying claim for a compressed key, this
    /// module's own for an uncompressed one.
    fn shape(&self) -> Option<Arc<Shape>> {
        if !self.is_well_formed() {
            return None;
        }
        match self.encoding {
            KeyEncoding::Compressed => ownership_shape(&self.ownership),
            KeyEncoding::Uncompressed => Some(uncompressed_shape()),
        }
    }

    /// Strict inverse of [`Self::to_bytes`].
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let rest = bytes.strip_prefix(STATEMENT_TAG.as_slice())?;
        let (&network, rest) = rest.split_first()?;
        let (&encoding, rest) = rest.split_first()?;
        let network = match network {
            0 => Network::Main,
            1 => Network::Test,
            _ => return None,
        };
        let encoding = match encoding {
            0 => KeyEncoding::Compressed,
            1 => KeyEncoding::Uncompressed,
            _ => return None,
        };
        let statement = Self {
            network,
            encoding,
            ownership: OwnershipStatement::from_bytes(rest)?,
        };
        statement.is_well_formed().then_some(statement)
    }

    fn transcript(&self, regime: WhirSecurityRegime) -> Vec<u8> {
        let mut out = self.to_bytes();
        out.push(regime as u8);
        out
    }

    /// The binding a verified statement asks the registry to record. The legacy
    /// identifier is that of the Zcash address (network and payload), not the Bitcoin
    /// identifier of the same key hash.
    #[cfg(feature = "std")]
    pub fn binding(&self) -> Option<crate::hem::registry::MigrationBinding> {
        let mut id = [0u8; 21];
        id[0] = network_byte(self.network);
        id[1..].copy_from_slice(&self.hash160()?);
        let mut binding = self.ownership.binding();
        binding.legacy_id =
            super::recovery::zcash_legacy_identifier(LEGACY_TAG_TRANSPARENT_P2PKH, &id);
        Some(binding)
    }
}

/// A transparent ownership proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransparentProof {
    claim_tag: u8,
    pub regime: WhirSecurityRegime,
    pub proof: ZkHemProof,
}

impl TransparentProof {
    /// `magic(8) || claim kind || regime || zk-Hem proof`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = PROOF_MAGIC.to_vec();
        out.push(self.claim_tag);
        out.push(self.regime as u8);
        out.extend_from_slice(&self.proof.to_bytes());
        out
    }

    /// Strict decoding against the statement the proof is for.
    pub fn from_bytes(bytes: &[u8], statement: &TransparentStatement) -> Option<Self> {
        let rest = bytes.strip_prefix(PROOF_MAGIC.as_slice())?;
        let (&claim_tag, rest) = rest.split_first()?;
        let (&regime, rest) = rest.split_first()?;
        if claim_tag != statement.proof_tag() {
            return None;
        }
        let regime = WhirSecurityRegime::from_u8(regime)?;
        let shape = statement.shape()?;
        Some(Self {
            claim_tag,
            regime,
            proof: ZkHemProof::from_bytes(rest, &shape, regime)?,
        })
    }
}

/// Prove a statement. `seed` must be uniform and secret.
pub fn prove_transparent(
    statement: &TransparentStatement,
    witness: &OwnershipWitness,
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
) -> Result<TransparentProof, OwnershipError> {
    if !statement.is_well_formed() {
        return Err(OwnershipError::MalformedStatement);
    }
    let (shape, assignment) = match (statement.encoding, witness) {
        (KeyEncoding::Compressed, _) => synthesize_ownership(&statement.ownership, witness)?,
        (KeyEncoding::Uncompressed, OwnershipWitness::Secp256k1Key(key)) => {
            let o = &statement.ownership;
            if uncompressed_hash160(key).map(LegacyClaim::BitcoinHash160) != Some(o.claim.clone())
                || migration_nullifier(NullifierCurve::Secp256k1, key, &o.migration_domain)
                    != o.nullifier
            {
                return Err(OwnershipError::WitnessMismatch);
            }
            let public = o
                .public_inputs()
                .ok_or(OwnershipError::MalformedStatement)?;
            build_uncompressed(&public, key)
        }
        _ => return Err(OwnershipError::WitnessMismatch),
    };
    let proof = protocol::prove(
        &shape,
        assignment,
        &statement.transcript(regime),
        regime,
        seed,
    )
    .map_err(OwnershipError::Proof)?;
    Ok(TransparentProof {
        claim_tag: statement.proof_tag(),
        regime,
        proof,
    })
}

/// Verify a proof against a statement under the regime the verifier requires.
pub fn verify_transparent(
    statement: &TransparentStatement,
    regime: WhirSecurityRegime,
    proof: &TransparentProof,
) -> bool {
    if proof.regime != regime || proof.claim_tag != statement.proof_tag() {
        return false;
    }
    let (Some(shape), Some(public_inputs)) =
        (statement.shape(), statement.ownership.public_inputs())
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

// ============================================================================
// The relation of an uncompressed key
// ============================================================================

/// `1 <= k < n`, `HASH160(04 || x || y) = claim` for `(x, y) = [k] G`, and the nullifier
/// of `k`: the `HASH160` relation of [`crate::hem::relations`] with the other encoding
/// of the same point. Public inputs in the same order: the claim (160 bits), the
/// nullifier chaining value (256), the nullifier (256).
fn build_uncompressed(public: &[F], key_be: &[u8; 32]) -> (Shape, Vec<F>) {
    assert_eq!(public.len(), 160 + 512);
    let mut cs = ConstraintSystem::new();
    let public: Vec<Lc> = public.iter().map(|&v| cs.public_input(v).into()).collect();
    let (claim, rest) = public.split_at(160);
    let (midstate, nullifier) = rest.split_at(256);
    let pin = |cs: &mut ConstraintSystem, got: &[Lc], want: &[Lc]| {
        for (g, w) in got.chunks(60).zip(want.chunks(60)) {
            cs.enforce_equal(&pack_bits(g), &pack_bits(w));
        }
    };

    let secret = alloc_bits(&mut cs, key_be);
    // The big-endian key bytes as little-endian scalar bits.
    let key: Vec<Lc> = secret.chunks(8).rev().flatten().cloned().collect();
    secp256k1_enforce_scalar_range(&mut cs, &key);
    let public_key = secp256k1_fixed_base_mul(&mut cs, &key);
    let mut encoding = const_bits(&[0x04]);
    encoding.extend(public_key.uncompressed_bits().into_iter().flatten());
    let digest = hash160(&mut cs, &encoding);
    pin(&mut cs, &digest, claim);

    let midstate: Vec<Word> = midstate
        .chunks(32)
        .map(|w| Word::from_bits(w.to_vec()))
        .collect();
    let midstate: &[Word; 8] = midstate.as_slice().try_into().expect("eight words");
    let digest = sha256_from_midstate(&mut cs, midstate, 64, &secret);
    pin(&mut cs, &digest, nullifier);
    cs.finish()
}

fn build_uncompressed_shape() -> Shape {
    let mut key = [0u8; 32];
    key[31] = 1;
    let (shape, mut assignment) = build_uncompressed(&[F::ZERO; 160 + 512], &key);
    dregg_sig_asm::volatile_fill(&mut assignment, F::ZERO);
    shape
}

#[cfg(feature = "std")]
fn uncompressed_shape() -> Arc<Shape> {
    static SHAPE: std::sync::OnceLock<Arc<Shape>> = std::sync::OnceLock::new();
    SHAPE
        .get_or_init(|| Arc::new(build_uncompressed_shape()))
        .clone()
}

#[cfg(not(feature = "std"))]
fn uncompressed_shape() -> Arc<Shape> {
    Arc::new(build_uncompressed_shape())
}

#[cfg(test)]
mod tests {
    use super::super::vectors::unhex;
    use super::*;
    use crate::hem::relations::{
        OwnershipProof, bip32_derive, bitcoin_hash160, prove_ownership, verify_ownership,
    };

    const REGIME: WhirSecurityRegime = WhirSecurityRegime::BciksJohnsonQrom128;
    const PQ: [u8; 32] = [0x51; 32];
    const DOMAIN: [u8; 32] = [0x2c; 32];
    const EPOCH: u64 = 7;
    const KEY: [u8; 32] = [
        0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x0f, 0xed, 0xcb, 0xa9, 0x87, 0x65, 0x43,
        0x21, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x01,
    ];

    // zcash-test-vectors unified_address.json: the P2PKH receiver for the root seed
    // 00 01 .. 1f at (account, address index).
    const P2PKH_VECTORS: [(u32, u32, &str); 3] = [
        (0, 0, "7bb83570b8fae146e03c5331a020b1e0892f631d"),
        (0, 3, "a7244a362f49f29644a955cf0039b88a61657861"),
        (0, 4, "e256dcb03e05dde7c91212b47a7461311c415059"),
    ];

    fn seed() -> Vec<u8> {
        (0..32).collect()
    }

    #[test]
    fn seed_addresses_match_the_zcash_vectors() {
        for (account, index, want) in P2PKH_VECTORS {
            let path = bip44_path(Network::Main, account, 0, index).unwrap();
            let node = bip32_derive(&seed(), &path).unwrap();
            let st = TransparentStatement::derive_from_seed(
                Network::Main,
                &OwnershipWitness::Bip32Seed(seed()),
                account,
                0,
                index,
                PQ,
                DOMAIN,
                EPOCH,
            )
            .unwrap();
            assert_eq!(st.hash160().unwrap().to_vec(), unhex(want));
            assert_eq!(
                sha2_native::hash160(&node.public_key()).to_vec(),
                unhex(want)
            );
            let address = st.address().unwrap();
            assert!(address.starts_with("t1"), "{address}");
            assert!(st.is_for_address(&address));
            assert!(st.is_well_formed());
            assert_eq!(TransparentStatement::from_bytes(&st.to_bytes()), Some(st));
        }
        assert!(bip44_path(Network::Main, 0, 2, 0).is_none());
        assert!(bip44_path(Network::Main, BIP32_HARDENED, 0, 0).is_none());
    }

    #[test]
    fn hidden_key_statement_and_encoding() {
        let w = OwnershipWitness::Secp256k1Key(KEY);
        let st = TransparentStatement::derive_hidden(
            Network::Main,
            KeyEncoding::Compressed,
            &w,
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        assert_eq!(st.hash160(), bitcoin_hash160(&KEY));
        let address = st.address().unwrap();
        assert!(address.starts_with("t1"));
        assert!(st.is_for_address(&address));
        let test = TransparentStatement {
            network: Network::Test,
            ..st.clone()
        };
        assert!(test.address().unwrap().starts_with("tm"));
        assert!(
            TransparentStatement::derive_hidden(
                Network::Main,
                KeyEncoding::Uncompressed,
                &OwnershipWitness::Bip32Seed(seed()),
                PQ,
                DOMAIN,
                EPOCH
            )
            .is_none()
        );
        assert!(!test.is_for_address(&address));
        assert!(!st.is_for_address(&encode_transparent(
            Network::Main,
            TransparentKind::P2sh,
            &st.hash160().unwrap()
        )));
        assert!(!st.is_for_address("t1invalid"));

        let bytes = st.to_bytes();
        assert_eq!(TransparentStatement::from_bytes(&bytes), Some(st.clone()));
        assert_ne!(test.to_bytes(), bytes);
        assert!(TransparentStatement::from_bytes(&bytes[..bytes.len() - 1]).is_none());
        let mut bad = bytes.clone();
        bad[29] = 2;
        assert!(TransparentStatement::from_bytes(&bad).is_none());
        let mut bad = bytes.clone();
        bad[30] = 7;
        assert!(TransparentStatement::from_bytes(&bad).is_none());
        // The underlying statement's own encoding is not this statement's.
        assert!(TransparentStatement::from_bytes(&st.ownership.to_bytes()).is_none());

        // Claims this module does not admit: other kinds, and paths that are not BIP 44
        // address paths of the network.
        let eth =
            OwnershipStatement::derive(&ClaimKind::EthereumAddress, &w, PQ, DOMAIN, EPOCH).unwrap();
        let wrapped = TransparentStatement {
            network: Network::Main,
            encoding: KeyEncoding::Compressed,
            ownership: eth,
        };
        assert!(!wrapped.is_well_formed());
        assert!(wrapped.address().is_none());
        assert!(TransparentStatement::from_bytes(&wrapped.to_bytes()).is_none());
        let seed_w = OwnershipWitness::Bip32Seed(seed());
        let main = TransparentStatement::derive_from_seed(
            Network::Main,
            &seed_w,
            0,
            0,
            0,
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        let as_test = TransparentStatement {
            network: Network::Test,
            ..main.clone()
        };
        assert!(main.is_well_formed());
        assert!(!as_test.is_well_formed(), "coin type 133 is not testnet's");
        let short = OwnershipStatement::derive(
            &ClaimKind::Bip32Secp256k1 {
                path: alloc::vec![44 | BIP32_HARDENED],
            },
            &seed_w,
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        assert!(
            !TransparentStatement {
                network: Network::Main,
                encoding: KeyEncoding::Compressed,
                ownership: short
            }
            .is_well_formed()
        );
        // Seed provenance is for compressed keys.
        assert!(
            !TransparentStatement {
                encoding: KeyEncoding::Uncompressed,
                ..main
            }
            .is_well_formed()
        );
    }

    #[test]
    fn uncompressed_key_statement_and_proof() {
        // The secret key 1: HASH160 of the uncompressed and compressed generator, the
        // payloads of the Bitcoin addresses 1EHNa6Q4Jz2uvNExL497mE43ikXhwF6kZm and
        // 1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH.
        let mut one = [0u8; 32];
        one[31] = 1;
        assert_eq!(
            uncompressed_hash160(&one).unwrap().to_vec(),
            unhex("91b24bf9f5288532960ac687abb035127b1d28a5")
        );
        assert_eq!(
            bitcoin_hash160(&one).unwrap().to_vec(),
            unhex("751e76e8199196d454941c45d1b3a323f1433bd6")
        );
        assert!(uncompressed_hash160(&[0; 32]).is_none());

        let w = OwnershipWitness::Secp256k1Key(KEY);
        let derive = |encoding| {
            TransparentStatement::derive_hidden(Network::Main, encoding, &w, PQ, DOMAIN, EPOCH)
                .unwrap()
        };
        let (st, compressed) = (
            derive(KeyEncoding::Uncompressed),
            derive(KeyEncoding::Compressed),
        );
        assert_eq!(st.hash160(), uncompressed_hash160(&KEY));
        assert_ne!(st.hash160(), compressed.hash160());
        // One key, one nullifier, whichever address is migrated.
        assert_eq!(st.ownership.nullifier, compressed.ownership.nullifier);
        assert_eq!(
            TransparentStatement::from_bytes(&st.to_bytes()),
            Some(st.clone())
        );
        assert_ne!(st.to_bytes(), compressed.to_bytes());
        let mut bad = st.to_bytes();
        bad[30] = 2;
        assert!(TransparentStatement::from_bytes(&bad).is_none());

        let proof = prove_transparent(&st, &w, REGIME, &[3; 32]).unwrap();
        let bytes = proof.to_bytes();
        assert!(verify_transparent(
            &st,
            REGIME,
            &TransparentProof::from_bytes(&bytes, &st).unwrap()
        ));
        // The same payload claimed for the other encoding is another statement: the key
        // behind it would have to hash to it in compressed form.
        let relabelled = TransparentStatement {
            encoding: KeyEncoding::Compressed,
            ..st.clone()
        };
        assert!(TransparentProof::from_bytes(&bytes, &relabelled).is_none());
        assert_eq!(
            prove_transparent(&relabelled, &w, REGIME, &[3; 32]).err(),
            Some(OwnershipError::WitnessMismatch)
        );
        // A proof for the compressed address does not verify for the uncompressed one.
        let other = prove_transparent(&compressed, &w, REGIME, &[3; 32]).unwrap();
        assert!(TransparentProof::from_bytes(&other.to_bytes(), &st).is_none());
        let forced = TransparentProof {
            claim_tag: st.proof_tag(),
            regime: REGIME,
            proof: other.proof.clone(),
        };
        assert!(!verify_transparent(&st, REGIME, &forced));
        // Public fields and proof bytes.
        let mut claim = st.hash160().unwrap();
        claim[19] ^= 1;
        for changed in [
            TransparentStatement {
                network: Network::Test,
                ..st.clone()
            },
            TransparentStatement {
                ownership: OwnershipStatement {
                    claim: LegacyClaim::BitcoinHash160(claim),
                    ..st.ownership.clone()
                },
                ..st.clone()
            },
            TransparentStatement {
                ownership: OwnershipStatement {
                    nullifier: [1; 32],
                    ..st.ownership.clone()
                },
                ..st.clone()
            },
        ] {
            assert!(!verify_transparent(&changed, REGIME, &proof), "{changed:?}");
        }
        let mut tampered = bytes.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 1;
        assert!(
            TransparentProof::from_bytes(&tampered, &st)
                .is_none_or(|p| !verify_transparent(&st, REGIME, &p))
        );
        let mut other_key = KEY;
        other_key[0] ^= 1;
        assert_eq!(
            prove_transparent(
                &st,
                &OwnershipWitness::Secp256k1Key(other_key),
                REGIME,
                &[3; 32]
            )
            .err(),
            Some(OwnershipError::WitnessMismatch)
        );
        // The relation has no S-box rows and does not depend on the witness.
        let shape = uncompressed_shape();
        assert_eq!(shape.num_sbox, 0);
        let (built, z) = build_uncompressed(&st.ownership.public_inputs().unwrap(), &KEY);
        assert!(built.is_satisfied(&z));
        assert_eq!(built.digest(), shape.digest());
    }

    #[cfg(feature = "std")]
    #[test]
    fn registry_identifier_is_the_zcash_address() {
        let w = OwnershipWitness::Secp256k1Key(KEY);
        let st = TransparentStatement::derive_hidden(
            Network::Main,
            KeyEncoding::Compressed,
            &w,
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        let binding = st.binding().unwrap();
        // The same key hash as a Bitcoin credential has another identifier, and so does
        // the testnet address.
        assert_ne!(binding.legacy_id, st.ownership.binding().legacy_id);
        assert_eq!(binding.nullifier, st.ownership.nullifier);
        let test = TransparentStatement {
            network: Network::Test,
            ..st.clone()
        };
        assert_ne!(test.binding().unwrap().legacy_id, binding.legacy_id);
        // Seed provenance of the same address has the same identifier.
        let seed_st = TransparentStatement::derive_from_seed(
            Network::Main,
            &OwnershipWitness::Bip32Seed(seed()),
            0,
            0,
            0,
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        let key = bip32_derive(&seed(), &bip44_path(Network::Main, 0, 0, 0).unwrap()).unwrap();
        let hidden = TransparentStatement::derive_hidden(
            Network::Main,
            KeyEncoding::Compressed,
            &OwnershipWitness::Secp256k1Key(key.private_key),
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        assert_eq!(
            seed_st.binding().unwrap().legacy_id,
            hidden.binding().unwrap().legacy_id
        );
        assert_eq!(seed_st.ownership.nullifier, hidden.ownership.nullifier);
    }

    #[test]
    fn hidden_key_proof_roundtrip_and_separation() {
        let w = OwnershipWitness::Secp256k1Key(KEY);
        let st = TransparentStatement::derive_hidden(
            Network::Main,
            KeyEncoding::Compressed,
            &w,
            PQ,
            DOMAIN,
            EPOCH,
        )
        .unwrap();
        let proof = prove_transparent(&st, &w, REGIME, &[3; 32]).unwrap();
        let bytes = proof.to_bytes();
        let decoded = TransparentProof::from_bytes(&bytes, &st).unwrap();
        assert_eq!(decoded, proof);
        assert!(verify_transparent(&st, REGIME, &decoded));

        // Network, every field of the underlying statement, the regime.
        let o = &st.ownership;
        let mut other_claim = st.hash160().unwrap();
        other_claim[0] ^= 1;
        for other in [
            TransparentStatement {
                network: Network::Test,
                ..st.clone()
            },
            TransparentStatement {
                ownership: OwnershipStatement {
                    epoch: 8,
                    ..o.clone()
                },
                ..st.clone()
            },
            TransparentStatement {
                ownership: OwnershipStatement {
                    migration_domain: [1; 32],
                    ..o.clone()
                },
                ..st.clone()
            },
            TransparentStatement {
                ownership: OwnershipStatement {
                    pq_commitment: [1; 32],
                    ..o.clone()
                },
                ..st.clone()
            },
            TransparentStatement {
                ownership: OwnershipStatement {
                    nullifier: [1; 32],
                    ..o.clone()
                },
                ..st.clone()
            },
            TransparentStatement {
                ownership: OwnershipStatement {
                    claim: LegacyClaim::BitcoinHash160(other_claim),
                    ..o.clone()
                },
                ..st.clone()
            },
        ] {
            assert!(!verify_transparent(&other, REGIME, &proof), "{other:?}");
        }
        assert!(!verify_transparent(
            &st,
            WhirSecurityRegime::Cdhz25JohnsonQrom128,
            &proof
        ));
        for at in [8, 9, bytes.len() / 2, bytes.len() - 1] {
            let mut tampered = bytes.clone();
            tampered[at] ^= 1;
            assert!(
                TransparentProof::from_bytes(&tampered, &st)
                    .is_none_or(|p| !verify_transparent(&st, REGIME, &p)),
                "byte {at}"
            );
        }

        // A Bitcoin proof for the same key hash is not a Zcash proof, and the reverse.
        let bitcoin = prove_ownership(o, &w, REGIME, &[3; 32]).unwrap();
        assert!(verify_ownership(o, REGIME, &bitcoin));
        assert!(TransparentProof::from_bytes(&bitcoin.to_bytes(), &st).is_none());
        let relabelled_proof = TransparentProof {
            claim_tag: proof.claim_tag,
            regime: REGIME,
            proof: bitcoin.proof.clone(),
        };
        assert!(!verify_transparent(&st, REGIME, &relabelled_proof));
        assert!(OwnershipProof::from_bytes(&bytes, o).is_none());
        let as_bitcoin =
            OwnershipProof::from_bytes(&[b"QSHEMOW1".as_slice(), &bytes[8..]].concat(), o).unwrap();
        assert!(!verify_ownership(o, REGIME, &as_bitcoin));

        // A witness for another key is refused.
        let mut other_key = KEY;
        other_key[31] ^= 1;
        assert_eq!(
            prove_transparent(
                &st,
                &OwnershipWitness::Secp256k1Key(other_key),
                REGIME,
                &[3; 32]
            )
            .err(),
            Some(OwnershipError::WitnessMismatch)
        );
    }

    /// The BIP 44 relation has two non-hardened steps; run with the measurements:
    /// `cargo test --release -p dregg-sig-migrate --features std --lib --
    /// hem::zcash::transparent::tests::seed_provenance --ignored --nocapture`
    #[test]
    #[ignore = "a 2^20-row relation"]
    fn seed_provenance_proof_roundtrip() {
        let w = OwnershipWitness::Bip32Seed(seed());
        let st =
            TransparentStatement::derive_from_seed(Network::Main, &w, 0, 0, 3, PQ, DOMAIN, EPOCH)
                .unwrap();
        let t = std::time::Instant::now();
        let proof = prove_transparent(&st, &w, REGIME, &[3; 32]).unwrap();
        let prove_s = t.elapsed().as_secs_f64();
        let bytes = proof.to_bytes();
        let t = std::time::Instant::now();
        assert!(verify_transparent(
            &st,
            REGIME,
            &TransparentProof::from_bytes(&bytes, &st).unwrap()
        ));
        let shape = ownership_shape(&st.ownership).unwrap();
        std::println!(
            "HEM_ZCASH statement=\"transparent-p2pkh seed m/44'/133'/0'/0/3\" regime={} \
             padded_rows=2^{} vars={} prove_s={prove_s:.2} verify_warm_ms={:.1} proof_bytes={}",
            REGIME as u8,
            shape.log_rows,
            shape.num_vars,
            t.elapsed().as_secs_f64() * 1e3,
            bytes.len()
        );
        // Another index of the same seed is another statement.
        let other =
            TransparentStatement::derive_from_seed(Network::Main, &w, 0, 0, 4, PQ, DOMAIN, EPOCH)
                .unwrap();
        assert!(!verify_transparent(&other, REGIME, &proof));
        assert_eq!(
            prove_transparent(
                &st,
                &OwnershipWitness::Bip32Seed(alloc::vec![9; 32]),
                REGIME,
                &[3; 32]
            )
            .err(),
            Some(OwnershipError::WitnessMismatch)
        );
    }
}
