//! The legacy commitment a registry record is indexed by. Transitional: `hem::registry`
//! and `hem::relations` are the only users.

/// Supported classical-to-PQ migration target commitment kinds.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LegacyCommitmentKind {
    /// Bitcoin `HASH160 = RIPEMD160(SHA256(compressed_pk_33))` (`20 B` P2PKH / P2WPKH).
    BitcoinHash160([u8; 20]),
    /// Bitcoin BIP-341 Taproot tweaked x-only output key `x(P_even + H_TapTweak(x(P_even)) * G)` (`32 B`).
    BitcoinTaprootXOnly([u8; 32]),
    /// Ethereum EOA `Keccak256(uncompressed_pk_64)[12..32]` (`20 B`).
    EthereumKeccak20([u8; 20]),
    /// SLIP-0010 Ed25519 hardened chain key commitment (RFC 8032 compressed public key, 32 bytes).
    Slip0010Ed25519([u8; 32]),
}
