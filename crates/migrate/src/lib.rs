#![no_std]
#![forbid(unsafe_code)]
#![allow(clippy::chunks_exact_to_as_chunks, clippy::manual_is_multiple_of)]
//! Proofs that the holder of a legacy credential (a Bitcoin or Ethereum address, an
//! Ed25519 key, a BIP-32 seed) authorises a post-quantum address, and the registry that
//! records each migration once.
//!
//! * [`hem::relations`]: the ownership statements and their zk-Hem proofs.
//! * [`hem::registry`] (`std`): the durable one-way nullifier registry.
//! * [`hem::collab`]: proving over a secret-shared witness.
//! * [`secp256k1_ct`], [`ed25519_ct`]: constant-time native references the relations are
//!   tested against.
//! * [`threshold_mpc`], [`threshold_prep`]: an authenticated general-quorum arithmetic
//!   engine and its preprocessing. No prover in this crate runs on it.
//!
//! A proof shows authorisation by whoever holds the secret. It does not disable the legacy
//! key and does not prevent a second migration; the chain or the registry must. See
//! `SECURITY.md` for what each statement proves and for the status of the proof system.
extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod ed25519_ct;
pub mod hem;
pub mod secp256k1_ct;

// The general-quorum engine below lost its only caller when the old distributed prover
// was removed. Its public surface is the preprocessing ceremony and the share types; the
// online engine and the field layer under it are reachable only from tests.
#[allow(dead_code)]
mod bls12_381;
#[allow(dead_code)]
mod circuit;
#[cfg(test)]
mod custody_share;
#[allow(dead_code)]
mod limbs;
#[allow(dead_code)]
mod outer_mpc;
#[allow(dead_code)]
mod pallas;
mod scalar;
mod secret;
#[allow(dead_code)]
pub mod threshold_mpc;
pub mod threshold_prep;

#[cfg(test)]
pub(crate) use custody_share::CoZkCustodianShare;
pub use threshold_mpc::{
    poly0x11b_to_t3_byte_ct, poly0x11b_to_t3_bytes32_ct, t3_to_poly0x11b_byte_ct,
    t3_to_poly0x11b_bytes32_ct,
};
