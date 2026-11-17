#![no_std]
#![forbid(unsafe_code)]
#![allow(clippy::chunks_exact_to_as_chunks, clippy::manual_is_multiple_of)]
//! Proofs that the holder of a legacy credential (a Bitcoin or Ethereum address, an
//! Ed25519 key, a BIP-32 seed) authorises a post-quantum address, and the registry that
//! records each migration once.
//!
//! * [`hem::relations`]: the ownership statements and their zk-Hem proofs.
//! * [`hem::registry`] (`std`): the durable one-way nullifier registry.
//! * [`hem::collab`]: the threshold prover: a quorum of custodians proves a statement on
//!   a secret-shared assignment, with its authenticated engine and preprocessing.
//! * [`secp256k1_ct`], [`ed25519_ct`]: constant-time native references the relations are
//!   tested against.
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

#[allow(dead_code)]
mod bls12_381;
#[allow(dead_code)]
mod limbs;
#[allow(dead_code)]
mod pallas;
mod scalar;
