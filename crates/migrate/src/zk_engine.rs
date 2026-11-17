//! The statement shape `hem::registry::MigrationBinding::from_statement` reads.
//! Transitional: nothing produces or proves this statement any more.

use crate::legacy::LegacyCommitmentKind;
use dregg_sig_addr::QsagAddress;

/// Public statement of a Classical-to-PQ Migration ZK Proof (`Π_zk_migrate`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MigrationStatement {
    pub legacy_commitment: LegacyCommitmentKind,
    pub target_pq_address: QsagAddress,
    pub epoch_anchor: u64,
    /// Replay domain shared by every destination in a migration campaign.
    pub migration_domain: [u8; 32],
    /// Context-bound nullifier; replay tracking must be supplied by the caller.
    pub migration_nullifier: [u64; 4],
    /// Reserved public binding; must be zero in protocol version 3.
    pub witness_anchor: [u64; 4],
}
