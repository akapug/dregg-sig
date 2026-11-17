//! Constructor checks of a general-quorum custody share: what is left of the share type
//! of the removed distributed prover, kept because a `threshold_mpc` test still calls it
//! at this path. It validates and holds nothing.
use crate::{
    outer_mpc::Error,
    threshold_mpc::{MacKeyShare, ThresholdConfig},
};
use alloc::vec::Vec;

pub(crate) struct CoZkCustodianShare(());

impl CoZkCustodianShare {
    /// `(t, n)` bytewise Shamir custody: `party` must be in the quorum, with one channel
    /// key per other quorum member, and its share must convert to an additive one.
    pub(crate) fn new_shamir(
        party: usize,
        config: ThresholdConfig,
        _session: [u8; 32],
        witness: [u8; 32],
        _entropy: [u8; 32],
        peer_keys: Vec<[u8; 32]>,
        _mac_keys: MacKeyShare,
    ) -> Result<Self, Error> {
        Self::check(party, &config, &peer_keys)?;
        config.shamir_contribution(party, &witness)?;
        Ok(Self(()))
    }

    /// n-of-n XOR custody over a roster of 2 to 64 members.
    pub(crate) fn new_additive(
        party: usize,
        parties: usize,
        _session: [u8; 32],
        _witness: [u8; 32],
        _entropy: [u8; 32],
        peer_keys: Vec<[u8; 32]>,
        _mac_keys: MacKeyShare,
    ) -> Result<Self, Error> {
        if !(2..=64).contains(&parties) {
            return Err(Error::InvalidConfiguration);
        }
        let config = ThresholdConfig::new(parties, parties, (0..parties).collect())?;
        Self::check(party, &config, &peer_keys)?;
        Ok(Self(()))
    }

    fn check(party: usize, config: &ThresholdConfig, peer_keys: &[[u8; 32]]) -> Result<(), Error> {
        if !config.quorum().contains(&party) || peer_keys.len() != config.quorum().len() - 1 {
            return Err(Error::InvalidConfiguration);
        }
        Ok(())
    }
}
