//! Threshold proving: the zk-Hem prover run by a quorum of custodians on a secret-shared
//! assignment.
//!
//! * [`net`]: authenticated, encrypted message transport between custodians.
//! * [`engine`]: MAC-authenticated additive sharing over Goldilocks (SPDZ).
//! * [`custody`]: from `(k, n)` Shamir or XOR custody shares of a secret to authenticated
//!   shares of its bits.
//! * [`prep`]: the dealerless ceremony that produces [`engine::Preprocessing`].
//! * [`witgen`]: from shares of the secret's bits to shares of the whole assignment.
//! * [`prover`]: one custodian's side of the proof, [`prover::prove_party`].
//! * [`prove_ownership_party`]: the three in order, from a custody share to a proof.
//! * [`verify_threshold_ownership`]: the verifier for ownership statements.
//!
//! # What the proof is
//!
//! A [`ZkHemSplitProof`] is a zk-Hem proof whose commitment is a list of `N` roots, one
//! per custodian, each over that custodian's additive shares of the five committed
//! tables. The verifier is `zk_hem::protocol::verify_split`: the steps of
//! `protocol::verify` (the same function, `replay_front`, runs them for both), then WHIR
//! with every Stage-0 fiber checked against each root and the opened share symbols
//! summed. Its transcript has its own relation tag and its wire form its own magic
//! (`QSAGZKS1`). The single-prover `prove`, `verify` and their proof bytes are unchanged;
//! a split proof with one root is accepted by `verify_split` but is a different format,
//! not the single-prover one.
//!
//! WHIR is kept. The codeword of the assignment table determines the table whatever the
//! blinders (`a_complete_stage0_codeword_reveals_the_table_whatever_the_blinders`), so it
//! cannot be opened among custodians for one of them to hash; each custodian therefore
//! hashes its own share codewords, which is the interleaved code of 2026/729 Section 3
//! (`code-based-scalable-collaborative-snarks-lagrange-2026-729`). Everything WHIR does
//! after Stage 0 is a function of the blended word `U`, which is uniform given the public
//! claim and is opened to the quorum
//! (`the_blended_word_and_companion_claims_are_simulated_from_the_public_claim`).
//!
//! # The protocol ([`prover::prove_party`])
//!
//! Every custodian holds authenticated shares of the assignment `z` and one-use
//! preprocessing (Beaver triples and uniform values). All messages are broadcast.
//!
//! 1. Table. The constant and the public inputs are set to shares of the public values.
//!    The masking variables, the coefficients of both sumcheck masks and the Stage-0
//!    blinders are preprocessed uniform values, so no custodian knows them and they are
//!    authenticated like the rest of the table.
//! 2. Commit. Each custodian commits to the value part of its table shares and to four
//!    companion tables it samples itself, and broadcasts its root. The transcript binds
//!    the list of roots.
//! 3. Row sumcheck of `eq (a b - c)`. Per round and pair of rows two products
//!    (`a_lo b_lo` and `(a_hi - a_lo)(b_hi - b_lo)`); the middle coefficient comes from the
//!    shared running claim. Round 0 multiplies base-field values (one triple each), later
//!    rounds extension-field values (sixteen triples each). Opened: the mask sum, the
//!    Beaver openings, the masked round polynomials, then `(Az, Bz, Cz)(rx)`.
//! 4. Column sumcheck of `M(rx, y) Z(y)`: linear, no products. Opened: the mask sum and
//!    the masked round polynomials.
//! 5. Zero test. The custodians replay the verifier on the messages so far and obtain
//!    the linear claim `<Z, K> = V`. They open `rho (<Z, K> - V)` for a uniform shared
//!    `rho`, computed from the authenticated table. Nonzero: abort with
//!    [`prover::ProveError::Unsatisfied`].
//! 6. Each custodian broadcasts its shares of the four companion claims and, after
//!    `beta`, its share of `U`. These are not authenticated.
//! 7. Each custodian runs WHIR's public stages on `U`, opens its own Stage-0 leaves at
//!    the queried fibers, assembles the proof and verifies it. A proof that does not
//!    verify is [`prover::ProveError::Rejected`].
//!
//! The MAC check ([`engine::Engine::check`]) runs before every opening of steps 3 to 5
//! other than a Beaver opening: before each mask sum, each round polynomial, the row
//! values and the zero-test value, and once more after the zero-test value. A Beaver
//! opening `x - a` is uniform whatever was sent before it, so it may precede the check;
//! every other opened value is a function of earlier openings and is sent only once
//! those are verified.
//!
//! # Corruption threshold and abort
//!
//! The quorum's sharing is additive. Privacy is claimed against any `N - 1` custodians of
//! the quorum that deviate arbitrarily; with `(k, n)` Shamir custody the quorum has `k`
//! members, so against fewer than `k` custodians overall. This is the proving quorum's
//! bound and is the custody threshold; it is not the `t <= (1/2 - eps) N` of 2026/729,
//! which packs shares. Soundness of the proof is zk-Hem's and needs no honest custodian.
//!
//! Abort is not identifiable and not fair. Any custodian can stop the run; the one that
//! receives the last Stage-0 opening can keep the proof. A run that aborts has consumed
//! its preprocessing: a retry needs fresh material, and a deployment must not reuse a
//! store after any error.
//!
//! # Can a deviating custodian learn another custodian's share?
//!
//! The question is whether a selectively wrong share codeword, opened symbol, sumcheck
//! message, MAC share or input lets the deviator learn more than the fact that the run
//! aborted. The argument, by message an honest custodian sends:
//!
//! * Beaver openings, the zero-test product and the input masks are one-time-padded by
//!   preprocessed uniform values; they are uniform whatever the others did.
//! * Mask sums, round polynomials and row values are sent only after the MAC check has
//!   accepted every earlier opening, so they are the honest protocol's values on the
//!   authenticated shares. For a satisfying assignment those are simulated from the
//!   public output by the single-prover simulators (`libra_real_eq_sim`, the masking
//!   rows). For an assignment that does not satisfy the relation (a custodian that input
//!   something else than its share produces one) the row values are still uniform and
//!   the round polynomials are still masked; what they would let a verifier derive is
//!   the value `<Z, K> - V`, and that is exactly what step 5 refuses to release: it opens
//!   `rho (<Z, K> - V)`, which is zero or uniform.
//! * Companion claims and `U` are sent only after the zero test passed, so `<Z, K> = V`
//!   holds for the authenticated table, and they are then a function of `V` and of
//!   uniform companions. They are unauthenticated: a deviator can send anything, after
//!   seeing the honest ones, but learns nothing from doing so.
//! * Stage-0 leaves. An honest custodian opens the symbols of its own share codewords at
//!   the fibers the transcript selects, at most `Layout::blind_cells` symbols. Its table
//!   holds that many uniform authenticated cells no custodian knows, so those symbols
//!   are uniform for every set of queried fibers of that size, whatever tables or word
//!   the deviator sent to steer the queries.
//! * The verdict. Whether the assembled proof verifies is decided by the deviator's own
//!   tables, word and leaves against public values; it does not depend on an honest
//!   share beyond the values above.
//!
//! So a wrong share codeword is not checked against the authenticated shares by a
//! separate consistency protocol: it makes the proof fail and nothing else. The check
//! that is needed, and present, is the zero test, which closes the one leak the plain
//! design had (an unsatisfying input turning the companion claims into `<Z, K> - V`).
//!
//! What is proven and what is not. SPDZ's MAC check and Beaver multiplication are from
//! the literature (Damgard, Pastro, Smart, Zakarias 2012; Damgard et al. 2013) for a
//! reactive arithmetic functionality. The simulators for the masked sumcheck, the
//! companion blend and the opened symbols are the theorems of
//! `ZkHemSoundnessAndPrivacy.lean` for the single prover. Their composition into the
//! argument above is this module's claim: it is not proven, not mechanized, and the
//! "uniform for every set of queried fibers" step relies on that file's
//! `opened_symbols_perfectly_simulated`. The tests play the deviator
//! (`a_deviating_custodian_makes_every_honest_custodian_abort`: wrong table, round
//! share, word, leaf, MAC share, value share; `an_unsatisfying_assignment_aborts_at_the_zero_test`;
//! `engine` and `custody` tests for wrong MAC-check shares, equivocation and non-bit
//! inputs) and check that every honest custodian aborts, at the same point and after
//! the same number of rounds for two witnesses of one statement. They do not test that the
//! deviator's view has the same distribution for both witnesses.
//!
//! # S-box rows
//!
//! `a^7 = c` rows are refused ([`prover::ProveError::SboxRows`]). On shares a round
//! polynomial of such a row needs seven seventh powers per pair, 28 products in depth
//! three against two in depth one. The ownership relations have none.
//!
//! # Witness generation
//!
//! [`prove_ownership_party`] is one custodian's whole run: [`custody::input_secret_bits`]
//! turns its custody share into authenticated shares of the secret's bits,
//! [`witgen::generate`] computes authenticated shares of every other variable, and
//! [`prover::prove_party`] proves. No custodian holds the secret, a variable of the
//! assignment or another custodian's share at any point.
//!
//! The relation says how each variable follows from earlier ones: the gadgets allocate
//! with `ConstraintSystem::alloc_defined`, and `relations::ownership_definitions` returns
//! the definitions of a statement
//! (`witgen::tests::every_ownership_statement_defines_every_variable` checks that none is
//! missing for every lock and key source). The subprotocols, their sources and what each
//! opens are in the module documentation of [`witgen`]; malicious security is the
//! engine's MAC check, run before every opening that is masked only if earlier openings
//! were right. No division reveals whether its denominator is zero for a secret that
//! has a valid statement: an addition that can be a doubling selects chord or tangent on
//! shares ([`witgen`], "Divisions by zero").
//!
//! Some relations take inputs beyond the bits of the secret: the length of a master seed,
//! the steps of a hidden derivation path, a Taproot script-tree root. They are hidden
//! from the verifier, not from the provers: every custodian of the quorum knows them
//! ([`CustodyInput`]) and enters them as public constants of the engine, and a seed
//! shorter than 64 bytes is padded with public zeros.
//!
//! Not covered: relations with lookups (a multiplicity is a count over the whole witness;
//! `ConstraintSystem::finish_recorded` refuses them).
//!
//! # Preprocessing
//!
//! The engine consumes Goldilocks triples and uniform values under two Goldilocks MAC
//! keys. [`prep::run_preprocessing`] is the dealerless ceremony that produces every
//! custodian's [`engine::Preprocessing`]: MASCOT-style triple generation and
//! authentication over the OT mesh of `dregg_sig_core::preprocessing`, with security
//! with abort against all members of the quorum but one. It runs all members' steps in
//! one process on separated state and is not a wire protocol; its parameters and what
//! its soundness arguments are worth are in the module documentation of [`prep`].
//! `engine::Dealer` (tests and the `test-dealer` feature only) generates the same
//! material from one seed and knows both keys.
//!
//! `prep::tests::measure_ceremony` on hbox, three members, for the 2,228,208 triples and
//! 9,156 uniform values of the proof stage of one ownership statement: 4,502.5 s
//! (1.25 h) wall-clock on a loaded machine, 8,269.5 s of CPU, 2.02 ms per triple, 55
//! microseconds per uniform value, 74.5 GiB of payload sent per member, 685 MB peak
//! memory; every produced triple and value was reconstructed and checked. Witness
//! generation adds about 1.23 million triples and 0.61 million uniform values per
//! statement, which at these rates is a further 0.7 h; that part was not run.
//! `prep::tests::ceremony_output_drives_the_threshold_prover` runs the ceremony for a
//! small relation (528 triples, 4,424 uniform values), inputs a clear assignment and
//! proves on the result.
//!
//! # Measured cost
//!
//! `tests::measure_threshold_ownership` on hbox (16 cores), default regime, all custodians
//! as threads of one process over sealed channel links, dealer preprocessing. The secret is
//! held as `(N, N + 2)` Shamir shares; each custodian runs [`prove_ownership_party`]. Per
//! custodian (rounds include two per MAC check):
//!
//! | statement | N | stage | triples | uniform values | sent | rounds | MAC checks | time |
//! |---|---|---|---|---|---|---|---|---|
//! | Bitcoin HASH160 | 3 | input | 1,280 | 768 | 62,080 B | 8 | 2 | 0.2 s |
//! | | | witness | 2,151,917 | 603,115 | 79.1 MB | 15,013 | 482 | 5.8 s |
//! | | | proof | 2,228,208 | 9,156 | 88.9 MB | 138 | 39 | 4.4 s |
//! | Ed25519 seed | 3 | input | 1,280 | 768 | 62,080 B | 8 | 2 | 0.2 s |
//! | | | witness | 2,286,466 | 635,671 | 84.0 MB | 14,763 | 660 | 6.2 s |
//! | | | proof | 2,228,208 | 9,156 | 88.9 MB | 138 | 39 | 4.2 s |
//! | Bitcoin HASH160 | 5 | input | 2,304 | 1,280 | 206,080 B | 10 | 2 | 0.3 s |
//! | | | witness | 2,151,917 | 603,115 | 158.2 MB | 15,013 | 482 | 8.2 s |
//! | | | proof | 2,228,208 | 9,156 | 177.8 MB | 138 | 39 | 6.7 s |
//! | HASH160, BIP-32 seed, `m/44'` | 3 | input | 640 | 384 | 31,360 B | 8 | 2 | 0.6 s |
//! | | | witness | 3,363,835 | 910,885 | 123.6 MB | 39,294 | 2,612 | 9.3 s |
//! | | | proof | 8,912,880 | 9,260 | 353.2 MB | 152 | 43 | 17.6 s |
//! | Taproot script tree, seed, hidden path of depth 2 | 3 | input | 1,320 | 792 | 64,000 B | 8 | 2 | 1.2 s |
//! | | | witness | 9,828,350 | 2,747,456 | 361.6 MB | 70,380 | 4,177 | 24.5 s |
//! | | | proof | 17,825,776 | 17,568 | 706.1 MB | 159 | 45 | 28.3 s |
//!
//! Proofs: 1,282,887 B, 1,281,383 B, 2,052,417 B, 1,354,343 B and 2,341,263 B;
//! verification 0.2 to 0.8 s. "Sent" counts every broadcast once per recipient.
//!
//! On a network the witness stage is bound by its rounds: at 50 ms a round, 12.5 min for
//! the HASH160 statement and 33 min for `m/44'` from a seed. Before witness generation
//! was scheduled by dependency ([`witgen`], "Rounds") the same two statements took
//! 515,439 and 817,663 rounds (7.2 h and 11.4 h) with 1,235,043 and 2,064,294 triples.
//! `m/44'/0'/0'/0/0` from a seed, counted by `witgen::tests::measure_chains` and not run:
//! 10,359,511 witness triples, 2,813,971 uniform values and 107,370 rounds (91,388 and
//! two for each of 7,991 MAC checks), 89 min at 50 ms a round.

pub mod custody;
pub mod engine;
pub mod net;
pub mod prep;
pub mod prover;
pub mod witgen;

use dregg_sig_agg::pcs::WhirSecurityRegime;
use dregg_sig_agg::zk_hem::protocol::{ZkHemSplitProof, verify_split};

use alloc::vec::Vec;

use dregg_sig_agg::field::Goldilocks;

use super::relations::{
    OwnershipStatement, ownership_auxiliary_inputs, ownership_definitions, ownership_shape,
    ownership_transcript,
};
use engine::{Engine, Stats};
use net::Transport;

/// Why a custodian's [`prove_ownership_party`] produced no proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThresholdError {
    /// The statement is malformed, or the custody input does not fit it: a share of a
    /// length the key source does not take, a path that the statement does not hide or
    /// that is too long for it, a script-tree root that is missing or not called for.
    Statement,
    Input(custody::InputError),
    Witness(witgen::WitgenError),
    Prove(prover::ProveError),
}

/// The stages of [`prove_ownership_party`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage {
    /// Custody shares to authenticated shares of the secret's bits.
    Input,
    /// Shares of the secret's bits to shares of the assignment.
    Witness,
    /// The proof.
    Proof,
}

/// What one custodian brings to [`prove_ownership_party`].
///
/// `xor_share` is its XOR share of the legacy secret (see
/// [`custody::xor_share_from_shamir`]); no custodian holds more of the secret than that.
/// `path` and `merkle_root` are the parts of the witness that are hidden from the
/// verifier and known to the whole quorum: the derivation path of a statement with a
/// hidden path (empty otherwise) and the script-tree root of a Taproot script-tree
/// lock. The length of a master seed is the length of the share, so the custodians know
/// it too. Custodians that disagree on these values hold inconsistent shares of the
/// inputs, which the engine's MAC check reports like any other wrong share.
#[derive(Clone, Copy, Debug)]
pub struct CustodyInput<'a> {
    pub xor_share: &'a [u8],
    pub path: &'a [u32],
    pub merkle_root: Option<&'a [u8; 32]>,
}

impl<'a> CustodyInput<'a> {
    /// A share of a secret whose statement has no hidden path and no script tree.
    pub fn secret(xor_share: &'a [u8]) -> Self {
        Self {
            xor_share,
            path: &[],
            merkle_root: None,
        }
    }
}

/// Triples and uniform values one custodian consumes in [`prove_ownership_party`], by
/// stage, for a secret of `secret_bytes` bytes. `None` for a malformed statement.
pub fn ownership_demand(
    statement: &OwnershipStatement,
    regime: WhirSecurityRegime,
    parties: usize,
    secret_bytes: usize,
) -> Option<[(Stage, usize, usize); 3]> {
    let (shape, defs) = ownership_definitions(statement)?;
    let input = custody::input_demand(parties, secret_bytes);
    let witness = witgen::demand(&shape, &defs).ok()?;
    let proof = prover::prover_demand(&shape, regime)?;
    Some([
        (Stage::Input, input.0, input.1),
        (Stage::Witness, witness.triples, witness.randoms),
        (Stage::Proof, proof.0, proof.1),
    ])
}

/// One custodian's side of a threshold proof of `statement`. No custodian holds the
/// secret, any variable of the assignment that depends on it or any share of another
/// custodian at any point: the secret's bits enter as authenticated shares
/// ([`custody`]), the assignment is computed on shares ([`witgen`]) and proved on shares
/// ([`prover`]).
pub fn prove_ownership_party<T: Transport>(
    e: &mut Engine<T>,
    statement: &OwnershipStatement,
    regime: WhirSecurityRegime,
    input: CustodyInput<'_>,
) -> Result<ZkHemSplitProof, ThresholdError> {
    prove_ownership_party_observed(e, statement, regime, input, &mut |_, _| {})
}

/// [`prove_ownership_party`], reporting the engine's counters after each stage.
pub fn prove_ownership_party_observed<T: Transport>(
    e: &mut Engine<T>,
    statement: &OwnershipStatement,
    regime: WhirSecurityRegime,
    input: CustodyInput<'_>,
    after: &mut dyn FnMut(Stage, Stats),
) -> Result<ZkHemSplitProof, ThresholdError> {
    let (shape, defs) = ownership_definitions(statement).ok_or(ThresholdError::Statement)?;
    let public_inputs = statement.public_inputs().ok_or(ThresholdError::Statement)?;
    let auxiliary = ownership_auxiliary_inputs(
        statement,
        input.xor_share.len(),
        input.path,
        input.merkle_root,
    )
    .ok_or(ThresholdError::Statement)?;
    // The relation's inputs: the secret, zero-padded to its width, then the auxiliary
    // inputs as public constants.
    let widths = witgen::input_bits(&defs);
    let fits = widths.len() == 1 + auxiliary.len()
        && widths[0] >= 8 * input.xor_share.len()
        && widths[1..].iter().zip(&auxiliary).all(|(&w, a)| w == a.len());
    if !fits {
        return Err(ThresholdError::Statement);
    }
    let mut secret =
        custody::input_secret_bits(e, input.xor_share).map_err(ThresholdError::Input)?;
    after(Stage::Input, e.stats);
    secret.resize(widths[0], e.public(Goldilocks::ZERO));
    let mut inputs = Vec::with_capacity(widths.len());
    inputs.push(secret);
    for bits in &auxiliary {
        inputs.push(
            bits.iter()
                .map(|&b| e.public(Goldilocks::from_u64_reduced(u64::from(b))))
                .collect(),
        );
    }
    let z = witgen::generate(e, &shape, &defs, &public_inputs, &inputs)
        .map_err(ThresholdError::Witness)?;
    after(Stage::Witness, e.stats);
    let proof = prover::prove_party(
        e,
        &shape,
        &public_inputs,
        &ownership_transcript(statement, regime),
        regime,
        z,
    )
    .map_err(ThresholdError::Prove)?;
    after(Stage::Proof, e.stats);
    Ok(proof)
}

/// Verify a threshold proof of an ownership statement: the ordinary zk-Hem verifier on
/// the statement's relation, public inputs and transcript, with the Stage-0 fibers
/// checked against every custodian's root.
pub fn verify_threshold_ownership(
    statement: &OwnershipStatement,
    regime: WhirSecurityRegime,
    proof: &ZkHemSplitProof,
) -> bool {
    let (Some(shape), Some(public_inputs)) =
        (ownership_shape(statement), statement.public_inputs())
    else {
        return false;
    };
    verify_split(
        &shape,
        &public_inputs,
        &ownership_transcript(statement, regime),
        regime,
        proof,
    )
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;
    use core::ops::{Add, Sub};

    use dregg_sig_agg::field::{
        Goldilocks, GoldilocksExt4, encode_rs_coset_goldilocks, intt_goldilocks,
    };
    use dregg_sig_agg::pcs::{WhirSecurityRegime, hypercube_to_monomial_coeffs};
    use dregg_sig_agg::zk_hem::protocol::Layout;
    use dregg_sig_agg::zk_hem::{PrimitiveChallenge, SeedStream};

    type E = GoldilocksExt4;
    type F = Goldilocks;

    fn coins(tag: u8) -> SeedStream {
        SeedStream::new(b"DREGG.TEST.COLLAB", &[tag; 32])
    }

    fn random_table(s: &mut SeedStream, len: usize) -> Vec<E> {
        (0..len).map(|_| s.next_ext4()).collect()
    }

    /// Additive shares of `values` among `parties`: parties `1..` get `coin()` values, party 0
    /// the remainder.
    fn share_additive<T>(values: &[T], parties: usize, mut coin: impl FnMut() -> T) -> Vec<Vec<T>>
    where
        T: Copy + Sub<Output = T>,
    {
        assert!(parties >= 2);
        let mut shares: Vec<Vec<T>> = (0..parties)
            .map(|_| Vec::with_capacity(values.len()))
            .collect();
        for &value in values {
            let mut rest = value;
            for share in &mut shares[1..] {
                let r = coin();
                share.push(r);
                rest = rest - r;
            }
            shares[0].push(rest);
        }
        shares
    }

    /// Sum of the parties' share vectors.
    fn reconstruct<T>(shares: &[Vec<T>]) -> Vec<T>
    where
        T: Copy + Add<Output = T>,
    {
        let mut out = shares[0].clone();
        for share in &shares[1..] {
            assert_eq!(share.len(), out.len());
            for (acc, &s) in out.iter_mut().zip(share) {
                *acc = *acc + s;
            }
        }
        out
    }

    /// Local: one party's share of a Stage-0 style codeword of its share of a table, the
    /// coset Reed-Solomon encoding of the table's multilinear monomial coefficients.
    fn codeword_share(table_share: &[F], blowup: usize) -> Vec<F> {
        encode_rs_coset_goldilocks(&hypercube_to_monomial_coeffs(table_share), blowup)
    }

    /// Local: one party's share of the blended word `U = sum_j beta^j T_j` from its shares of
    /// the committed tables (`T_0 = Z`, then the companions).
    fn blend_share(beta: E, table_shares: &[Vec<F>]) -> Vec<E> {
        let cells = table_shares[0].len();
        let mut out = vec![E::ZERO; cells];
        let mut scalar = E::ONE;
        for table in table_shares {
            assert_eq!(table.len(), cells);
            for (u, &v) in out.iter_mut().zip(table) {
                *u += scalar.mul_base(v);
            }
            scalar *= beta;
        }
        out
    }

    #[test]
    fn encoding_and_blending_commute_with_sharing() {
        let mut s = coins(50);
        for (log_cells, parties, blowup) in [(4usize, 2usize, 4usize), (7, 3, 4), (9, 5, 16)] {
            let cells = 1usize << log_cells;
            let table: Vec<F> = (0..cells).map(|_| s.next_base()).collect();
            let shares = share_additive(&table, parties, || s.next_base());
            let share_words: Vec<Vec<F>> =
                shares.iter().map(|sh| codeword_share(sh, blowup)).collect();
            let word = codeword_share(&table, blowup);
            assert_eq!(word.len(), cells * blowup);
            assert_eq!(reconstruct(&share_words), word);
            // One share's codeword is not the codeword.
            assert!(share_words.iter().all(|w| w != &word));

            // The blend of five tables, share by share.
            let tables: Vec<Vec<F>> = core::iter::once(table.clone())
                .chain((0..4).map(|_| (0..cells).map(|_| s.next_base()).collect()))
                .collect();
            let beta = s.next_ext4();
            let per_table: Vec<Vec<Vec<F>>> = tables
                .iter()
                .map(|t| share_additive(t, parties, || s.next_base()))
                .collect();
            let blends: Vec<Vec<E>> = (0..parties)
                .map(|p| {
                    let mine: Vec<Vec<F>> = per_table.iter().map(|t| t[p].clone()).collect();
                    blend_share(beta, &mine)
                })
                .collect();
            assert_eq!(reconstruct(&blends), blend_share(beta, &tables));
        }
    }

    /// Inverse of [`codeword_share`]: the table from its complete codeword.
    fn decode(word: &[F], cells: usize) -> Vec<F> {
        let mut coeffs = word.to_vec();
        intt_goldilocks(&mut coeffs);
        assert!(coeffs[cells..].iter().all(|&c| c == F::ZERO));
        coeffs.truncate(cells);
        let shift_inv = F::NON_RESIDUE.inv();
        let mut power = F::ONE;
        for c in &mut coeffs {
            *c *= power;
            power *= shift_inv;
        }
        // Monomial coefficients back to hypercube values.
        for b in 0..cells.trailing_zeros() {
            for idx in 0..cells {
                if (idx >> b) & 1 == 1 {
                    let lower = coeffs[idx ^ (1 << b)];
                    coeffs[idx] += lower;
                }
            }
        }
        coeffs
    }

    /// zk-Hem blinds as many cells as Stage-0 opens symbols. That hides the opened
    /// symbols and nothing more: the complete codeword is the table.
    #[test]
    fn a_complete_stage0_codeword_reveals_the_table_whatever_the_blinders() {
        let regime = WhirSecurityRegime::default();
        let (shape, assignment) = super::prover::tests::small_relation(5);
        let layout = Layout::new(&shape, regime).unwrap();
        let st0 = layout.schedule.stages[0];
        let cells = 1usize << layout.log_cells;
        let opened = st0.num_queries.min((cells * st0.blowup) >> st0.step_vars) << st0.step_vars;
        assert_eq!(layout.blind_cells, opened);
        assert!(layout.blind_cells < cells * st0.blowup);

        let mut s = coins(60);
        let mut table = vec![F::ZERO; cells];
        table[..assignment.len()].copy_from_slice(&assignment);
        for slot in &mut table[cells - layout.blind_cells..] {
            *slot = s.next_base();
        }
        let word = codeword_share(&table, st0.blowup);
        assert_eq!(decode(&word, cells), table);

        // An additive share of the same table decodes to the share, which is uniform.
        let shares = share_additive(&table, 3, || s.next_base());
        for share in &shares {
            let recovered = decode(&codeword_share(share, st0.blowup), cells);
            assert_eq!(&recovered, share);
            assert_ne!(recovered[..assignment.len()], assignment[..]);
        }
    }

    /// The companions as a function of the blend and the table: the `F_p`-linear
    /// coordinates of `u - z` in the basis `(beta, beta^2, beta^3, beta^4)`.
    fn unblend(beta: E, z: &[F], u: &[E]) -> [Vec<F>; 4] {
        let basis: [[F; 4]; 4] = {
            let mut power = beta;
            core::array::from_fn(|_| {
                let limbs = power.to_limbs();
                power *= beta;
                limbs
            })
        };
        let mut out: [Vec<F>; 4] = core::array::from_fn(|_| Vec::with_capacity(z.len()));
        for (&zi, &ui) in z.iter().zip(u) {
            let c = unblend_generic(basis, (ui - E::from_base(zi)).to_limbs());
            for (col, cj) in out.iter_mut().zip(c) {
                col.push(cj);
            }
        }
        out
    }

    /// Opening the whole blended word `U` and the companion claims to the provers reveals
    /// the public claim `<Z, K>` and nothing else about `Z`: for a base-field `Z`, the map
    /// from the companions to `U` is a bijection, and the companion claims are a function
    /// of `U` and `<Z, K>`.
    #[test]
    fn the_blended_word_and_companion_claims_are_simulated_from_the_public_claim() {
        let mut s = coins(70);
        let cells = 32;
        let beta = loop {
            if let Some(b) = PrimitiveChallenge::new(s.next_ext4()) {
                break b.get();
            }
        };
        let kernel = random_table(&mut s, cells);
        let dot = |t: &[F]| {
            t.iter()
                .zip(&kernel)
                .fold(E::ZERO, |acc, (&v, &k)| acc + k.mul_base(v))
        };
        let z: Vec<F> = (0..cells).map(|_| s.next_base()).collect();
        let companions: Vec<Vec<F>> = (0..4)
            .map(|_| (0..cells).map(|_| s.next_base()).collect())
            .collect();
        let mut tables = vec![z.clone()];
        tables.extend(companions.iter().cloned());
        let u = blend_share(beta, &tables);
        let claims: Vec<E> = companions.iter().map(|c| dot(c)).collect();

        // Bijection, both ways.
        assert_eq!(unblend(beta, &z, &u).to_vec(), companions);
        let any_u = random_table(&mut s, cells);
        let mut back = vec![z.clone()];
        back.extend(unblend(beta, &z, &any_u));
        assert_eq!(blend_share(beta, &back), any_u);

        // Simulator: from `U` and `V = <Z, K>` alone.
        let zeros = vec![F::ZERO; cells];
        let ones = vec![F::ONE; cells];
        let of_u = unblend(beta, &zeros, &u);
        let unit = unblend(beta, &ones, &vec![E::ZERO; cells]);
        let v = dot(&z);
        for j in 0..4 {
            // `unit[j]` is constant: minus the coordinate of `1`.
            assert!(unit[j].iter().all(|&c| c == unit[j][0]));
            assert_eq!(claims[j], dot(&of_u[j]) + v.mul_base(unit[j][0]));
        }

        // The same view explains another table with the same public claim.
        let mut z2: Vec<F> = (0..cells).map(|_| s.next_base()).collect();
        let k: Vec<[F; 4]> = kernel.iter().map(|k| k.to_limbs()).collect();
        // Four cells of `z2` take up the four base-field coordinates of the claim.
        let gap = (v - dot(&z2)).to_limbs();
        let fix = unblend_generic([k[0], k[1], k[2], k[3]], gap);
        for (slot, d) in z2.iter_mut().zip(fix) {
            *slot += d;
        }
        assert_ne!(z2, z);
        assert_eq!(dot(&z2), v);
        let other = unblend(beta, &z2, &u);
        assert_ne!(other.to_vec(), companions);
        let mut tables2 = vec![z2];
        tables2.extend(other.iter().cloned());
        assert_eq!(blend_share(beta, &tables2), u);
        let claims2: Vec<E> = other.iter().map(|c| dot(c)).collect();
        assert_eq!(claims2, claims);

        // An `Ext4`-valued table has no such simulator: the claims then move.
        let mut z3 = z.clone();
        z3[0] += F::ONE;
        let other3 = unblend(beta, &z3, &u);
        let claims3: Vec<E> = other3.iter().map(|c| dot(c)).collect();
        assert_ne!(claims3, claims);
    }

    /// Coordinates of `target` in four base-field vectors, by elimination.
    fn unblend_generic(basis: [[F; 4]; 4], target: [F; 4]) -> [F; 4] {
        let mut m: [[F; 5]; 4] = core::array::from_fn(|row| {
            core::array::from_fn(|col| {
                if col < 4 {
                    basis[col][row]
                } else {
                    target[row]
                }
            })
        });
        for col in 0..4 {
            let pivot = (col..4).find(|&r| m[r][col] != F::ZERO).unwrap();
            m.swap(col, pivot);
            let inv = m[col][col].inv();
            for cell in &mut m[col] {
                *cell *= inv;
            }
            let pivot_row = m[col];
            for (row, cells) in m.iter_mut().enumerate() {
                if row != col {
                    let factor = cells[col];
                    for (cell, p) in cells.iter_mut().zip(pivot_row) {
                        *cell -= factor * p;
                    }
                }
            }
        }
        core::array::from_fn(|j| m[j][4])
    }

    /// Threshold proofs of real ownership statements from `(k, n)` Shamir shares of the
    /// secret, with dealer preprocessing (test-only).
    /// `cargo test --release -p dregg-sig-migrate --features std --lib --
    /// hem::collab::tests::measure_threshold_ownership --ignored --nocapture`
    #[test]
    #[ignore = "measurement"]
    fn measure_threshold_ownership() {
        use super::custody::tests::shamir;
        use super::custody::xor_share_from_shamir;
        use super::engine::Dealer;
        use super::engine::tests::run_parties;
        use super::witgen::tests::{derived_cases, reference_cases};
        use super::*;
        let regime = WhirSecurityRegime::default();
        let only = std::env::var("COLLAB_MEASURE_ONLY").ok();
        let mut cases: Vec<_> = reference_cases()
            .into_iter()
            .map(|(st, _, secret)| (st, secret, Vec::new(), None))
            .collect();
        cases.extend(
            derived_cases()
                .into_iter()
                .map(|(st, _, secret, path, root)| (st, secret, path, root)),
        );
        for (parties, case) in [(3usize, 0usize), (3, 1), (5, 0), (3, 2), (3, 3)] {
            let (st, secret, path, root) = cases[case].clone();
            let label = std::format!("{:?} {:?} N={parties}", st.lock, st.source);
            if only.as_ref().is_some_and(|o| !label.contains(o.as_str())) {
                continue;
            }
            // Custody: parties-of-(parties + 2); the quorum leaves custodians 1 and
            // parties + 1 out.
            let shares = shamir(&secret, parties, parties + 2, 9);
            let quorum: Vec<usize> = (0..parties + 2).filter(|&p| p != 1).take(parties).collect();
            let stages = ownership_demand(&st, regime, parties, secret.len()).unwrap();
            let triples: usize = stages.iter().map(|s| s.1).sum();
            let randoms: usize = stages.iter().map(|s| s.2).sum();
            let preps = Dealer::new(parties, &[3; 32]).preprocessing(triples, randoms);
            let t = std::time::Instant::now();
            let out = run_parties(preps, |mut e| {
                let me = quorum[e.me()];
                let xor = xor_share_from_shamir(&quorum, me, &shares[me]).unwrap();
                let mut marks = Vec::new();
                let start = std::time::Instant::now();
                let proof = prove_ownership_party_observed(
                    &mut e,
                    &st,
                    regime,
                    CustodyInput {
                        xor_share: &xor,
                        path: &path,
                        merkle_root: root.as_ref(),
                    },
                    &mut |stage, stats| marks.push((stage, stats, start.elapsed().as_secs_f64())),
                );
                assert_eq!(e.remaining(), (0, 0), "demand is exact");
                (proof, marks)
            });
            let total_s = t.elapsed().as_secs_f64();
            let proof = out[0].0.clone().unwrap();
            assert!(out.iter().all(|(p, _)| p.as_ref() == Ok(&proof)));
            let bytes = proof.to_bytes();
            let t = std::time::Instant::now();
            assert!(verify_threshold_ownership(&st, regime, &proof));
            let verify_s = t.elapsed().as_secs_f64();
            let mut other = st.clone();
            other.epoch += 1;
            assert!(!verify_threshold_ownership(&other, regime, &proof));
            std::println!(
                "{label}: proof={} bytes wall={total_s:.1}s verify={verify_s:.2}s",
                bytes.len()
            );
            let mut before = (Stats::default(), 0.0);
            for ((stage, stats, at), demand) in out[0].1.iter().zip(&stages) {
                std::println!(
                    "  {stage:?}: triples={} randoms={} sent={} bytes rounds={} mac_checks={} time={:.1}s",
                    stats.triples_used - before.0.triples_used,
                    stats.randoms_used - before.0.randoms_used,
                    stats.bytes_sent - before.0.bytes_sent,
                    stats.rounds - before.0.rounds,
                    stats.mac_checks - before.0.mac_checks,
                    at - before.1,
                );
                assert_eq!(
                    (stats.triples_used - before.0.triples_used) as usize,
                    demand.1
                );
                assert_eq!(
                    (stats.randoms_used - before.0.randoms_used) as usize,
                    demand.2
                );
                before = (*stats, *at);
            }
        }
    }
}
