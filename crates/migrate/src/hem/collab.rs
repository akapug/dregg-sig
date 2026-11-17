//! Collaborative proving: the zk-Hem prover run by `N` custodians on an additively shared
//! witness.
//!
//! # Verdict
//!
//! Collaborative zk-Hem works with WHIR and with named changes; it does not need a
//! tensor-code or Basefold commitment. The one part of the prover that cannot run on
//! shares is the Stage-0 Merkle tree, and the change is to replace that tree by one tree
//! per custodian over the custodian's own share codewords (an interleaved commitment).
//! WHIR's proximity protocol, its later stages and its verifier logic stay as they are.
//! The price is `N` times the Stage-0 part of the proof and a verifier that sums `N`
//! opened share symbols per query. It is not a scalable collaborative SNARK in the sense
//! of 2026/729: every custodian does the full prover's work.
//!
//! # Where the prover is linear, where it multiplies, where it hashes
//!
//! Step numbers are those of `dregg_sig_agg::zk_hem::protocol`.
//!
//! | Prover step | In the shared witness | Here |
//! |---|---|---|
//! | masks, companions, blinders, masking variables | sampled | each party samples its own share |
//! | row tables `(Az, Bz, Cz)` | linear | [`row_table_shares`] |
//! | Stage-0 codewords | linear | [`codeword_share`] |
//! | Stage-0 Merkle tree | hash of secret symbols | per-party trees (not built here) |
//! | 1. row sumcheck, multiplication rows | degree 2 | [`collab_row_sumcheck`], Beaver triples |
//! | 1. row sumcheck, S-box rows | degree 7 | not supported, see below |
//! | mask sums, mask round polynomials, `g(point)` | linear | `LibraMask` methods on a share |
//! | 2. row values at `rx` | linear, opened | [`RowParty::terminal_shares`] |
//! | 3. column sumcheck `M(rx, y) Z(y)`, `M` public | linear | [`collab_column_sumcheck`] |
//! | 4. batched functional `K` | public | computed by anyone |
//! | 5. companion claims `<C_j, K>` | linear, opened | not built here |
//! | 5. blended word `U` | linear, opened in full | [`blend_share`] |
//! | 5. WHIR on `U`: out-of-domain values, folds, later trees, proof of work | function of `U` | public once `U` is open |
//! | 6. Stage-0 query answers | each party opens its own leaves | not built here |
//! | Fiat-Shamir transcript | hash of public messages | computed by every party |
//!
//! Hashing touches secret data in exactly two places: the Stage-0 leaves, and the coin
//! derivation of `protocol::prove`, which hashes the witness into its seed. The second
//! disappears: custodians use local randomness.
//!
//! # The committed codeword
//!
//! zk-Hem's masking covers the queried positions only. `Layout::blind_cells` is the number
//! of Stage-0 symbols the verifier opens; every other leaf is salted and never revealed.
//! The codeword of `Z` is an injective linear image of the table, so a party that sees
//! all of it has the table, whatever the blinders
//! (`a_complete_stage0_codeword_reveals_the_table_whatever_the_blinders` decodes it).
//! Opening the codeword among the custodians so that one of them can hash it is therefore
//! not an option, and blinding it against that is not possible either: a blinding that
//! hides `s` symbols of a Reed-Solomon word needs `s` uniform coefficients, and the whole
//! word has `blowup` times more symbols than the message has coefficients.
//!
//! 2026/729 does not open the codeword either. There party `i` holds row `i` of a tensor
//! codeword, which is at once a segment of the codeword and a packed Shamir share of its
//! columns; it hashes its own row, and the commitment is the root over the `N` partial
//! roots (Section 4, steps 1 and 2). Its `(t, l)`-zero-knowledge code (Theorem 1) has
//! `t <= k' - k + 1` from the column code's padding and `l = m' - m` from the row code's
//! masking columns: a coalition sees `t` rows and `l` queried symbols. The same segment
//! idea on zk-Hem's single Reed-Solomon word would need `t n / N + q` uniform
//! coefficients for a word of length `n` and `q` opened symbols, which exceeds the
//! message length as soon as `t / N >= 1 / blowup` (Stage-0 blowup is 4).
//!
//! What fits zk-Hem is what 2026/729 Section 3 calls the trivial collaborative code.
//! Every committed table is additively shared, each custodian encodes and Merkle-hashes
//! its own shares of `Z, C_0..C_3` with its own salt seed (this is
//! `whir_commit_batch_secret_with_schedule` on the share tables), and the commitment bound
//! into the transcript is the list of `N` roots. No custodian sees another's leaves. A
//! Stage-0 query is answered by `N` leaf openings and the verifier uses the sum of the
//! symbols. Masking degree: unchanged. `blind_cells` uniform cells, each custodian
//! choosing its share of them, hide the opened symbols of `Z` as before; the shares of one
//! symbol held by the honest custodians are uniform given their sum; the unopened leaves
//! of a custodian are seen by nobody else. Privacy holds against any `N - 1` custodians.
//!
//! The blended word can be opened in full to the custodians. `U = Z + sum_j beta^(j+1)
//! C_j` with `Z` and the `C_j` over the base field and `beta` outside the quadratic
//! subfield: for a fixed `Z` the map from the companions to `U` is a bijection, and the
//! companion claims are a function of `U` and the public value `<Z, K>`
//! (`the_blended_word_and_companion_claims_are_simulated_from_the_public_claim`). With
//! `U` public, everything WHIR does after Stage 0 is a public computation.
//!
//! # The protocol
//!
//! Setup: a quorum of `N` custodians holds additive shares of the assignment `z` (see
//! "Witness generation") and enough preprocessing. Messages are broadcast.
//!
//! 1. Each custodian samples its shares of the masking variables, of both sumcheck masks,
//!    of the blinders and of the four companion tables, builds its share tables, commits
//!    to them locally and broadcasts its root. The transcript binds the `N` roots.
//! 2. Row sumcheck. Opened: the mask sum; per round, for each pair of rows, the Beaver
//!    openings `(x - a, y - b)` of two products, then the masked round polynomial.
//! 3. Opened: `(Az, Bz, Cz)(rx)`, uniform by the masking rows when
//!    `mask_rows_full_rank` holds for the public `rx` (otherwise abort and rerun).
//! 4. Column sumcheck. Opened: the mask sum and the masked round polynomials. No
//!    multiplication: `M(rx, .)` is public.
//! 5. Opened: the four companion claims; after `beta`, the whole of `U`.
//! 6. Any custodian runs WHIR's stages on `U`. Each custodian opens its Stage-0 leaves at
//!    the queried fibers. Every custodian runs the verifier on the assembled proof
//!    before releasing it.
//!
//! Never opened: `Z(ry)`, `g1(rx)`, `g2(ry)` (they are terms of the linear claim), any
//! share table, any unqueried Stage-0 symbol.
//!
//! # Multiplications
//!
//! A row round over pairs of rows needs, per pair, `a_lo b_lo` and
//! `(a_hi - a_lo)(b_hi - b_lo)`; the middle coefficient follows from the running claim,
//! which is itself shared and linear. That is two secure multiplications per pair, all
//! in one layer, `2^(n - i)` in round `i` and [`row_triples_needed`]`(n) = 2 (2^n - 1)` in
//! total for `2^n` rows. The column sumcheck needs none. Not done here: for a satisfied
//! relation the first product of round 0 equals `c_lo`, which saves `2^(n - 1)`
//! multiplications, and round 0 could use base-field triples.
//!
//! # S-box rows
//!
//! zk-Hem's `a^7 = c` rows are outside the two-factor argument of 2026/729 and of this
//! file. On shares, the round polynomial of `eq * (a^7 - c)` has degree 7 in the shared
//! line `a_lo + X (a_hi - a_lo)`: seven evaluation points per pair (the eighth
//! coefficient comes from the claim), each a seventh power of a shared value, four
//! multiplications in depth three. That is 28 multiplications per pair per round against
//! two, with three sequential openings a round. Rewriting the S-box as four
//! multiplication rows (`a2 = a a`, `a3 = a2 a`, `a4 = a2 a2`, `c = a3 a4`) costs three
//! variables and eight multiplications per original pair, depth one.
//! Collaborative proving should use shapes without S-box rows; [`collab_front_end`]
//! refuses any other.
//!
//! # Witness generation
//!
//! 2026/729 Construction 6 starts from shares of the complete proving data
//! `(w, Aw, Bw, Cw)`. Custodians here hold shares of a seed or a scalar. `Aw, Bw, Cw` are
//! linear and cost nothing ([`row_table_shares`]); `w` itself, every SHA, HMAC and curve
//! intermediate, is not, and computing its shares is a secure computation of the relation,
//! once. In the relation's own arithmetic that is one authenticated Goldilocks
//! multiplication for every row whose output cell is a new variable, at most `2^n`,
//! provided every variable is a linear form or a product of earlier ones. Two kinds of
//! variable are not:
//!
//! * the bits of the seed: custody shares are bytes over `GF(256)`, so each seed bit
//!   enters through one doubly authenticated bit (`threshold_mpc::DaBitWord`);
//! * hint variables of non-native arithmetic (quotients, carries, range-check bits of
//!   curve field elements). These need either a curve gadget whose hints are products of
//!   earlier cells, or the engine's native secp256k1 and Ed25519 wires followed by a
//!   bit decomposition through doubly authenticated bits.
//!
//! The engine that runs it is `threshold_mpc::SpdzEngine` on `threshold_prep` material:
//! it already has authenticated Goldilocks wires, field triples and the bit conversions.
//! Whether the total beats today's design: today's ceremony evaluates the ZKBoo prover
//! (438 repetitions, three views each, with their SHAKE tapes and commitments) inside
//! the engine, about 1.1 billion Boolean `AND` words. Here the engine evaluates the
//! relation once and then two extension-field products per row. The count below says yes
//! by about three orders of magnitude for a relation of `2^20` rows; the migration
//! relation itself has not been counted (the `hash` and `curve` modules are being written),
//! and the cost is linear in its row count.
//!
//! # Threshold, adversary, abort
//!
//! These are properties of the proving quorum, not of the custody scheme. A `(k, n)`
//! Shamir custody picks a quorum of `N = k` custodians and converts their shares to
//! additive ones (`ThresholdConfig::shamir_contribution`); `n`-of-`n` custody has
//! `N = n`.
//!
//! * Privacy threshold: `N - 1` of the quorum. With Shamir custody that is fewer than `k`
//!   custodians overall, the custody threshold itself. 2026/729 has `t <= (1/2 - eps) N`
//!   because it packs shares; this protocol does not pack.
//! * What is built and tested here is secure against honest-but-curious custodians:
//!   every party follows the protocol and the preprocessing is correct.
//! * Malicious custodians: run the same steps on the engine's MAC-authenticated shares.
//!   The values opened in steps 2 to 5 are then partial openings, and the batch MAC check
//!   must pass before the next message that depends on them is sent: once per sumcheck
//!   round. A wrong Beaver opening without that check would shift a round polynomial by a
//!   multiple of a secret table entry. A custodian that commits to a tree that is not the
//!   encoding of its authenticated shares, or opens a wrong leaf, makes the assembled
//!   proof fail verification; soundness never depends on a custodian.
//! * Abort: any custodian can make the run fail, at a MAC check or by withholding.
//!   Abort is not identifiable and not fair: the custodian that sends its Stage-0
//!   openings last can keep the finished proof to itself. A failed run is repeated with
//!   fresh masks, companions, blinders and triples, never with reused ones.
//! * Soundness of the proof is that of zk-Hem for the verifier and holds if all `N`
//!   custodians collude.
//!
//! 2026/729 proves its protocols for honest-but-curious provers and states that the
//! packed-Shamir compiler of its reference \[44\] gives malicious security at up to twice
//! the cost; it leaves the cheaper variant as future work. That compiler is for an honest
//! majority and does not apply to additive sharing; the MAC check above is this repo's
//! equivalent, and its composition with the masked sumcheck is not proven here.
//!
//! # Cost for `2^20` rows
//!
//! Assumptions: `2^20` multiplication rows, at most `2^20` variables, so a committed
//! table of `2^21` cells; default regime, Stage 0 with blowup 4 and 258 queries of 64
//! symbols (`estimate_inputs`). An `Ext4` element is 32 bytes.
//!
//! Online, sent by each custodian as broadcasts, as implemented (every row product in
//! `Ext4`):
//!
//! | | elements | bytes |
//! |---|---|---|
//! | witness generation, `2^20` products | `2^21` base | 16 MiB |
//! | row sumcheck, `2 (2^20 - 1)` products | `2^22` ext | 128 MiB |
//! | blended word | `2^21` ext | 64 MiB |
//! | everything else | under 1,000 ext | under 32 KiB |
//! | total | | 208 MiB |
//!
//! The MAC checks add a constant per check. All custodians together broadcast 624 MiB
//! for `N = 3` and 1,040 MiB for `N = 5`; on a full mesh, where a broadcast is `N - 1`
//! sends, 1.2 GiB and 4.1 GiB cross the wire. The proof grows by `N - 1` copies of the
//! Stage-0 opening, 645 KiB of field values each plus authentication paths.
//!
//! Preprocessing per custodian: `2^20` Goldilocks triples and `2 (2^20 - 1)` `Ext4`
//! triples. `threshold_prep` has no `Ext4` triple; with nine Goldilocks triples per
//! `Ext4` product that is about 19.9 million `FieldTriple`s, 5.3 GiB at their in-memory
//! size, against 3 TiB today. At the rate `SECURITY.md` reports for three members (2 ms
//! per Goldilocks triple, one thread) generating them takes about 11 hours, against five
//! weeks. The rate for five members has not been measured.
//!
//! # Changes this needs in `crates/agg`
//!
//! * `zk_hem::protocol::prove` split at its steps: table and mask layout
//!   (`Layout::row_mask_block`, `Layout::col_mask_block`, `Mask::write`), `claim_terms`
//!   and `start_transcript` made public, so a custodian can build its share table and the
//!   functional `K`.
//! * `start_transcript`, `ZkHemProof` and `verify`: a commitment that is a list of `N`
//!   roots.
//! * `pcs::whir_open_blend` / `whir_open_core`: an entry point that takes `U`'s monomial
//!   coefficients and no `HemWhirProverState`, and returns the Stage-0 query positions
//!   instead of opening them; a per-custodian Stage-0 opening over
//!   `MerkleCanopyTree::open_multi_with_leaf_fn`.
//! * `pcs::whir_verify_blend`: Stage-0 fibers checked against `N` trees and summed
//!   before the blend.
//! * `pcs::whir_commit_batch_secret_with_schedule` made public.
//!
//! In `crates/migrate`: an `Ext4` triple in `threshold_prep`, and the relation gadgets
//! written so that every variable is a product or linear form of earlier ones.
//!
//! # What is proven where
//!
//! * 2026/729, for its own construction (tensor Reed-Solomon code, packed Shamir shares,
//!   Basefold-style commitment, Spartan): Theorem 1 (zero-knowledge collaborative code),
//!   Theorem 2 (the collaborative BCS compiler with per-party partial roots keeps
//!   round-by-round soundness and `t`-zero-knowledge), Theorems 3 to 6. None of them is
//!   about WHIR or additive sharing.
//! * `ZkHemSoundnessAndPrivacy.lean`, for the single prover: the masked sumcheck, the
//!   companion blend and the opened symbols are each perfectly simulated. Their
//!   composition is not mechanized (see `protocol::prove`).
//! * Tested in this file: the collaborative sumchecks emit the single prover's messages,
//!   including those of `protocol::prove` itself on the same coins
//!   (`front_end_reproduces_the_messages_of_the_zk_hem_prover`); the view of `N - 1`
//!   parties in the row sumcheck is identical for two witnesses with the same public
//!   output under a translation of the honest party's coins
//!   (`coalition_view_does_not_depend_on_the_witness`); encoding and blending commute
//!   with sharing; the two statements about the codeword and about `U` above.
//! * Claimed here without proof or test: that the sum of `N` separately committed words
//!   is as binding a Stage-0 oracle as one tree over the same symbols; privacy of the
//!   composed protocol; everything under "Malicious custodians"; the cost table, which is
//!   arithmetic on the counts above and on rates quoted from `SECURITY.md`.
//!
//! # What this file implements
//!
//! Steps 2 to 4 for relations without S-box rows, honest-but-curious, with all parties
//! in one process: [`collab_row_sumcheck`], [`collab_column_sumcheck`],
//! [`collab_front_end`], and the share-wise linear maps. Triples come from the caller.

use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, Sub};

use dregg_sig_agg::field::{
    Goldilocks, GoldilocksExt4, build_eq_table_ext4, encode_rs_coset_goldilocks,
};
use dregg_sig_agg::pcs::hypercube_to_monomial_coeffs;
use dregg_sig_agg::zk_hem::relation::Shape;
use dregg_sig_agg::zk_hem::{LibraMask, NonzeroChallenge};
use dregg_sig_agg::{FiatShamirTranscript, InstanceBound};

type E = GoldilocksExt4;
type F = Goldilocks;

/// Degree of the row round polynomial for multiplication rows: `eq * (a * b - c)`.
pub const ROW_PRODUCT_DEGREE: usize = 3;
/// Degree of the column round polynomial `M * Z`.
pub const COLUMN_DEGREE: usize = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CollabError {
    /// Party count, indices, table sizes or mask shapes do not fit together.
    Malformed,
    /// A party holds fewer triples than [`row_triples_needed`].
    OutOfTriples,
    /// A row challenge `tau_i` is zero, so the middle coefficient cannot be taken from the
    /// running claim (probability `2^-256` per round for a Fiat-Shamir challenge).
    DegenerateChallenge,
    /// The relation has S-box rows; only multiplication rows are supported.
    SboxRows,
}

/// One party's additive share of a Beaver triple `c = a * b` over `Ext4`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TripleShare {
    pub a: E,
    pub b: E,
    pub c: E,
}

/// What a broadcast message is, so a transcript of the run can be read back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BroadcastKind {
    /// Share of `sum_x g(x)` for a sumcheck mask.
    MaskSum,
    /// `(x - a, y - b)` for every multiplication of a row round, in multiplication order.
    MaskedInputs { round: usize },
    /// Share of the masked round polynomial's coefficients.
    RoundShare { round: usize },
    /// Share of a value the protocol opens.
    Value,
}

/// A message sent by one party to all others. A party's view of a run is its initial
/// state together with every `Broadcast`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Broadcast {
    pub from: usize,
    pub kind: BroadcastKind,
    pub values: Vec<E>,
}

// ============================================================================
// 1. Additive sharing
// ============================================================================

/// Additive shares of `values` among `parties`: parties `1..` get `coin()` values, party 0
/// the remainder.
pub fn share_additive<T>(values: &[T], parties: usize, mut coin: impl FnMut() -> T) -> Vec<Vec<T>>
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
pub fn reconstruct<T>(shares: &[Vec<T>]) -> Vec<T>
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

/// Additive shares of a sumcheck mask. Every quantity the prover derives from a mask
/// (`sum`, `round_poly`, `eval`) is linear in its coefficients for public challenges, so
/// the parties apply those functions to their shares.
pub fn share_mask(mask: &LibraMask, parties: usize, mut coin: impl FnMut() -> E) -> Vec<LibraMask> {
    let a0 = share_additive(&[mask.a0], parties, &mut coin);
    let rows: Vec<Vec<Vec<E>>> = mask
        .a
        .iter()
        .map(|row| share_additive(row, parties, &mut coin))
        .collect();
    (0..parties)
        .map(|p| LibraMask {
            a0: a0[p][0],
            a: rows.iter().map(|row| row[p].clone()).collect(),
        })
        .collect()
}

fn mask_degree(mask: &LibraMask) -> Option<usize> {
    let d = mask.a.first()?.len();
    mask.a.iter().all(|row| row.len() == d).then_some(d)
}

#[inline]
fn eval_poly(coeffs: &[E], x: E) -> E {
    coeffs.iter().rev().fold(E::ZERO, |acc, &c| acc * x + c)
}

fn fold_in_place(table: &mut Vec<E>, r: E) {
    let half = table.len() / 2;
    for i in 0..half {
        table[i] = table[2 * i] + r * (table[2 * i + 1] - table[2 * i]);
    }
    dregg_sig_asm::volatile_fill(&mut table[half..], E::ZERO);
    table.truncate(half);
}

fn lift(table: &[F]) -> Vec<E> {
    table.iter().map(|&v| E::from_base(v)).collect()
}

fn add_into(acc: &mut [E], part: &[E]) {
    for (a, &p) in acc.iter_mut().zip(part) {
        *a += p;
    }
}

// ============================================================================
// 2. Row sumcheck: `sum_x eq(tau, x) (A(x) B(x) - C(x))`, one multiplication layer a round
// ============================================================================

/// Beaver triples one party consumes in a row sumcheck over `2^log_rows` rows: two for
/// every pair of rows in every round.
pub const fn row_triples_needed(log_rows: usize) -> usize {
    2 * ((1usize << log_rows) - 1)
}

/// One party of the row sumcheck: shares of the three row tables, of the mask and of the
/// triples.
pub struct RowParty {
    index: usize,
    tables: [Vec<E>; 3],
    mask: LibraMask,
    triples: Vec<TripleShare>,
    used: usize,
    /// Share of the unmasked running claim.
    claim: E,
    /// Share of the unmasked round polynomial awaiting its challenge.
    pending: [E; ROW_PRODUCT_DEGREE + 1],
}

impl RowParty {
    pub fn new(
        index: usize,
        tables: [Vec<E>; 3],
        mask: LibraMask,
        triples: Vec<TripleShare>,
    ) -> Self {
        Self {
            index,
            tables,
            mask,
            triples,
            used: 0,
            claim: E::ZERO,
            pending: [E::ZERO; ROW_PRODUCT_DEGREE + 1],
        }
    }

    /// Local: share of `sum_x g(x)`.
    pub fn mask_sum_share(&self) -> E {
        self.mask.sum()
    }

    /// Local: for every pair of rows, the two products the round needs, `a_lo * b_lo` and
    /// `(a_hi - a_lo) * (b_hi - b_lo)`, as Beaver-masked inputs `(x - a, y - b)`.
    fn masked_inputs(&self) -> Vec<E> {
        let [ta, tb, _] = &self.tables;
        let pairs = ta.len() / 2;
        let mut out = Vec::with_capacity(4 * pairs);
        for k in 0..pairs {
            let t0 = self.triples[self.used + 2 * k];
            let t1 = self.triples[self.used + 2 * k + 1];
            out.push(ta[2 * k] - t0.a);
            out.push(tb[2 * k] - t0.b);
            out.push(ta[2 * k + 1] - ta[2 * k] - t1.a);
            out.push(tb[2 * k + 1] - tb[2 * k] - t1.b);
        }
        out
    }

    /// Local, given the opened masked inputs: share of the masked round polynomial.
    ///
    /// With `h(X) = sum_k eq_rest[k] (a_k(X) b_k(X) - c_k(X)) = h0 + h1 X + h2 X^2`, the
    /// products give shares of `h0` and `h2`. The unmasked round polynomial is
    /// `p(X) = (l0 + l1 X) h(X)` and satisfies `p(0) + p(1) = claim`, so
    /// `h1 = (claim - l0 h0) / (l0 + l1) - h0 - h2` is linear in shares.
    fn round_share(
        &mut self,
        opened: &[E],
        eq_rest: &[E],
        [l0, l1]: [E; 2],
        sum_inv: E,
        rho: E,
        prefix: &[E],
    ) -> Vec<E> {
        let pairs = eq_rest.len();
        let (mut h0, mut h2) = (E::ZERO, E::ZERO);
        for k in 0..pairs {
            let product = |t: TripleShare, d: E, e: E| {
                let share = t.c + d * t.b + e * t.a;
                if self.index == 0 {
                    share + d * e
                } else {
                    share
                }
            };
            let lo = product(
                self.triples[self.used + 2 * k],
                opened[4 * k],
                opened[4 * k + 1],
            );
            let top = product(
                self.triples[self.used + 2 * k + 1],
                opened[4 * k + 2],
                opened[4 * k + 3],
            );
            h0 += eq_rest[k] * (lo - self.tables[2][2 * k]);
            h2 += eq_rest[k] * top;
        }
        dregg_sig_asm::volatile_fill(
            &mut self.triples[self.used..self.used + 2 * pairs],
            TripleShare {
                a: E::ZERO,
                b: E::ZERO,
                c: E::ZERO,
            },
        );
        self.used += 2 * pairs;
        let h1 = (self.claim - l0 * h0) * sum_inv - h0 - h2;
        self.pending = [l0 * h0, l0 * h1 + l1 * h0, l0 * h2 + l1 * h1, l1 * h2];
        let mut out = self.mask.round_poly(prefix);
        for c in &mut out {
            *c *= rho;
        }
        add_into(&mut out, &self.pending);
        out
    }

    /// Local: bind the current variable to the challenge.
    fn bind(&mut self, c: E) {
        self.claim = eval_poly(&self.pending, c);
        for table in &mut self.tables {
            fold_in_place(table, c);
        }
    }

    /// Shares of `(A, B, C)` at the sumcheck point, once all rounds have run.
    pub fn terminal_shares(&self) -> [E; 3] {
        [self.tables[0][0], self.tables[1][0], self.tables[2][0]]
    }

    /// Local: share of the mask value `g(point)`.
    pub fn mask_at_point_share(&self, point: &[E]) -> E {
        self.mask.eval(point)
    }
}

impl Drop for RowParty {
    fn drop(&mut self) {
        for table in &mut self.tables {
            dregg_sig_asm::volatile_fill(table, E::ZERO);
        }
        dregg_sig_asm::volatile_fill(
            &mut self.triples,
            TripleShare {
                a: E::ZERO,
                b: E::ZERO,
                c: E::ZERO,
            },
        );
        dregg_sig_asm::volatile_fill(&mut self.pending, E::ZERO);
        self.claim = E::ZERO;
    }
}

/// Public result of a collaborative sumcheck.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckOutput {
    /// `sum_x g(x)`, opened before `rho` is drawn.
    pub mask_sum: E,
    pub rho: E,
    /// Coefficients of the masked round polynomials.
    pub rounds: Vec<Vec<E>>,
    pub point: Vec<E>,
    /// Every message of the run, in order.
    pub broadcasts: Vec<Broadcast>,
}

fn open(
    log: &mut Vec<Broadcast>,
    kind: BroadcastKind,
    width: usize,
    shares: impl Iterator<Item = Vec<E>>,
) -> Vec<E> {
    let mut total = vec![E::ZERO; width];
    for (from, values) in shares.enumerate() {
        add_into(&mut total, &values);
        log.push(Broadcast { from, kind, values });
    }
    total
}

fn check_parties(indices: impl Iterator<Item = usize>) -> Result<usize, CollabError> {
    let mut count = 0;
    for (expected, index) in indices.enumerate() {
        if index != expected {
            return Err(CollabError::Malformed);
        }
        count += 1;
    }
    if count < 2 {
        return Err(CollabError::Malformed);
    }
    Ok(count)
}

/// Masked sumcheck of `sum_x eq(tau, x) (A(x) B(x) - C(x)) = claimed_sum` over additively
/// shared tables, with the transcript messages of zk-Hem's row sumcheck: the mask sum
/// under `ZKHEM_ROW_MASK_SUM`, `rho` under `ZKHEM_RHO1`, the rounds under
/// `ZKHEM_ROW_ROUND`. The round polynomials are those of the single prover whenever
/// `claimed_sum` is the true sum.
///
/// Per round and party: one broadcast of four field elements per pair of rows, then one
/// broadcast of the round polynomial share. Everything else is local.
pub fn collab_row_sumcheck(
    parties: &mut [RowParty],
    tau: &[E],
    claimed_sum: E,
    tr: &mut FiatShamirTranscript<InstanceBound>,
) -> Result<SumcheckOutput, CollabError> {
    check_parties(parties.iter().map(|p| p.index))?;
    let n = tau.len();
    if n == 0 || n >= usize::BITS as usize {
        return Err(CollabError::Malformed);
    }
    let mut width = 0;
    for p in parties.iter() {
        let degree = mask_degree(&p.mask).ok_or(CollabError::Malformed)?;
        if p.tables.iter().any(|t| t.len() != 1 << n)
            || p.mask.num_rounds() != n
            || degree < ROW_PRODUCT_DEGREE
            || (width != 0 && width != degree + 1)
        {
            return Err(CollabError::Malformed);
        }
        width = degree + 1;
        if p.triples.len() - p.used < row_triples_needed(n) {
            return Err(CollabError::OutOfTriples);
        }
    }
    for p in parties.iter_mut() {
        p.claim = if p.index == 0 { claimed_sum } else { E::ZERO };
    }

    let mut log = Vec::new();
    let mask_sum = open(
        &mut log,
        BroadcastKind::MaskSum,
        1,
        parties.iter().map(|p| vec![p.mask_sum_share()]),
    )[0];
    tr.absorb_ext4(b"ZKHEM_ROW_MASK_SUM", mask_sum);
    let rho = NonzeroChallenge::squeeze(tr, b"ZKHEM_RHO1").get();

    // `eq(tau, x)` splits into the bound prefix, the current variable and the rest.
    let mut eq_rest = build_eq_table_ext4(&tau[1..]);
    let mut eq_bound = E::ONE;
    let mut rounds = Vec::with_capacity(n);
    let mut point: Vec<E> = Vec::with_capacity(n);
    for (round, &t) in tau.iter().enumerate() {
        let line = [eq_bound * (E::ONE - t), eq_bound * (t + t - E::ONE)];
        let sum = line[0] + line[1];
        if sum.is_zero() {
            return Err(CollabError::DegenerateChallenge);
        }
        let sum_inv = sum.inv();
        let opened = open(
            &mut log,
            BroadcastKind::MaskedInputs { round },
            4 * eq_rest.len(),
            parties.iter().map(|p| p.masked_inputs()),
        );
        let poly = open(
            &mut log,
            BroadcastKind::RoundShare { round },
            width,
            parties
                .iter_mut()
                .map(|p| p.round_share(&opened, &eq_rest, line, sum_inv, rho, &point)),
        );
        tr.absorb_ext4_slice(b"ZKHEM_ROW_ROUND", &poly);
        let c = tr.squeeze_ext4(b"ZKHEM_ROW_ROUND");
        for p in parties.iter_mut() {
            p.bind(c);
        }
        let tc = t * c;
        eq_bound *= E::ONE - t - c + tc + tc;
        if eq_rest.len() > 1 {
            eq_rest = eq_rest.chunks_exact(2).map(|p| p[0] + p[1]).collect();
        }
        rounds.push(poly);
        point.push(c);
    }
    Ok(SumcheckOutput {
        mask_sum,
        rho,
        rounds,
        point,
        broadcasts: log,
    })
}

// ============================================================================
// 3. Column sumcheck: `sum_y M(y) Z(y)` with `M` public, no multiplication
// ============================================================================

/// One party of the column sumcheck: a share of the variable cells and of the mask.
pub struct ColumnParty {
    index: usize,
    z: Vec<E>,
    mask: LibraMask,
}

impl ColumnParty {
    pub fn new(index: usize, z: Vec<E>, mask: LibraMask) -> Self {
        Self { index, z, mask }
    }

    /// Local: share of the masked round polynomial of `M * Z`, which is linear in `Z`.
    fn round_share(&self, matrix: &[E], rho: E, prefix: &[E]) -> Vec<E> {
        let mut q = [E::ZERO; COLUMN_DEGREE + 1];
        for (m, z) in matrix.chunks_exact(2).zip(self.z.chunks_exact(2)) {
            let (dm, dz) = (m[1] - m[0], z[1] - z[0]);
            q[0] += m[0] * z[0];
            q[1] += m[0] * dz + dm * z[0];
            q[2] += dm * dz;
        }
        let mut out = self.mask.round_poly(prefix);
        for c in &mut out {
            *c *= rho;
        }
        add_into(&mut out, &q);
        out
    }

    /// Share of `Z` at the sumcheck point, once all rounds have run. zk-Hem never opens it.
    pub fn terminal_share(&self) -> E {
        self.z[0]
    }

    /// Local: share of the mask value `g(point)`.
    pub fn mask_at_point_share(&self, point: &[E]) -> E {
        self.mask.eval(point)
    }
}

impl Drop for ColumnParty {
    fn drop(&mut self) {
        dregg_sig_asm::volatile_fill(&mut self.z, E::ZERO);
    }
}

/// Masked sumcheck of `sum_y M(y) Z(y)` for a public table `M` and an additively shared
/// `Z`, with the transcript messages of zk-Hem's column sumcheck (`ZKHEM_COL_MASK_SUM`,
/// `ZKHEM_RHO2`, `ZKHEM_COL_ROUND`). Returns the public output and `M` at the point.
///
/// Per round and party: one broadcast of the round polynomial share.
pub fn collab_column_sumcheck(
    parties: &mut [ColumnParty],
    mut matrix: Vec<E>,
    tr: &mut FiatShamirTranscript<InstanceBound>,
) -> Result<(SumcheckOutput, E), CollabError> {
    check_parties(parties.iter().map(|p| p.index))?;
    if matrix.len() < 2 || !matrix.len().is_power_of_two() {
        return Err(CollabError::Malformed);
    }
    let n = matrix.len().trailing_zeros() as usize;
    let mut width = 0;
    for p in parties.iter() {
        let degree = mask_degree(&p.mask).ok_or(CollabError::Malformed)?;
        if p.z.len() != matrix.len()
            || p.mask.num_rounds() != n
            || degree < COLUMN_DEGREE
            || (width != 0 && width != degree + 1)
        {
            return Err(CollabError::Malformed);
        }
        width = degree + 1;
    }
    let mut log = Vec::new();
    let mask_sum = open(
        &mut log,
        BroadcastKind::MaskSum,
        1,
        parties.iter().map(|p| vec![p.mask.sum()]),
    )[0];
    tr.absorb_ext4(b"ZKHEM_COL_MASK_SUM", mask_sum);
    let rho = NonzeroChallenge::squeeze(tr, b"ZKHEM_RHO2").get();
    let mut rounds = Vec::with_capacity(n);
    let mut point: Vec<E> = Vec::with_capacity(n);
    for round in 0..n {
        let poly = open(
            &mut log,
            BroadcastKind::RoundShare { round },
            width,
            parties.iter().map(|p| p.round_share(&matrix, rho, &point)),
        );
        tr.absorb_ext4_slice(b"ZKHEM_COL_ROUND", &poly);
        let c = tr.squeeze_ext4(b"ZKHEM_COL_ROUND");
        for p in parties.iter_mut() {
            fold_in_place(&mut p.z, c);
        }
        fold_in_place(&mut matrix, c);
        rounds.push(poly);
        point.push(c);
    }
    Ok((
        SumcheckOutput {
            mask_sum,
            rho,
            rounds,
            point,
            broadcasts: log,
        },
        matrix[0],
    ))
}

// ============================================================================
// 4. The linear parts of the prover, applied to one party's share
// ============================================================================

/// Local: one party's shares of the row tables `(Az, Bz, Cz)` from its share of the
/// assignment. The constant `1` in cell 0 is shared like any other cell.
pub fn row_table_shares(shape: &Shape, z_share: &[F]) -> [Vec<E>; 3] {
    assert_eq!(z_share.len(), shape.num_vars);
    [&shape.a, &shape.b, &shape.c].map(|matrix| {
        (0..shape.num_rows())
            .map(|i| E::from_base(matrix.row_dot(i, z_share)))
            .collect()
    })
}

/// Public: `M(rx, y) = sum_i eq_rx[i] (r_a A + r_b B + r_c C)[i, y]` on `cells` columns.
pub fn column_matrix(shape: &Shape, eq_rx: &[E], combine: &[E; 3], cells: usize) -> Vec<E> {
    assert!(eq_rx.len() == shape.num_rows() && cells >= shape.num_vars);
    let mut table = vec![E::ZERO; cells];
    for (matrix, &r) in [&shape.a, &shape.b, &shape.c].into_iter().zip(combine) {
        for (i, &weight) in eq_rx.iter().enumerate() {
            for (col, val) in matrix.row(i) {
                table[col] += (r * weight).mul_base(val);
            }
        }
    }
    table
}

/// Local: one party's share of a Stage-0 style codeword of its share of a table, the
/// coset Reed-Solomon encoding of the table's multilinear monomial coefficients.
pub fn codeword_share(table_share: &[F], blowup: usize) -> Vec<F> {
    encode_rs_coset_goldilocks(&hypercube_to_monomial_coeffs(table_share), blowup)
}

/// Local: one party's share of the blended word `U = sum_j beta^j T_j` from its shares of
/// the committed tables (`T_0 = Z`, then the companions).
pub fn blend_share(beta: E, table_shares: &[Vec<F>]) -> Vec<E> {
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

// ============================================================================
// 5. Steps 1 to 3 of zk-Hem on shares
// ============================================================================

/// One custodian's input to [`collab_front_end`].
pub struct FrontParty {
    pub index: usize,
    /// Share of the assignment (`shape.num_vars` cells, masking variables included).
    pub z: Vec<F>,
    pub row_mask: LibraMask,
    pub col_mask: LibraMask,
    /// At least [`row_triples_needed`]`(shape.log_rows)` triples.
    pub triples: Vec<TripleShare>,
}

impl Drop for FrontParty {
    fn drop(&mut self) {
        dregg_sig_asm::volatile_fill(&mut self.z, F::ZERO);
    }
}

/// Public messages of zk-Hem's steps 1 to 3 and the shares the later steps consume.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FrontOutput {
    pub row: SumcheckOutput,
    /// `(Az, Bz, Cz)(rx)`, opened.
    pub row_values: [E; 3],
    pub col: SumcheckOutput,
    pub matrix_at_point: E,
    /// Per party: shares of `g1(rx)`, `g2(ry)` and `Z(ry)`. zk-Hem opens none of them; they
    /// enter the batched linear claim on the committed table.
    pub claim_shares: Vec<[E; 3]>,
    /// The messages opening the row values.
    pub value_broadcasts: Vec<Broadcast>,
}

/// zk-Hem's row sumcheck, row values and column sumcheck for a relation without S-box
/// rows, on an additively shared assignment. `tr` is the transcript after the commitment
/// has been bound; `var_bits` is `Layout::var_bits`.
pub fn collab_front_end(
    shape: &Shape,
    var_bits: usize,
    mut parties: Vec<FrontParty>,
    tr: &mut FiatShamirTranscript<InstanceBound>,
) -> Result<FrontOutput, CollabError> {
    if shape.num_sbox != 0 {
        return Err(CollabError::SboxRows);
    }
    if var_bits >= usize::BITS as usize
        || 1usize << var_bits < shape.num_vars
        || parties.iter().any(|p| p.z.len() != shape.num_vars)
    {
        return Err(CollabError::Malformed);
    }
    let cells = 1usize << var_bits;
    let mut row_parties = Vec::with_capacity(parties.len());
    let mut col_parties = Vec::with_capacity(parties.len());
    for p in &mut parties {
        row_parties.push(RowParty::new(
            p.index,
            row_table_shares(shape, &p.z),
            p.row_mask.clone(),
            core::mem::take(&mut p.triples),
        ));
        let mut z = lift(&p.z);
        z.resize(cells, E::ZERO);
        col_parties.push(ColumnParty::new(p.index, z, p.col_mask.clone()));
    }

    let tau: Vec<E> = (0..shape.log_rows)
        .map(|_| tr.squeeze_ext4(b"ZKHEM_TAU"))
        .collect();
    let row = collab_row_sumcheck(&mut row_parties, &tau, E::ZERO, tr)?;
    let mut value_broadcasts = Vec::new();
    let opened = open(
        &mut value_broadcasts,
        BroadcastKind::Value,
        3,
        row_parties.iter().map(|p| p.terminal_shares().to_vec()),
    );
    let row_values = [opened[0], opened[1], opened[2]];
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &row_values);

    let combine: [E; 3] = core::array::from_fn(|_| tr.squeeze_ext4(b"ZKHEM_COMBINE"));
    let matrix = column_matrix(shape, &build_eq_table_ext4(&row.point), &combine, cells);
    let (col, matrix_at_point) = collab_column_sumcheck(&mut col_parties, matrix, tr)?;
    let claim_shares = row_parties
        .iter()
        .zip(&col_parties)
        .map(|(r, c)| {
            [
                r.mask_at_point_share(&row.point),
                c.mask_at_point_share(&col.point),
                c.terminal_share(),
            ]
        })
        .collect();
    Ok(FrontOutput {
        row,
        row_values,
        col,
        matrix_at_point,
        claim_shares,
        value_broadcasts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use dregg_sig_agg::field::{intt_goldilocks, mle_eval_ext4};
    use dregg_sig_agg::pcs::WhirSecurityRegime;
    use dregg_sig_agg::sponge::cshake256_32;
    use dregg_sig_agg::zk_hem::protocol::{self, COL_DEGREE, Layout, ROW_DEGREE};
    use dregg_sig_agg::zk_hem::relation::{ConstraintSystem, Lc};
    use dregg_sig_agg::zk_hem::{LibraView, PrimitiveChallenge, SeedStream, interp, libra_verify};

    fn coins(tag: u8) -> SeedStream {
        SeedStream::new(b"DREGG.TEST.COLLAB", &[tag; 32])
    }

    fn transcript(tag: u8) -> FiatShamirTranscript<InstanceBound> {
        let schedule = WhirSecurityRegime::default().schedule(4);
        FiatShamirTranscript::new()
            .bind_relation(b"DREGG.TEST.COLLAB/v1", &[0; 32], &schedule)
            .bind_instance(&[&[tag]])
    }

    fn random_table(s: &mut SeedStream, len: usize) -> Vec<E> {
        (0..len).map(|_| s.next_ext4()).collect()
    }

    /// Tables with `A * B = C` in every row.
    fn satisfying(s: &mut SeedStream, n: usize) -> [Vec<E>; 3] {
        let a = random_table(s, 1 << n);
        let b = random_table(s, 1 << n);
        let c = a.iter().zip(&b).map(|(&x, &y)| x * y).collect();
        [a, b, c]
    }

    /// A dealer for the triple functionality: additive shares of uniform triples.
    fn deal_triples(s: &mut SeedStream, count: usize, parties: usize) -> Vec<Vec<TripleShare>> {
        let mut out = vec![Vec::with_capacity(count); parties];
        for _ in 0..count {
            let (a, b) = (s.next_ext4(), s.next_ext4());
            let shares = share_additive(&[a, b, a * b], parties, || s.next_ext4());
            for (party, share) in out.iter_mut().zip(&shares) {
                party.push(TripleShare {
                    a: share[0],
                    b: share[1],
                    c: share[2],
                });
            }
        }
        out
    }

    struct Dealt {
        tables: Vec<[Vec<E>; 3]>,
        masks: Vec<LibraMask>,
        triples: Vec<Vec<TripleShare>>,
    }

    impl Dealt {
        fn new(s: &mut SeedStream, tables: &[Vec<E>; 3], mask: &LibraMask, parties: usize) -> Self {
            let n = mask.num_rounds();
            let per_table = tables
                .each_ref()
                .map(|t| share_additive(t, parties, || s.next_ext4()));
            Self {
                tables: (0..parties)
                    .map(|p| per_table.each_ref().map(|shares| shares[p].clone()))
                    .collect(),
                masks: share_mask(mask, parties, || s.next_ext4()),
                triples: deal_triples(s, row_triples_needed(n), parties),
            }
        }

        fn parties(&self) -> Vec<RowParty> {
            (0..self.tables.len())
                .map(|p| {
                    RowParty::new(
                        p,
                        self.tables[p].clone(),
                        self.masks[p].clone(),
                        self.triples[p].clone(),
                    )
                })
                .collect()
        }
    }

    /// Unmasked row round polynomials from the definition, along given challenges: `eq`
    /// as a fourth table, every table folded, four evaluation points per pair. Also the
    /// tables at the point.
    fn plain_rounds(tables: &[Vec<E>; 3], tau: &[E], challenges: &[E]) -> (Vec<Vec<E>>, [E; 3]) {
        let mut eq = build_eq_table_ext4(tau);
        let mut t = tables.clone();
        let xs: Vec<E> = (0..=ROW_PRODUCT_DEGREE as u64).map(E::from_u64).collect();
        let mut rounds = Vec::new();
        for &c in challenges {
            let evals: Vec<E> = xs
                .iter()
                .map(|&x| {
                    (0..eq.len() / 2).fold(E::ZERO, |acc, k| {
                        let at = |t: &Vec<E>| t[2 * k] + x * (t[2 * k + 1] - t[2 * k]);
                        acc + at(&eq) * (at(&t[0]) * at(&t[1]) - at(&t[2]))
                    })
                })
                .collect();
            rounds.push(interp(&xs, &evals).unwrap());
            fold_in_place(&mut eq, c);
            for table in &mut t {
                fold_in_place(table, c);
            }
        }
        (rounds, [t[0][0], t[1][0], t[2][0]])
    }

    /// The single prover: the masked sumcheck loop of `zk_hem::protocol`.
    fn single_prover(
        tables: &[Vec<E>; 3],
        mask: &LibraMask,
        tau: &[E],
        tr: &mut FiatShamirTranscript<InstanceBound>,
    ) -> (E, Vec<Vec<E>>, Vec<E>, [E; 3]) {
        let mask_sum = mask.sum();
        tr.absorb_ext4(b"ZKHEM_ROW_MASK_SUM", mask_sum);
        let rho = NonzeroChallenge::squeeze(tr, b"ZKHEM_RHO1").get();
        let mut rounds = Vec::new();
        let mut point = Vec::new();
        for _ in 0..tau.len() {
            // Recomputing every earlier round keeps this independent of any folding state.
            let mut trial = point.clone();
            trial.push(E::ZERO);
            let f = plain_rounds(tables, tau, &trial).0.pop().unwrap();
            let mut poly = mask.round_poly(&point);
            for c in &mut poly {
                *c *= rho;
            }
            add_into(&mut poly, &f);
            tr.absorb_ext4_slice(b"ZKHEM_ROW_ROUND", &poly);
            point.push(tr.squeeze_ext4(b"ZKHEM_ROW_ROUND"));
            rounds.push(poly);
        }
        let values = plain_rounds(tables, tau, &point).1;
        (mask_sum, rounds, point, values)
    }

    fn open_terminals(parties: &[RowParty]) -> (Vec<[E; 3]>, [E; 3]) {
        let shares: Vec<[E; 3]> = parties.iter().map(RowParty::terminal_shares).collect();
        let total = shares.iter().fold([E::ZERO; 3], |acc, s| {
            core::array::from_fn(|j| acc[j] + s[j])
        });
        (shares, total)
    }

    #[test]
    fn row_sumcheck_on_shares_equals_the_single_prover_transcript() {
        let mut s = coins(1);
        for (n, parties, degree) in [(1usize, 2usize, 3usize), (3, 3, 3), (5, 5, 9), (6, 3, 4)] {
            let tables = satisfying(&mut s, n);
            let mask = LibraMask::from_stream(&mut s, n, degree);
            let tau = random_table(&mut s, n);
            let (mask_sum, rounds, point, values) =
                single_prover(&tables, &mask, &tau, &mut transcript(7));

            let dealt = Dealt::new(&mut s, &tables, &mask, parties);
            let mut run = dealt.parties();
            let out = collab_row_sumcheck(&mut run, &tau, E::ZERO, &mut transcript(7)).unwrap();
            assert_eq!(out.mask_sum, mask_sum);
            assert_eq!(out.rounds, rounds);
            assert_eq!(out.point, point);
            assert!(out.rounds.iter().all(|r| r.len() == degree + 1));
            assert_eq!(open_terminals(&run).1, values);
            for (j, table) in tables.iter().enumerate() {
                assert_eq!(values[j], mle_eval_ext4(table, &point));
            }

            // The masked verifier accepts and is left with the gate at the point.
            let view = LibraView {
                g_sum: out.mask_sum,
                rounds: out.rounds.clone(),
                g_at_point: run
                    .iter()
                    .fold(E::ZERO, |acc, p| acc + p.mask_at_point_share(&point)),
            };
            let eq = mle_eval_ext4(&build_eq_table_ext4(&tau), &point);
            assert_eq!(
                libra_verify(E::ZERO, &view, out.rho, &point, degree),
                Some(eq * (values[0] * values[1] - values[2]))
            );

            // A transcript bound to another instance gives other challenges.
            let other =
                collab_row_sumcheck(&mut dealt.parties(), &tau, E::ZERO, &mut transcript(8))
                    .unwrap();
            assert_ne!(other.point, point);
        }
    }

    #[test]
    fn row_sumcheck_rejects_malformed_runs() {
        let mut s = coins(2);
        let n = 3;
        let tables = satisfying(&mut s, n);
        let mask = LibraMask::from_stream(&mut s, n, 3);
        let tau = random_table(&mut s, n);
        let dealt = Dealt::new(&mut s, &tables, &mask, 3);
        let run = |parties: &mut [RowParty], tau: &[E]| {
            collab_row_sumcheck(parties, tau, E::ZERO, &mut transcript(1)).map(|_| ())
        };

        let mut short = dealt.parties();
        short[1].triples.pop();
        assert_eq!(run(&mut short, &tau), Err(CollabError::OutOfTriples));
        let mut swapped = dealt.parties();
        swapped.swap(0, 1);
        assert_eq!(run(&mut swapped, &tau), Err(CollabError::Malformed));
        assert_eq!(
            run(&mut dealt.parties()[..1], &tau),
            Err(CollabError::Malformed)
        );
        assert_eq!(
            run(&mut dealt.parties(), &tau[..2]),
            Err(CollabError::Malformed)
        );
        let mut zero_tau = tau.clone();
        zero_tau[1] = E::ZERO;
        assert_eq!(
            run(&mut dealt.parties(), &zero_tau),
            Err(CollabError::DegenerateChallenge)
        );
        assert_eq!(run(&mut dealt.parties(), &tau), Ok(()));

        // A wrong triple share changes the transcript.
        let honest =
            collab_row_sumcheck(&mut dealt.parties(), &tau, E::ZERO, &mut transcript(1)).unwrap();
        let mut bad = dealt.parties();
        bad[2].triples[0].c += E::ONE;
        let wrong = collab_row_sumcheck(&mut bad, &tau, E::ZERO, &mut transcript(1)).unwrap();
        assert_ne!(wrong.rounds, honest.rounds);
    }

    /// Everything a coalition holding all parties but `honest` sees, for two witnesses.
    ///
    /// Run 1 uses witness `W`. A second satisfying witness `W'` with the same opened row
    /// values is built from the run-1 challenge point. The honest party's secret state for
    /// run 2 is the run-1 state translated by offsets that depend only on `W`, `W'` and
    /// the public transcript: its table shares by `W' - W`, the mask by the difference of
    /// the unmasked round polynomials over `rho`, the triples by the difference of the
    /// multiplication inputs. Translations are bijections of the honest party's uniform
    /// coins, so equal views for the translated coins is equal view distributions.
    #[test]
    fn coalition_view_does_not_depend_on_the_witness() {
        let (n, parties, degree) = (4usize, 3usize, 3usize);
        for honest in 0..parties {
            let mut s = coins(10 + honest as u8);
            let w = satisfying(&mut s, n);
            let mask = LibraMask::from_stream(&mut s, n, degree);
            let tau = random_table(&mut s, n);
            let dealt = Dealt::new(&mut s, &w, &mask, parties);
            let mut run1 = dealt.parties();
            let out1 = collab_row_sumcheck(&mut run1, &tau, E::ZERO, &mut transcript(3)).unwrap();
            let (terminal1, values) = open_terminals(&run1);
            let rx = &out1.point;

            // A different satisfying witness with the same values at `rx`.
            let e = build_eq_table_ext4(rx);
            let mut b2 = random_table(&mut s, 1 << n);
            let gap = values[1] - mle_eval_ext4(&b2, rx);
            b2[0] += gap * e[0].inv();
            let mut a2 = random_table(&mut s, 1 << n);
            let (mut rest_a, mut rest_c) = (values[0], values[2]);
            for x in 2..1 << n {
                rest_a -= e[x] * a2[x];
                rest_c -= e[x] * b2[x] * a2[x];
            }
            // e0 a0 + e1 a1 = rest_a and e0 b0 a0 + e1 b1 a1 = rest_c.
            let det_inv = (e[0] * e[1] * (b2[1] - b2[0])).inv();
            a2[0] = (rest_a * e[1] * b2[1] - rest_c * e[1]) * det_inv;
            a2[1] = (rest_c * e[0] - rest_a * e[0] * b2[0]) * det_inv;
            let c2: Vec<E> = a2.iter().zip(&b2).map(|(&x, &y)| x * y).collect();
            let w2 = [a2, b2, c2];
            assert_ne!(w2, w);
            let (f1, v1) = plain_rounds(&w, &tau, rx);
            let (f2, v2) = plain_rounds(&w2, &tau, rx);
            assert_eq!((v1, v2), (values, values));
            assert_ne!(f1, f2);

            // The mask that gives `W'` the transcript of `W`.
            let mut mask2 = mask.clone();
            let mut pow = E::ONE;
            let mut shift = E::ZERO;
            for i in (0..n).rev() {
                let scale = (out1.rho * pow).inv();
                for k in 0..degree {
                    let delta = (f1[i][k + 1] - f2[i][k + 1]) * scale;
                    mask2.a[i][k] += delta;
                    shift += delta;
                }
                pow = pow + pow;
            }
            mask2.a0 -= shift * E::from_u64(2).inv();
            assert_eq!(mask2.sum(), mask.sum());

            // Run-2 state: the coalition keeps its run-1 state, the honest party's is
            // translated.
            let mut dealt2 = Dealt {
                tables: dealt.tables.clone(),
                masks: dealt.masks.clone(),
                triples: dealt.triples.clone(),
            };
            for j in 0..3 {
                for x in 0..1 << n {
                    dealt2.tables[honest][j][x] += w2[j][x] - w[j][x];
                }
            }
            dealt2.masks[honest].a0 += mask2.a0 - mask.a0;
            for i in 0..n {
                for k in 0..degree {
                    dealt2.masks[honest].a[i][k] += mask2.a[i][k] - mask.a[i][k];
                }
            }
            let unprogrammed = dealt2.parties();
            // Triples: the opened `(x - a, y - b)` of run 1 with the inputs of run 2.
            let mut folded = [w2[0].clone(), w2[1].clone()];
            let mut index = 0;
            for (round, &challenge) in rx.iter().enumerate() {
                let opened = out1
                    .broadcasts
                    .iter()
                    .filter(|m| m.kind == BroadcastKind::MaskedInputs { round })
                    .fold(vec![E::ZERO; 2 * folded[0].len()], |mut acc, m| {
                        add_into(&mut acc, &m.values);
                        acc
                    });
                for k in 0..folded[0].len() / 2 {
                    let [a, b] = folded
                        .each_ref()
                        .map(|t| (t[2 * k], t[2 * k + 1] - t[2 * k]));
                    for (m, (x, y)) in [(a.0, b.0), (a.1, b.1)].into_iter().enumerate() {
                        let ta = x - opened[4 * k + 2 * m];
                        let tb = y - opened[4 * k + 2 * m + 1];
                        let mut share = TripleShare {
                            a: ta,
                            b: tb,
                            c: ta * tb,
                        };
                        for p in (0..parties).filter(|&p| p != honest) {
                            let t = dealt.triples[p][index];
                            share.a -= t.a;
                            share.b -= t.b;
                            share.c -= t.c;
                        }
                        dealt2.triples[honest][index] = share;
                        index += 1;
                    }
                }
                for table in &mut folded {
                    fold_in_place(table, challenge);
                }
            }
            assert_eq!(index, row_triples_needed(n));
            assert_ne!(dealt2.tables[honest], dealt.tables[honest]);
            assert_ne!(dealt2.triples[honest], dealt.triples[honest]);

            let mut run2 = dealt2.parties();
            let out2 = collab_row_sumcheck(&mut run2, &tau, E::ZERO, &mut transcript(3)).unwrap();
            // The coalition's initial state is the same by construction; every message,
            // the honest party's included, and every opened terminal share are equal.
            assert_eq!(out2, out1);
            assert_eq!(open_terminals(&run2), (terminal1.clone(), values));

            // Controls. Without the reprogrammed triples the honest party's masked inputs
            // change; without the adjusted mask the public transcript changes.
            let mut plain_triples = unprogrammed;
            let out3 =
                collab_row_sumcheck(&mut plain_triples, &tau, E::ZERO, &mut transcript(3)).unwrap();
            assert_eq!(out3.rounds[0], out1.rounds[0]);
            assert_ne!(out3.broadcasts, out1.broadcasts);
            dealt2.masks[honest] = dealt.masks[honest].clone();
            let out4 =
                collab_row_sumcheck(&mut dealt2.parties(), &tau, E::ZERO, &mut transcript(3))
                    .unwrap();
            assert_ne!(out4.rounds, out1.rounds);
        }
    }

    #[test]
    fn column_sumcheck_on_shares_equals_the_single_prover_transcript() {
        let mut s = coins(20);
        for (n, parties, degree) in [(1usize, 2usize, 2usize), (4, 3, 2), (6, 5, 3)] {
            let z: Vec<E> = (0..1 << n).map(|_| E::from_base(s.next_base())).collect();
            let matrix = random_table(&mut s, 1 << n);
            let mask = LibraMask::from_stream(&mut s, n, degree);

            // Single prover: three evaluation points per pair, as in `zk_hem::protocol`.
            let mut tr = transcript(4);
            tr.absorb_ext4(b"ZKHEM_COL_MASK_SUM", mask.sum());
            let rho = NonzeroChallenge::squeeze(&mut tr, b"ZKHEM_RHO2").get();
            let xs: Vec<E> = (0..=COLUMN_DEGREE as u64).map(E::from_u64).collect();
            let (mut tm, mut tz) = (matrix.clone(), z.clone());
            let mut rounds = Vec::new();
            let mut point = Vec::new();
            for _ in 0..n {
                let evals: Vec<E> = xs
                    .iter()
                    .map(|&x| {
                        (0..tm.len() / 2).fold(E::ZERO, |acc, k| {
                            let at = |t: &Vec<E>| t[2 * k] + x * (t[2 * k + 1] - t[2 * k]);
                            acc + at(&tm) * at(&tz)
                        })
                    })
                    .collect();
                let mut poly = mask.round_poly(&point);
                for c in &mut poly {
                    *c *= rho;
                }
                add_into(&mut poly, &interp(&xs, &evals).unwrap());
                tr.absorb_ext4_slice(b"ZKHEM_COL_ROUND", &poly);
                let c = tr.squeeze_ext4(b"ZKHEM_COL_ROUND");
                fold_in_place(&mut tm, c);
                fold_in_place(&mut tz, c);
                rounds.push(poly);
                point.push(c);
            }

            let z_shares = share_additive(&z, parties, || s.next_ext4());
            let masks = share_mask(&mask, parties, || s.next_ext4());
            let mut run: Vec<ColumnParty> = (0..parties)
                .map(|p| ColumnParty::new(p, z_shares[p].clone(), masks[p].clone()))
                .collect();
            let (out, matrix_at_point) =
                collab_column_sumcheck(&mut run, matrix.clone(), &mut transcript(4)).unwrap();
            assert_eq!(out.rounds, rounds);
            assert_eq!(out.point, point);
            assert_eq!(matrix_at_point, mle_eval_ext4(&matrix, &point));
            let z_at_point = run.iter().fold(E::ZERO, |acc, p| acc + p.terminal_share());
            assert_eq!(z_at_point, mle_eval_ext4(&z, &point));
            // No message of this sumcheck is a multiplication opening.
            assert!(
                out.broadcasts
                    .iter()
                    .all(|m| !matches!(m.kind, BroadcastKind::MaskedInputs { .. }))
            );
        }
    }

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    /// `x * y = 35` with `x` Boolean-free, a square and a public input, multiplication
    /// rows only.
    fn small_relation() -> (Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        let p = cs.public_input(f(35));
        let x: Lc = cs.alloc(f(5)).into();
        let y: Lc = cs.alloc(f(7)).into();
        let prod = cs.mul(&x, &y);
        cs.enforce_equal(&prod.into(), &p.into());
        let sq = cs.mul(&x, &x);
        let cube = cs.mul(&sq.into(), &x);
        cs.enforce_zero(Lc::from(cube).plus_const(F::ZERO - f(125)));
        let bit: Lc = cs.alloc(f(1)).into();
        cs.enforce_boolean(&bit);
        cs.finish()
    }

    /// The real zk-Hem prover and the collaborative front end, on the same coins: the
    /// proof's mask sums, round polynomials and row values are reproduced from shares.
    #[test]
    fn front_end_reproduces_the_messages_of_the_zk_hem_prover() {
        let regime = WhirSecurityRegime::default();
        let (shape, assignment) = small_relation();
        assert_eq!(shape.num_sbox, 0);
        let statement = b"collab front end";
        let seed = [0x5a; 32];
        let proof = protocol::prove(&shape, assignment.clone(), statement, regime, &seed).unwrap();
        let publics = assignment[1..=shape.num_public].to_vec();
        assert!(protocol::verify(
            &shape, &publics, statement, regime, &proof
        ));
        let layout = Layout::new(&shape, regime).unwrap();

        // The prover's coins, as `protocol::prove` derives them.
        let mut coin_input = seed.to_vec();
        coin_input.extend_from_slice(&shape.digest());
        coin_input.extend_from_slice(&cshake256_32(b"QSAG.ZKHEM.COINS.STMT/v1", statement));
        let witness_bytes: Vec<u8> = assignment.iter().flat_map(|v| v.to_le_bytes()).collect();
        coin_input.extend_from_slice(&cshake256_32(b"QSAG.ZKHEM.COINS.WIT/v1", &witness_bytes));
        let coin_seed = cshake256_32(b"QSAG.ZKHEM.COINS.SEED/v1", &coin_input);
        let mut stream = SeedStream::new(b"QSAG.ZKHEM.COINS/v1", &coin_seed);
        let mut z = assignment.clone();
        for slot in &mut z[shape.mask_var_base..] {
            *slot = stream.next_base();
        }
        assert!(shape.is_satisfied(&z));
        let mut mask = |rounds: usize, degree: usize| {
            let coef: Vec<Vec<E>> = (0..rounds)
                .map(|_| (0..=degree).map(|_| stream.next_ext4()).collect())
                .collect();
            LibraMask {
                a0: coef.iter().fold(E::ZERO, |acc, row| acc + row[0]),
                a: coef.iter().map(|row| row[1..].to_vec()).collect(),
            }
        };
        let row_mask = mask(shape.log_rows, ROW_DEGREE);
        let col_mask = mask(layout.var_bits, COL_DEGREE);

        // The transcript after the commitment, as `protocol::verify` starts it.
        let start = || {
            let public_bytes: Vec<u8> = publics.iter().flat_map(|v| v.to_le_bytes()).collect();
            let mut params = shape.digest().to_vec();
            for n in [layout.log_cells, layout.var_bits, layout.blind_cells] {
                params.extend_from_slice(&(n as u64).to_le_bytes());
            }
            FiatShamirTranscript::new()
                .bind_relation(b"QSAG.ZKHEM.COMMITTED/v1", &params, &layout.schedule)
                .bind_instance(&[statement, &public_bytes, &proof.commitment.to_bytes()])
        };

        for parties in [2usize, 3, 5] {
            let mut s = coins(30 + parties as u8);
            let z_shares = share_additive(&z, parties, || s.next_base());
            assert!(z_shares.iter().all(|share| share != &z));
            let row_masks = share_mask(&row_mask, parties, || s.next_ext4());
            let col_masks = share_mask(&col_mask, parties, || s.next_ext4());
            let triples = deal_triples(&mut s, row_triples_needed(shape.log_rows), parties);
            let custodians: Vec<FrontParty> = (0..parties)
                .map(|p| FrontParty {
                    index: p,
                    z: z_shares[p].clone(),
                    row_mask: row_masks[p].clone(),
                    col_mask: col_masks[p].clone(),
                    triples: triples[p].clone(),
                })
                .collect();
            let out = collab_front_end(&shape, layout.var_bits, custodians, &mut start()).unwrap();
            assert_eq!(out.row.mask_sum, proof.row_mask_sum);
            assert_eq!(out.row.rounds, proof.row_rounds);
            assert_eq!(out.row_values, proof.row_values);
            assert_eq!(out.col.mask_sum, proof.col_mask_sum);
            assert_eq!(out.col.rounds, proof.col_rounds);

            // The shares left for the linear claim reconstruct to the committed values.
            let total = out.claim_shares.iter().fold([E::ZERO; 3], |acc, sh| {
                core::array::from_fn(|j| acc[j] + sh[j])
            });
            assert_eq!(total[0], row_mask.eval(&out.row.point));
            assert_eq!(total[1], col_mask.eval(&out.col.point));
            let mut padded = lift(&z);
            padded.resize(1 << layout.var_bits, E::ZERO);
            assert_eq!(total[2], mle_eval_ext4(&padded, &out.col.point));
        }

        // A front end fed a different witness share does not reproduce the proof.
        let mut s = coins(40);
        let mut z_shares = share_additive(&z, 2, || s.next_base());
        z_shares[1][shape.num_public + 1] += F::ONE;
        let row_masks = share_mask(&row_mask, 2, || s.next_ext4());
        let col_masks = share_mask(&col_mask, 2, || s.next_ext4());
        let triples = deal_triples(&mut s, row_triples_needed(shape.log_rows), 2);
        let custodians: Vec<FrontParty> = (0..2)
            .map(|p| FrontParty {
                index: p,
                z: z_shares[p].clone(),
                row_mask: row_masks[p].clone(),
                col_mask: col_masks[p].clone(),
                triples: triples[p].clone(),
            })
            .collect();
        let out = collab_front_end(&shape, layout.var_bits, custodians, &mut start()).unwrap();
        assert_ne!(out.row.rounds, proof.row_rounds);
    }

    #[test]
    fn front_end_refuses_sbox_rows() {
        let mut cs = ConstraintSystem::new();
        let x: Lc = cs.alloc(f(3)).into();
        cs.sbox7(&x);
        let (shape, _) = cs.finish();
        assert!(shape.num_sbox > 0);
        let mut tr = transcript(5);
        assert_eq!(
            collab_front_end(&shape, 8, Vec::new(), &mut tr).map(|_| ()),
            Err(CollabError::SboxRows)
        );
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
        let (shape, assignment) = small_relation();
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

    /// The numbers the module comment's estimate is computed from.
    #[test]
    fn estimate_inputs() {
        let log_rows = 20;
        assert_eq!(row_triples_needed(log_rows), 2_097_150);
        let schedule = WhirSecurityRegime::default().schedule(21);
        let st0 = schedule.stages[0];
        assert_eq!((st0.blowup, st0.step_vars, st0.num_queries), (4, 6, 258));
        // Field values in one custodian's Stage-0 opening: five tables, 8-byte symbols.
        assert_eq!(st0.num_queries * ((5 * 8) << st0.step_vars), 660_480);
        // Cells: variables, masks, blinders fit a table of 2^21.
        let masks = ((log_rows * 4) << 4) + ((20 * 4) << 2);
        let blind = st0.num_queries << st0.step_vars;
        assert!((1usize << 20) + masks + blind <= 1 << 21);
        // Triples in `FieldTriple`s, nine per `Ext4` product, and their size and time.
        let triples = (1u64 << 20) + 9 * row_triples_needed(log_rows) as u64;
        assert_eq!(triples, 19_922_926);
        assert_eq!((triples * 288) >> 20, 5_471);
        assert_eq!(triples * 2 / 1000 / 3600, 11);
    }
}
