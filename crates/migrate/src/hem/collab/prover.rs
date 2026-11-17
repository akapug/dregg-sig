//! One custodian's side of the collaborative zk-Hem prover.
//!
//! The steps, what each opens and why each opening is safe are in the module comment of
//! [`super`]. Every custodian runs [`prove_party`] with its authenticated shares of the
//! assignment and ends with the same [`ZkHemSplitProof`], which it has verified.
//!
//! # Lookups
//!
//! A relation with lookups (`zk_hem::relation::Lookups`, steps L1 to L4 of
//! `zk_hem::protocol`) is proved on shares as follows. The multiplicities are variables of
//! the assignment, so their shares arrive with `z` like every other variable.
//!
//! * Helpers. For a fraction with a shared value `v` and a public numerator `c` (a
//!   lookup), `h = c / (alpha - v)` by the masked inversion of Bar-Ilan and Beaver: open
//!   `w = r (alpha - v)` for a preprocessed uniform `r` in the extension field and set
//!   `h = (c / w) r`. `r v` is four base-field products per tuple column that is not a
//!   public constant. `w` is uniform whatever was sent before, like a Beaver opening. For
//!   a fraction with a public value (a table row), `h = n / (alpha - v)` is linear in the
//!   shared numerator. The four masking helpers are preprocessed uniform values.
//! * Helper commitment. Each custodian commits to the value part of its shares of the
//!   helper table (helper limbs, the lookup sumcheck mask, blinders: all authenticated)
//!   and to four companions of its own, and broadcasts the root. The transcript binds the
//!   list of helper roots.
//! * Lookup sumcheck of `sel (h + lambda eq (h (alpha - v) - n))`. Per round and live pair
//!   of entries three extension-field products give `h(X) v(X)`; everything else is
//!   public or linear, and the linear coefficient of a round polynomial is taken from the
//!   running claim. Opened, each after a MAC check: the mask sum, the masked round
//!   polynomials, then `(n, v, h)(rl)`.
//! * The column sumcheck takes the two lookup weights; the zero test covers the helper
//!   table's linear claim with a second uniform multiplier; the companion claims, the
//!   blended helper word and the Stage-0 leaves of the helper roots follow those of the
//!   assignment table.
//!
//! Privacy is the argument of [`super`] with the helper table in the place of the
//! assignment table: the inversion openings are one-time-padded, the round polynomials are
//! masked, the three revealed values are uniform by the masking entries for a satisfying
//! and for an unsatisfying assignment alike, and nothing that depends on the helper claim
//! is opened before the zero test. As there, this is an argument and not a proof.
//!
//! Cost per custodian for `L` lookups of one shared column and `2^d` fractions: `4 L`
//! triples for the inversions and 48 per live pair of the sumcheck, about `48 * 2^d` in
//! all, against `17 * 8` per byte for a bit decomposition in the row sumcheck.
//! [`prover_demand`] is exact. Not here, as for every other hint: producing the shares of
//! the multiplicities from shares of the looked-up values, which needs their one-hot
//! encodings (`2^b - b - 1` products from the `b` shared bits of a value in a `b`-bit
//! table: 247 for a byte, 11 for a nibble).

use alloc::vec;
use alloc::vec::Vec;

use dregg_sig_agg::field::{Goldilocks, GoldilocksExt4, GoldilocksOps as _, build_eq_table_ext4};
use dregg_sig_agg::pcs::{
    CanopyCommitment, CanopyMultiProof, Stage0ShareOpening, WhirSecurityRegime,
    hypercube_to_monomial_coeffs_ext4, whir_commit_batch_secret_with_schedule,
    whir_open_blend_split, whir_stage0_open_share,
};
use dregg_sig_agg::pcs::{HemWhirProverState, HemWhirSplitOpeningProof, WeightedPoint, WhirSchedule};
use dregg_sig_agg::zk_hem::protocol::{
    COL_DEGREE, COL_MASK_BITS, COMPANIONS, FrontMessages, LOOKUP_DEGREE, LOOKUP_MASK_BITS, Layout,
    LookupLayout, LookupMessages, LookupRoots, MAX_SPLIT_COMMITTERS, ROW_DEGREE, ROW_MASK_BITS,
    SplitLookupProof, ZkHemSplitProof, blend_claim, claim_kernel, lookup_column_add,
    lookup_masks_full_rank, mask_rows_full_rank, replay_front, split_transcript, verify_split,
};
use dregg_sig_agg::zk_hem::relation::{Csr, LOOKUP_MASK_ENTRIES, Lookups, Shape};
use dregg_sig_agg::zk_hem::{LibraMask, NonzeroChallenge};

use super::engine::{Engine, MpcError, Sb, Sh};
use super::net::Transport;

type E = GoldilocksExt4;
type F = Goldilocks;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProveError {
    Mpc(MpcError),
    /// The relation does not fit a commitment, or the quorum is too large.
    Unsupported,
    /// The relation has S-box rows.
    SboxRows,
    /// The share vector does not have one entry per variable.
    Malformed,
    /// A peer's Stage-0 opening or root does not decode.
    BadPeerMessage {
        from: usize,
    },
    /// A row challenge `tau_i` is zero (probability `2^-256` per round).
    DegenerateChallenge,
    /// The row point left the masking rows without full rank; rerun with fresh material.
    MaskRankDeficient,
    /// The shared assignment does not satisfy the relation. Nothing that depends on the
    /// assignment beyond this one bit has been opened.
    Unsatisfied,
    /// The assembled proof does not verify: some custodian committed to tables that are
    /// not its shares, or opened a wrong leaf.
    Rejected,
}

impl From<MpcError> for ProveError {
    fn from(e: MpcError) -> Self {
        Self::Mpc(e)
    }
}

/// A point where a custodian may deviate, for adversarial tests: the hook receives what
/// the custodian is about to use or send and may change it.
pub enum Fault<'a> {
    /// The value table about to be committed (the custodian's shares of `Z`).
    Table(&'a mut Vec<F>),
    /// The share of a masked row-round polynomial about to be opened.
    RoundShare(&'a mut Vec<Sh>),
    /// The share of the blended word about to be sent, 32 bytes a cell.
    Word(&'a mut Vec<u8>),
    /// The Stage-0 leaves about to be opened.
    Leaves(&'a mut Stage0ShareOpening),
}

/// Triples and uniform values one custodian's [`prove_party`] consumes for `shape`.
pub fn prover_demand(shape: &Shape, regime: WhirSecurityRegime) -> Option<(usize, usize)> {
    let layout = Layout::new(shape, regime)?;
    let half = 1usize << (shape.log_rows - 1);
    // Round 0 multiplies base-field values, later rounds extension-field values; the
    // zero test is one extension-field product.
    let triples = 2 * half + 32 * (half - 1) + 16;
    let randoms = shape.num_vars - shape.mask_var_base
        + 4 * (shape.log_rows * (ROW_DEGREE + 1) + layout.var_bits * (COL_DEGREE + 1))
        + layout.blind_cells
        + 4;
    let (lookup_triples, lookup_randoms) = match (shape.lookups(), &layout.lookup) {
        (Some(lookups), Some(ll)) => lookup_demand(lookups, ll)?,
        _ => (0, 0),
    };
    Some((triples + lookup_triples, randoms + lookup_randoms))
}

/// How the helper of one fraction is computed from shares.
enum Helper {
    /// Numerator zero: the helper is zero.
    Zero,
    /// Public value `v`: `h = n / (alpha - v)`.
    PublicValue,
    /// Public numerator and shared value with this many shared tuple columns.
    Inversion { shared_columns: usize },
}

/// The public constant a linear form evaluates to, if it has no other term.
fn public_form(matrix: &Csr, i: usize) -> Option<F> {
    matrix
        .row(i)
        .try_fold(F::ZERO, |acc, (col, val)| (col == 0).then_some(acc + val))
}

/// `None` for a fraction with a shared numerator over a shared value, which the builder
/// never produces.
fn helper_kind(lookups: &Lookups, i: usize) -> Option<Helper> {
    if lookups.num.row(i).next().is_none() {
        return Some(Helper::Zero);
    }
    let shared_columns = lookups
        .den
        .iter()
        .filter(|m| public_form(m, i).is_none())
        .count();
    if shared_columns == 0 {
        Some(Helper::PublicValue)
    } else {
        public_form(&lookups.num, i).map(|_| Helper::Inversion { shared_columns })
    }
}

/// Live pairs of lookup-sumcheck round `round`: those not entirely above the selector
/// boundary.
fn lookup_live_pairs(lookups: &Lookups, round: usize) -> usize {
    let pairs = lookups.num_entries() >> (round + 1);
    ((lookups.num_checked() >> round) / 2 + 1).min(pairs)
}

/// Triples and uniform values the lookup steps consume.
fn lookup_demand(lookups: &Lookups, ll: &LookupLayout) -> Option<(usize, usize)> {
    let d = lookups.log_entries;
    let (mut triples, mut randoms) = (0, 0);
    for i in 0..lookups.num_checked() {
        if let Helper::Inversion { shared_columns } = helper_kind(lookups, i)? {
            triples += 4 * shared_columns;
            randoms += 4;
        }
    }
    triples += (0..d)
        .map(|round| 48 * lookup_live_pairs(lookups, round))
        .sum::<usize>();
    // The second zero-test product and its multiplier.
    triples += 16;
    randoms += 4 * LOOKUP_MASK_ENTRIES + 4 * d * (LOOKUP_DEGREE + 1) + ll.blind_cells + 4;
    Some((triples, randoms))
}

/// An authenticated sumcheck mask: the three components of the coefficient shares.
struct MaskShare {
    parts: [LibraMask; 3],
}

impl MaskShare {
    fn new(coef: &[Vec<Sh>]) -> Self {
        let part = |pick: fn(&Sh) -> E| LibraMask {
            a0: coef.iter().fold(E::ZERO, |acc, row| acc + pick(&row[0])),
            a: coef
                .iter()
                .map(|row| row[1..].iter().map(pick).collect())
                .collect(),
        };
        Self {
            parts: [part(|s| s.v), part(|s| s.m[0]), part(|s| s.m[1])],
        }
    }

    fn zip(parts: [Vec<E>; 3]) -> Vec<Sh> {
        let [v, m0, m1] = parts;
        v.into_iter()
            .zip(m0)
            .zip(m1)
            .map(|((v, m0), m1)| Sh { v, m: [m0, m1] })
            .collect()
    }

    fn sum(&self) -> Sh {
        Self::zip(self.parts.each_ref().map(|p| vec![p.sum()]))[0]
    }

    fn round_poly(&self, prefix: &[E]) -> Vec<Sh> {
        Self::zip(self.parts.each_ref().map(|p| p.round_poly(prefix)))
    }
}

/// Sample one mask: per round `degree + 1` coefficients, each from four uniform base
/// values, and the cells that hold them in the committed table.
fn sample_mask<T: Transport>(
    e: &mut Engine<T>,
    table: &mut [Sb],
    rounds: usize,
    degree: usize,
    bits: usize,
    block: impl Fn(usize, usize) -> usize,
) -> Result<MaskShare, MpcError> {
    let unit: [E; 4] = core::array::from_fn(|j| {
        let mut limbs = [F::ZERO; 4];
        limbs[j] = F::ONE;
        E::from_limbs(limbs)
    });
    let mut coef = Vec::with_capacity(rounds);
    for i in 0..rounds {
        let mut cells = vec![[Sb::ZERO; 4]; 1 << bits];
        let mut row = Vec::with_capacity(degree + 1);
        for cell in cells.iter_mut().take(degree + 1) {
            let mut c = Sh::ZERO;
            for j in 0..4 {
                cell[j] = e.random()?;
                c += cell[j].scale_ext(unit[j]);
            }
            row.push(c);
        }
        // Monomial coefficients to hypercube values, limb by limb.
        for b in 0..bits {
            for idx in 0..cells.len() {
                if (idx >> b) & 1 == 1 {
                    let lower = cells[idx ^ (1 << b)];
                    for j in 0..4 {
                        cells[idx][j] += lower[j];
                    }
                }
            }
        }
        for j in 0..4 {
            let off = block(i, j);
            for (slot, cell) in table[off..off + cells.len()].iter_mut().zip(&cells) {
                *slot = cell[j];
            }
        }
        coef.push(row);
    }
    Ok(MaskShare::new(&coef))
}

fn eval_poly(coeffs: &[Sh], x: E) -> Sh {
    coeffs
        .iter()
        .rev()
        .fold(Sh::ZERO, |acc, &c| acc.scale(x) + c)
}

/// Add the masked share of a round polynomial: `poly + rho * mask`.
fn masked(poly: &[Sh], mask: Vec<Sh>, rho: E) -> Vec<Sh> {
    mask.into_iter()
        .enumerate()
        .map(|(k, g)| g.scale(rho) + poly.get(k).copied().unwrap_or(Sh::ZERO))
        .collect()
}

struct RowOutput {
    mask_sum: E,
    rounds: Vec<Vec<E>>,
    point: Vec<E>,
    values: [E; 3],
}

/// Masked row sumcheck of `eq(tau, x) (a b - c)` on authenticated shares. Per pair of
/// rows and round: two products. The MAC check runs before every round polynomial is
/// opened, so a wrong Beaver opening is caught before anything that depends on it leaves.
fn row_sumcheck<T: Transport>(
    e: &mut Engine<T>,
    tr: &mut dregg_sig_agg::FiatShamirTranscript<dregg_sig_agg::InstanceBound>,
    tau: &[E],
    base: [Vec<Sb>; 3],
    mask: &MaskShare,
    fault: &mut dyn FnMut(Fault<'_>),
) -> Result<RowOutput, ProveError> {
    let n = tau.len();
    e.check()?;
    let mask_sum = e.open_ext(&[mask.sum()])?[0];
    tr.absorb_ext4(b"ZKHEM_ROW_MASK_SUM", mask_sum);
    let rho = NonzeroChallenge::squeeze(tr, b"ZKHEM_RHO1").get();

    let mut base = Some(base);
    let mut ext: [Vec<Sh>; 3] = core::array::from_fn(|_| Vec::new());
    let mut eq_rest = build_eq_table_ext4(&tau[1..]);
    let mut eq_bound = E::ONE;
    let mut claim = Sh::ZERO;
    let mut rounds = Vec::with_capacity(n);
    let mut point: Vec<E> = Vec::with_capacity(n);
    for &t in tau {
        let (l0, l1) = (eq_bound * (E::ONE - t), eq_bound * (t + t - E::ONE));
        if (l0 + l1).is_zero() {
            return Err(ProveError::DegenerateChallenge);
        }
        let sum_inv = (l0 + l1).inv();
        let pairs = eq_rest.len();
        let (mut h0, mut h2) = (Sh::ZERO, Sh::ZERO);
        if let Some([a, b, c]) = &base {
            let mut xs = Vec::with_capacity(2 * pairs);
            let mut ys = Vec::with_capacity(2 * pairs);
            for k in 0..pairs {
                xs.extend([a[2 * k], a[2 * k + 1] - a[2 * k]]);
                ys.extend([b[2 * k], b[2 * k + 1] - b[2 * k]]);
            }
            let products = e.mul(&xs, &ys)?;
            for k in 0..pairs {
                h0 += (products[2 * k] - c[2 * k]).scale_ext(eq_rest[k]);
                h2 += products[2 * k + 1].scale_ext(eq_rest[k]);
            }
        } else {
            let [a, b, c] = &ext;
            let mut xs = Vec::with_capacity(2 * pairs);
            let mut ys = Vec::with_capacity(2 * pairs);
            for k in 0..pairs {
                xs.extend([a[2 * k], a[2 * k + 1] - a[2 * k]]);
                ys.extend([b[2 * k], b[2 * k + 1] - b[2 * k]]);
            }
            let products = e.mul_ext(&xs, &ys)?;
            for k in 0..pairs {
                h0 += (products[2 * k] - c[2 * k]).scale(eq_rest[k]);
                h2 += products[2 * k + 1].scale(eq_rest[k]);
            }
        }
        // `p(X) = (l0 + l1 X)(h0 + h1 X + h2 X^2)` with `p(0) + p(1)` the running claim.
        let h1 = (claim - h0.scale(l0)).scale(sum_inv) - h0 - h2;
        let pending = [
            h0.scale(l0),
            h1.scale(l0) + h0.scale(l1),
            h2.scale(l0) + h1.scale(l1),
            h2.scale(l1),
        ];
        let mut share = masked(&pending, mask.round_poly(&point), rho);
        fault(Fault::RoundShare(&mut share));
        e.check()?;
        let poly = e.open_ext(&share)?;
        tr.absorb_ext4_slice(b"ZKHEM_ROW_ROUND", &poly);
        let c = tr.squeeze_ext4(b"ZKHEM_ROW_ROUND");
        claim = eval_poly(&pending, c);
        if let Some(mut tables) = base.take() {
            for (dst, src) in ext.iter_mut().zip(&mut tables) {
                *dst = src
                    .chunks_exact(2)
                    .map(|p| p[0].lift() + (p[1] - p[0]).scale_ext(c))
                    .collect();
                dregg_sig_asm::volatile_fill(src, Sb::ZERO);
            }
        } else {
            for table in &mut ext {
                let half = table.len() / 2;
                for k in 0..half {
                    table[k] = table[2 * k] + (table[2 * k + 1] - table[2 * k]).scale(c);
                }
                dregg_sig_asm::volatile_fill(&mut table[half..], Sh::ZERO);
                table.truncate(half);
            }
        }
        let tc = t * c;
        eq_bound *= E::ONE - t - c + tc + tc;
        if eq_rest.len() > 1 {
            eq_rest = eq_rest.chunks_exact(2).map(|p| p[0] + p[1]).collect();
        }
        rounds.push(poly);
        point.push(c);
    }
    e.check()?;
    let opened = e.open_ext(&[ext[0][0], ext[1][0], ext[2][0]])?;
    Ok(RowOutput {
        mask_sum,
        rounds,
        point,
        values: [opened[0], opened[1], opened[2]],
    })
}

/// Masked column sumcheck of `M(y) Z(y)` for the public `M`: linear in the shares.
fn column_sumcheck<T: Transport>(
    e: &mut Engine<T>,
    tr: &mut dregg_sig_agg::FiatShamirTranscript<dregg_sig_agg::InstanceBound>,
    mut matrix: Vec<E>,
    z: &[Sb],
    mask: &MaskShare,
) -> Result<(E, Vec<Vec<E>>), ProveError> {
    let n = matrix.len().trailing_zeros() as usize;
    e.check()?;
    let mask_sum = e.open_ext(&[mask.sum()])?[0];
    tr.absorb_ext4(b"ZKHEM_COL_MASK_SUM", mask_sum);
    let rho = NonzeroChallenge::squeeze(tr, b"ZKHEM_RHO2").get();
    let mut ext: Vec<Sh> = Vec::new();
    let mut rounds = Vec::with_capacity(n);
    let mut point: Vec<E> = Vec::with_capacity(n);
    for round in 0..n {
        let mut q = [Sh::ZERO; COL_DEGREE + 1];
        let mut add = |m: &[E], z0: Sh, z1: Sh| {
            let (dm, dz) = (m[1] - m[0], z1 - z0);
            q[0] += z0.scale(m[0]);
            q[1] += dz.scale(m[0]) + z0.scale(dm);
            q[2] += dz.scale(dm);
        };
        if round == 0 {
            for (m, p) in matrix.chunks_exact(2).zip(z.chunks_exact(2)) {
                add(m, p[0].lift(), p[1].lift());
            }
        } else {
            for (m, p) in matrix.chunks_exact(2).zip(ext.chunks_exact(2)) {
                add(m, p[0], p[1]);
            }
        }
        let share = masked(&q, mask.round_poly(&point), rho);
        e.check()?;
        let poly = e.open_ext(&share)?;
        tr.absorb_ext4_slice(b"ZKHEM_COL_ROUND", &poly);
        let c = tr.squeeze_ext4(b"ZKHEM_COL_ROUND");
        ext = if round == 0 {
            z.chunks_exact(2)
                .map(|p| p[0].lift() + (p[1] - p[0]).scale_ext(c))
                .collect()
        } else {
            ext.chunks_exact(2)
                .map(|p| p[0] + (p[1] - p[0]).scale(c))
                .collect()
        };
        matrix = matrix
            .chunks_exact(2)
            .map(|p| p[0] + c * (p[1] - p[0]))
            .collect();
        rounds.push(poly);
        point.push(c);
    }
    Ok((mask_sum, rounds))
}

/// `M(rx, y) = sum_i eq_rx[i] (r_a A + r_b B + r_c C)[i, y]` on `cells` columns.
fn column_matrix(shape: &Shape, eq_rx: &[E], combine: &[E], cells: usize) -> Vec<E> {
    let mut table = vec![E::ZERO; cells];
    for (matrix, &r) in [&shape.a, &shape.b, &shape.c].into_iter().zip(combine) {
        for (i, &weight) in eq_rx.iter().enumerate() {
            let w = r * weight;
            for (col, val) in matrix.row(i) {
                table[col] += w.mul_base(val);
            }
        }
    }
    table
}

/// A product of a shared polynomial with a public one.
fn poly_times(shared: &[Sh], public: &[E]) -> Vec<Sh> {
    let mut out = vec![Sh::ZERO; shared.len() + public.len() - 1];
    for (i, &s) in shared.iter().enumerate() {
        for (j, &p) in public.iter().enumerate() {
            out[i + j] += s.scale(p);
        }
    }
    out
}

/// What the lookup steps L1 to L3 leave for the rest of the proof.
struct LookupOutput {
    gamma: E,
    roots: Vec<CanopyCommitment>,
    state: HemWhirProverState,
    /// This custodian's authenticated shares of the helper table.
    table: Vec<Sb>,
    mask_sum: E,
    rounds: Vec<Vec<E>>,
    point: Vec<E>,
    values: [E; 3],
}

/// Lookup steps L1 to L3 on authenticated shares (module comment). `z` are the shares of
/// the variable cells.
fn lookup_front<T: Transport>(
    e: &mut Engine<T>,
    tr: &mut dregg_sig_agg::FiatShamirTranscript<dregg_sig_agg::InstanceBound>,
    lookups: &Lookups,
    ll: &LookupLayout,
    z: &[Sb],
) -> Result<LookupOutput, ProveError> {
    let d = lookups.log_entries;
    let (entries, checked) = (lookups.num_entries(), lookups.num_checked());
    let gamma = tr.squeeze_ext4(b"ZKHEM_LK_GAMMA");
    let alpha = tr.squeeze_ext4(b"ZKHEM_LK_ALPHA");
    let unit: [E; 4] = core::array::from_fn(|j| {
        let mut limbs = [F::ZERO; 4];
        limbs[j] = F::ONE;
        E::from_limbs(limbs)
    });
    let form = |matrix: &Csr, i: usize| {
        matrix
            .row(i)
            .fold(Sb::ZERO, |acc, (col, val)| acc + z[col].scale(val))
    };

    // Numerators and values of every fraction.
    let mut n: Vec<Sh> = (0..entries).map(|i| form(&lookups.num, i).lift()).collect();
    let mut v: Vec<Sh> = (0..entries)
        .map(|i| {
            lookups
                .den
                .iter()
                .rev()
                .fold(Sh::ZERO, |acc, m| acc.scale(gamma) + form(m, i).lift())
        })
        .collect();

    // Helpers. Inversions: `w = r (alpha - v)` with `r v` from base-field products of the
    // limbs of `r` with the shared tuple columns.
    let mut h = vec![Sh::ZERO; entries];
    let mut inversions: Vec<(usize, [Sb; 4])> = Vec::new();
    let (mut xs, mut ys) = (Vec::new(), Vec::new());
    for i in 0..checked {
        match helper_kind(lookups, i).ok_or(ProveError::Unsupported)? {
            Helper::Zero => {}
            Helper::PublicValue => {
                let value = lookups.den.iter().rev().fold(E::ZERO, |acc, m| {
                    acc * gamma + E::from_base(public_form(m, i).unwrap_or(F::ZERO))
                });
                if (alpha - value).is_zero() {
                    return Err(ProveError::DegenerateChallenge);
                }
                h[i] = n[i].scale((alpha - value).inv());
            }
            Helper::Inversion { .. } => {
                let r = [e.random()?, e.random()?, e.random()?, e.random()?];
                for m in &lookups.den {
                    if public_form(m, i).is_none() {
                        let column = form(m, i);
                        xs.extend(r);
                        ys.extend([column; 4]);
                    }
                }
                inversions.push((i, r));
            }
        }
    }
    let products = e.mul(&xs, &ys)?;
    let mut next = products.chunks_exact(4);
    let mut masked_values = Vec::with_capacity(inversions.len());
    let mut pads = Vec::with_capacity(inversions.len());
    for &(i, r) in &inversions {
        let pad = (0..4).fold(Sh::ZERO, |acc, j| acc + r[j].scale_ext(unit[j]));
        // `r v = sum_c gamma^c r x_c`, with public columns scaling `r` directly.
        let mut rv = Sh::ZERO;
        let mut weight = E::ONE;
        for m in &lookups.den {
            match public_form(m, i) {
                Some(constant) => rv += pad.scale(weight.mul_base(constant)),
                None => {
                    let limbs = next.next().ok_or(ProveError::Malformed)?;
                    for j in 0..4 {
                        rv += limbs[j].scale_ext(weight * unit[j]);
                    }
                }
            }
            weight *= gamma;
        }
        masked_values.push(pad.scale(alpha) - rv);
        pads.push(pad);
    }
    let opened = e.open_ext(&masked_values)?;
    for ((&(i, _), pad), w) in inversions.iter().zip(pads).zip(opened) {
        if w.is_zero() {
            return Err(ProveError::DegenerateChallenge);
        }
        let numerator = public_form(&lookups.num, i).ok_or(ProveError::Unsupported)?;
        h[i] = pad.scale(w.inv().mul_base(numerator));
    }
    for slot in &mut h[checked..] {
        *slot = e.random_ext()?;
    }

    // The helper table, its commitment and the list of helper roots.
    let cells = 1usize << ll.log_cells;
    let mut table = vec![Sb::ZERO; cells];
    for (i, value) in h.iter().enumerate() {
        for j in 0..4 {
            table[ll.limb_block(j) + i] = value.limb(j);
        }
    }
    let mask = sample_mask(e, &mut table, d, LOOKUP_DEGREE, LOOKUP_MASK_BITS, |i, j| {
        ll.mask_block(i, j)
    })?;
    for slot in &mut table[cells - ll.blind_cells..] {
        *slot = e.random()?;
    }
    let (root, state) = commit_shares(e, &table, &ll.schedule, &mut |_| {});
    let roots = exchange_roots(e, &root)?;
    tr.absorb(
        b"ZKHEM_LK_ROOT",
        &LookupRoots::Split(&roots).transcript_bytes(),
    );

    // The masked sumcheck.
    let tau: Vec<E> = (0..d).map(|_| tr.squeeze_ext4(b"ZKHEM_LK_TAU")).collect();
    let lambda = tr.squeeze_ext4(b"ZKHEM_LK_BATCH");
    e.check()?;
    let mask_sum = e.open_ext(&[mask.sum()])?[0];
    tr.absorb_ext4(b"ZKHEM_LK_MASK_SUM", mask_sum);
    let rho = NonzeroChallenge::squeeze(tr, b"ZKHEM_LK_RHO").get();
    let mut eq = build_eq_table_ext4(&tau);
    // The selector of the constrained entries: one below `count`, `boundary` at it.
    let (mut count, mut boundary) = (checked, E::ZERO);
    let mut rounds = Vec::with_capacity(d);
    let mut point: Vec<E> = Vec::with_capacity(d);
    // The running claim; the lookup sum is claimed to be zero.
    let mut claim = Sh::ZERO;
    for round in 0..d {
        let live = lookup_live_pairs(lookups, round);
        let mut xs = Vec::with_capacity(3 * live);
        let mut ys = Vec::with_capacity(3 * live);
        for k in 0..live {
            xs.extend([h[2 * k], h[2 * k + 1], h[2 * k + 1] - h[2 * k]]);
            ys.extend([v[2 * k], v[2 * k + 1], v[2 * k + 1] - v[2 * k]]);
        }
        let products = e.mul_ext(&xs, &ys)?;
        let mut pending = vec![Sh::ZERO; LOOKUP_DEGREE + 1];
        for k in 0..live {
            let [q0, q_one, q2] = [products[3 * k], products[3 * k + 1], products[3 * k + 2]];
            let (h0, dh) = (h[2 * k], h[2 * k + 1] - h[2 * k]);
            let (n0, dn) = (n[2 * k], n[2 * k + 1] - n[2 * k]);
            // `h (alpha - v) - n` on the line through the pair.
            let inner = [
                h0.scale(alpha) - q0 - n0,
                dh.scale(alpha) - (q_one - q0 - q2) - dn,
                Sh::ZERO - q2,
            ];
            let eq_line = [lambda * eq[2 * k], lambda * (eq[2 * k + 1] - eq[2 * k])];
            let mut gate = poly_times(&inner, &eq_line);
            gate[0] += h0;
            gate[1] += dh;
            let at = |j: usize| match j.cmp(&count) {
                core::cmp::Ordering::Less => E::ONE,
                core::cmp::Ordering::Equal => boundary,
                core::cmp::Ordering::Greater => E::ZERO,
            };
            let sel_line = [at(2 * k), at(2 * k + 1) - at(2 * k)];
            for (slot, term) in pending.iter_mut().zip(poly_times(&gate, &sel_line)) {
                *slot += term;
            }
        }
        // The linear coefficient is taken from the running claim, `p(0) + p(1) = claim`, as
        // the row sumcheck takes its middle coefficient. For fractions that cancel it is
        // the computed one. For fractions that do not, the opened polynomial stays masked
        // and consistent, and the defect moves to the helper table's linear claim, which
        // only the zero test sees; opening the computed one would release the sum of the
        // fractions.
        pending[1] = claim - pending[0] - pending[0] - pending[2] - pending[3] - pending[4];
        let share = masked(&pending, mask.round_poly(&point), rho);
        e.check()?;
        let poly = e.open_ext(&share)?;
        tr.absorb_ext4_slice(b"ZKHEM_LK_ROUND", &poly);
        let c = tr.squeeze_ext4(b"ZKHEM_LK_ROUND");
        claim = eval_poly(&pending, c);
        for shares in [&mut n, &mut v, &mut h] {
            let half = shares.len() / 2;
            for k in 0..half {
                shares[k] = shares[2 * k] + (shares[2 * k + 1] - shares[2 * k]).scale(c);
            }
            dregg_sig_asm::volatile_fill(&mut shares[half..], Sh::ZERO);
            shares.truncate(half);
        }
        eq = eq
            .chunks_exact(2)
            .map(|p| p[0] + c * (p[1] - p[0]))
            .collect();
        boundary = if count & 1 == 1 {
            E::ONE + c * (boundary - E::ONE)
        } else {
            boundary - c * boundary
        };
        count >>= 1;
        rounds.push(poly);
        point.push(c);
    }
    e.check()?;
    let opened = e.open_ext(&[n[0], v[0], h[0]])?;
    if !lookup_masks_full_rank(lookups, &point) {
        return Err(ProveError::MaskRankDeficient);
    }
    let values = [opened[0], opened[1], opened[2]];
    tr.absorb_ext4_slice(b"ZKHEM_LK_VALUES", &values);
    Ok(LookupOutput {
        gamma,
        roots,
        state,
        table,
        mask_sum,
        rounds,
        point,
        values,
    })
}

/// Commit to the value part of table shares and to four companion tables known to this
/// custodian only.
fn commit_shares<T: Transport>(
    e: &mut Engine<T>,
    table: &[Sb],
    schedule: &WhirSchedule,
    fault: &mut dyn FnMut(Fault<'_>),
) -> (CanopyCommitment, HemWhirProverState) {
    let mut polys: Vec<Vec<F>> = Vec::with_capacity(1 + COMPANIONS);
    polys.push(table.iter().map(|s| s.v).collect());
    fault(Fault::Table(&mut polys[0]));
    for _ in 0..COMPANIONS {
        polys.push((0..table.len()).map(|_| e.local_base()).collect());
    }
    let mut salt_seed = [0u8; 32];
    for chunk in salt_seed.chunks_mut(8) {
        chunk.copy_from_slice(&e.local_base().to_le_bytes());
    }
    let committed = whir_commit_batch_secret_with_schedule(polys, &salt_seed, schedule);
    dregg_sig_asm::volatile_fill(&mut salt_seed, 0u8);
    committed
}

/// Broadcast this custodian's root and collect every custodian's.
fn exchange_roots<T: Transport>(
    e: &mut Engine<T>,
    root: &CanopyCommitment,
) -> Result<Vec<CanopyCommitment>, ProveError> {
    let mut roots = Vec::with_capacity(e.parties());
    for (from, bytes) in e.exchange(root.to_bytes().to_vec())?.iter().enumerate() {
        let (peer_root, used) = CanopyCommitment::from_bytes_canonical(bytes)
            .ok_or(ProveError::BadPeerMessage { from })?;
        if used != bytes.len() {
            return Err(ProveError::BadPeerMessage { from });
        }
        roots.push(peer_root);
    }
    Ok(roots)
}

/// The functional `sum_t weight_t W(point_t)` on monomial coefficients (`kernel`) and on
/// hypercube values (`dual`, the transpose of the monomial transform).
fn kernel_and_dual(terms: &[WeightedPoint], log_cells: usize) -> (Vec<E>, Vec<E>) {
    let cells = 1usize << log_cells;
    let kernel = claim_kernel(terms, cells);
    let mut dual = kernel[..cells].to_vec();
    for b in 0..log_cells {
        for idx in 0..cells {
            if (idx >> b) & 1 == 0 {
                let upper = dual[idx | (1 << b)];
                dual[idx] -= upper;
            }
        }
    }
    (kernel, dual)
}

/// Steps 5 and 6 for one committed table whose linear claim has passed the zero test:
/// companion claims, the blended word, WHIR on it with every custodian's Stage-0 leaves.
#[allow(clippy::too_many_arguments)]
fn open_table<T: Transport>(
    e: &mut Engine<T>,
    tr: &mut dregg_sig_agg::FiatShamirTranscript<dregg_sig_agg::InstanceBound>,
    roots: &[CanopyCommitment],
    log_cells: usize,
    schedule: &WhirSchedule,
    state: &HemWhirProverState,
    (kernel, dual): (Vec<E>, Vec<E>),
    value: E,
    fault: &mut dyn FnMut(Fault<'_>),
) -> Result<([E; COMPANIONS], HemWhirSplitOpeningProof), ProveError> {
    let (parties, cells) = (e.parties(), 1usize << log_cells);
    let mut payload = Vec::with_capacity(32 * COMPANIONS);
    for companion in &state.hypercube_evals[1..] {
        let sigma = companion
            .iter()
            .zip(&dual)
            .fold(E::ZERO, |acc, (&c, &k)| acc + k.mul_base(c));
        payload.extend_from_slice(&sigma.to_le_bytes());
    }
    let mut companion_claims = [E::ZERO; COMPANIONS];
    for (from, bytes) in e.exchange(payload)?.iter().enumerate() {
        if bytes.len() != 32 * COMPANIONS {
            return Err(ProveError::BadPeerMessage { from });
        }
        for (claim, chunk) in companion_claims.iter_mut().zip(bytes.chunks_exact(32)) {
            *claim += chunk
                .try_into()
                .ok()
                .and_then(E::from_le_bytes_canonical)
                .ok_or(ProveError::BadPeerMessage { from })?;
        }
    }
    let (scalars, claim) = blend_claim(tr, value, &companion_claims);
    let mut payload = Vec::with_capacity(32 * cells);
    for x in 0..cells {
        let mut u = E::ZERO;
        for (evals, &s) in state.hypercube_evals.iter().zip(&scalars) {
            u += s.mul_base(evals[x]);
        }
        payload.extend_from_slice(&u.to_le_bytes());
    }
    fault(Fault::Word(&mut payload));
    let mut word = vec![E::ZERO; cells];
    for (from, bytes) in e.exchange(payload)?.iter().enumerate() {
        if bytes.len() != 32 * cells {
            return Err(ProveError::BadPeerMessage { from });
        }
        for (u, chunk) in word.iter_mut().zip(bytes.chunks_exact(32)) {
            *u += chunk
                .try_into()
                .ok()
                .and_then(E::from_le_bytes_canonical)
                .ok_or(ProveError::BadPeerMessage { from })?;
        }
    }

    // WHIR on the public word; every custodian opens its own Stage-0 leaves.
    let mut failure: Option<ProveError> = None;
    let opening = whir_open_blend_split(
        roots,
        log_cells,
        schedule,
        &scalars,
        hypercube_to_monomial_coeffs_ext4(&word),
        kernel,
        claim,
        tr,
        &mut |fibers| {
            let mut own = whir_stage0_open_share(state, fibers);
            fault(Fault::Leaves(&mut own));
            let mut all = Vec::with_capacity(parties);
            match e.exchange(encode_opening(&own)) {
                Ok(messages) => {
                    for (from, bytes) in messages.iter().enumerate() {
                        match decode_opening(bytes) {
                            Some(opening) => all.push(opening),
                            None => {
                                failure.get_or_insert(ProveError::BadPeerMessage { from });
                            }
                        }
                    }
                }
                Err(err) => {
                    failure.get_or_insert(err.into());
                }
            }
            // Keep the shape; a run with `failure` set is discarded below.
            while all.len() < parties {
                all.push(Stage0ShareOpening {
                    salts: Vec::new(),
                    vals: Vec::new(),
                    multiproof: own.multiproof.clone(),
                });
            }
            all
        },
    );
    if let Some(err) = failure {
        return Err(err);
    }
    // A custodian whose leaves do not open its own root.
    let opening = opening.map_err(|_| ProveError::Rejected)?;
    Ok((companion_claims, opening))
}

fn encode_opening(opening: &Stage0ShareOpening) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&(opening.salts.len() as u32).to_le_bytes());
    for salt in &opening.salts {
        out.extend_from_slice(salt);
    }
    out.extend_from_slice(&(opening.vals.len() as u32).to_le_bytes());
    for v in &opening.vals {
        out.extend_from_slice(&v.to_le_bytes());
    }
    opening.multiproof.push_bytes(&mut out);
    out
}

fn decode_opening(bytes: &[u8]) -> Option<Stage0ShareOpening> {
    let count = |pos: &mut usize| -> Option<usize> {
        let n = u32::from_le_bytes(bytes.get(*pos..*pos + 4)?.try_into().ok()?) as usize;
        *pos += 4;
        Some(n)
    };
    let mut pos = 0;
    let n_salts = count(&mut pos)?;
    let salts = bytes
        .get(pos..pos.checked_add(n_salts.checked_mul(16)?)?)?
        .chunks_exact(16)
        .map(|c| c.try_into().ok())
        .collect::<Option<Vec<[u8; 16]>>>()?;
    pos += 16 * n_salts;
    let n_vals = count(&mut pos)?;
    let vals = bytes
        .get(pos..pos.checked_add(n_vals.checked_mul(8)?)?)?
        .chunks_exact(8)
        .map(|c| F::from_canonical_u64(u64::from_le_bytes(c.try_into().ok()?)))
        .collect::<Option<Vec<F>>>()?;
    pos += 8 * n_vals;
    let (multiproof, used) = CanopyMultiProof::from_bytes_canonical(bytes.get(pos..)?)?;
    (pos + used == bytes.len()).then_some(Stage0ShareOpening {
        salts,
        vals,
        multiproof,
    })
}

/// Prove that the shared assignment satisfies `shape`, bound to `statement`.
///
/// `z` holds this custodian's authenticated shares of the assignment, one per variable.
/// The constant, the public inputs and the masking variables are overwritten here: the
/// first two with shares of the public values, the last with uniform values no custodian
/// knows. On `Err` no proof exists and the run must not be continued; see [`ProveError`]
/// for what each failure means.
pub fn prove_party<T: Transport>(
    e: &mut Engine<T>,
    shape: &Shape,
    public_inputs: &[F],
    statement: &[u8],
    regime: WhirSecurityRegime,
    z: Vec<Sb>,
) -> Result<ZkHemSplitProof, ProveError> {
    prove_party_with_fault(e, shape, public_inputs, statement, regime, z, &mut |_| {})
}

/// [`prove_party`] with a hook at each [`Fault`] point.
pub fn prove_party_with_fault<T: Transport>(
    e: &mut Engine<T>,
    shape: &Shape,
    public_inputs: &[F],
    statement: &[u8],
    regime: WhirSecurityRegime,
    mut z: Vec<Sb>,
    fault: &mut dyn FnMut(Fault<'_>),
) -> Result<ZkHemSplitProof, ProveError> {
    let (me, parties) = (e.me(), e.parties());
    if shape.num_sbox != 0 {
        return Err(ProveError::SboxRows);
    }
    let layout = Layout::new(shape, regime).ok_or(ProveError::Unsupported)?;
    if parties > MAX_SPLIT_COMMITTERS {
        return Err(ProveError::Unsupported);
    }
    if z.len() != shape.num_vars || public_inputs.len() != shape.num_public {
        return Err(ProveError::Malformed);
    }
    let cells = 1usize << layout.log_cells;

    // The committed table: variables, masks, blinders.
    z[0] = e.public(F::ONE);
    for (slot, &value) in z[1..].iter_mut().zip(public_inputs) {
        *slot = e.public(value);
    }
    for slot in &mut z[shape.mask_var_base..] {
        *slot = e.random()?;
    }
    let mut table = vec![Sb::ZERO; cells];
    let row_mask = sample_mask(
        e,
        &mut table,
        shape.log_rows,
        ROW_DEGREE,
        ROW_MASK_BITS,
        |i, j| layout.row_mask_block(i, j),
    )?;
    let col_mask = sample_mask(
        e,
        &mut table,
        layout.var_bits,
        COL_DEGREE,
        COL_MASK_BITS,
        |i, j| layout.col_mask_block(shape.log_rows, i, j),
    )?;
    table[..shape.num_vars].copy_from_slice(&z);
    for slot in &mut table[cells - layout.blind_cells..] {
        *slot = e.random()?;
    }
    let row_base: [Vec<Sb>; 3] = [&shape.a, &shape.b, &shape.c].map(|matrix| {
        (0..shape.num_rows())
            .map(|i| {
                matrix
                    .row(i)
                    .fold(Sb::ZERO, |acc, (col, val)| acc + z[col].scale(val))
            })
            .collect()
    });
    dregg_sig_asm::volatile_fill(&mut z, Sb::ZERO);

    let (root, state) = commit_shares(e, &table, &layout.schedule, fault);
    let roots = exchange_roots(e, &root)?;

    // Steps 1 to 3.
    let mut tr = split_transcript(shape, &layout, statement, public_inputs, &roots);
    let lookup = match (shape.lookups(), &layout.lookup) {
        (Some(lookups), Some(ll)) => Some((
            lookups,
            ll,
            lookup_front(e, &mut tr, lookups, ll, &table[..shape.num_vars])?,
        )),
        _ => None,
    };
    let tau: Vec<E> = (0..shape.log_rows)
        .map(|_| tr.squeeze_ext4(b"ZKHEM_TAU"))
        .collect();
    let row = row_sumcheck(e, &mut tr, &tau, row_base, &row_mask, fault)?;
    if !mask_rows_full_rank(shape, &row.point) {
        return Err(ProveError::MaskRankDeficient);
    }
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &row.values);
    let combine: Vec<E> = (0..if lookup.is_some() { 5 } else { 3 })
        .map(|_| tr.squeeze_ext4(b"ZKHEM_COMBINE"))
        .collect();
    let mut matrix = column_matrix(
        shape,
        &build_eq_table_ext4(&row.point),
        &combine[..3],
        1 << layout.var_bits,
    );
    if let Some((lookups, _, out)) = &lookup {
        lookup_column_add(
            &mut matrix,
            lookups,
            &build_eq_table_ext4(&out.point),
            [combine[3], combine[4]],
            out.gamma,
        );
    }
    let (col_mask_sum, col_rounds) = column_sumcheck(
        e,
        &mut tr,
        matrix,
        &table[..1 << layout.var_bits],
        &col_mask,
    )?;

    // Step 4, by the verifier's own replay of the messages sent so far.
    let mut tr = split_transcript(shape, &layout, statement, public_inputs, &roots);
    let front = replay_front(
        shape,
        &layout,
        public_inputs,
        &mut tr,
        &FrontMessages {
            row_mask_sum: row.mask_sum,
            row_rounds: &row.rounds,
            row_values: row.values,
            col_mask_sum,
            col_rounds: &col_rounds,
            lookup: lookup.as_ref().map(|(_, _, out)| LookupMessages {
                roots: LookupRoots::Split(&out.roots),
                mask_sum: out.mask_sum,
                rounds: &out.rounds,
                values: out.values,
            }),
        },
    )
    .ok_or(ProveError::Rejected)?;
    let (kernel, dual) = kernel_and_dual(&front.terms, layout.log_cells);
    let helper = match (&lookup, &front.lookup) {
        (Some((_, ll, out)), Some(claim)) => Some((
            *ll,
            out,
            kernel_and_dual(&claim.terms, ll.log_cells),
            claim.value,
        )),
        (None, None) => None,
        _ => return Err(ProveError::Rejected),
    };

    // The linear claims must hold on the authenticated tables before anything that depends
    // on them is opened: `rho * (<Z, K> - V)` for a uniform shared `rho` is zero or uniform.
    let gap_of = |e: &Engine<T>, table: &[Sb], dual: &[E], value: E| {
        table
            .iter()
            .zip(dual)
            .fold(Sh::ZERO, |acc, (s, &k)| acc + s.scale_ext(k))
            - e.public_ext(value)
    };
    let mut gaps = vec![gap_of(e, &table, &dual, front.value)];
    if let Some((_, out, (_, helper_dual), value)) = &helper {
        gaps.push(gap_of(e, &out.table, helper_dual, *value));
    }
    let mut blinds = Vec::with_capacity(gaps.len());
    for _ in &gaps {
        blinds.push(e.random_ext()?);
    }
    let test = e.mul_ext(&gaps, &blinds)?;
    e.check()?;
    let verdict = e.open_ext(&test)?;
    e.check()?;
    if verdict.iter().any(|v| !v.is_zero()) {
        return Err(ProveError::Unsatisfied);
    }
    dregg_sig_asm::volatile_fill(&mut table, Sb::ZERO);

    // Steps 5 and 6, for the assignment table and then for the helper table.
    let (companion_claims, opening) = open_table(
        e,
        &mut tr,
        &roots,
        layout.log_cells,
        &layout.schedule,
        &state,
        (kernel, dual),
        front.value,
        fault,
    )?;
    let lookup_proof = match helper {
        None => None,
        Some((ll, out, functional, value)) => {
            let (companion_claims, opening) = open_table(
                e,
                &mut tr,
                &out.roots,
                ll.log_cells,
                &ll.schedule,
                &out.state,
                functional,
                value,
                fault,
            )?;
            Some(SplitLookupProof {
                roots: out.roots.clone(),
                mask_sum: out.mask_sum,
                rounds: out.rounds.clone(),
                values: out.values,
                companion_claims,
                opening,
            })
        }
    };
    debug_assert_eq!(me, e.me());
    let proof = ZkHemSplitProof {
        roots,
        row_mask_sum: row.mask_sum,
        row_rounds: row.rounds,
        row_values: row.values,
        col_mask_sum,
        col_rounds,
        companion_claims,
        opening,
        lookup: lookup_proof,
    };
    if !verify_split(shape, public_inputs, statement, regime, &proof) {
        return Err(ProveError::Rejected);
    }
    Ok(proof)
}

#[cfg(test)]
pub(super) mod tests {
    use super::super::engine::tests::run_parties;
    use super::super::engine::{Dealer, Stats};
    use super::*;
    use dregg_sig_agg::zk_hem::relation::{ConstraintSystem, Lc};

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    /// `x * y = 35`, a cube and a Boolean: multiplication rows only.
    pub(in super::super) fn small_relation(x: u64) -> (Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        let p = cs.public_input(f(35));
        let xv: Lc = cs.alloc(f(x)).into();
        let y: Lc = cs.alloc(f(7)).into();
        let prod = cs.mul(&xv, &y);
        cs.enforce_equal(&prod.into(), &p.into());
        let sq = cs.mul(&xv, &xv);
        let cube = cs.mul(&sq.into(), &xv);
        cs.enforce_zero(Lc::from(cube).plus_const(F::ZERO - f(125)));
        let bit: Lc = cs.alloc(f(1)).into();
        cs.enforce_boolean(&bit);
        cs.finish()
    }

    /// Deal authenticated shares of `assignment` and the preprocessing, then run every
    /// custodian. `tamper` may alter a custodian's shares before it starts.
    pub(in super::super) fn threshold_prove(
        shape: &Shape,
        assignment: &[F],
        statement: &[u8],
        parties: usize,
        seed: u8,
        tamper: impl Fn(usize, &mut Vec<Sb>) + Sync,
        fault: impl Fn(usize, Fault<'_>) + Sync,
    ) -> Vec<(Result<ZkHemSplitProof, ProveError>, Stats)> {
        let regime = WhirSecurityRegime::default();
        let mut dealer = Dealer::new(parties, &[seed; 32]);
        let mut shares: Vec<Vec<Sb>> = (0..parties)
            .map(|_| Vec::with_capacity(assignment.len()))
            .collect();
        for &value in assignment {
            for (p, s) in dealer.share(value).into_iter().enumerate() {
                shares[p].push(s);
            }
        }
        let (triples, randoms) = prover_demand(shape, regime).unwrap();
        let preps = dealer.preprocessing(triples, randoms);
        let publics = assignment[1..=shape.num_public].to_vec();
        run_parties(preps, |mut e| {
            let mut z = shares[e.me()].clone();
            tamper(e.me(), &mut z);
            let me = e.me();
            let result = prove_party_with_fault(
                &mut e,
                shape,
                &publics,
                statement,
                regime,
                z,
                &mut |point| fault(me, point),
            );
            if result.is_ok() {
                assert_eq!(e.remaining(), (0, 0), "demand is exact");
                assert!(!e.has_pending());
            }
            (result, e.stats)
        })
    }

    #[test]
    fn a_quorum_proves_and_the_split_verifier_accepts() {
        let regime = WhirSecurityRegime::default();
        let (shape, assignment) = small_relation(5);
        let publics = assignment[1..=shape.num_public].to_vec();
        for parties in [2usize, 3, 5] {
            let out = threshold_prove(
                &shape,
                &assignment,
                b"stmt",
                parties,
                1,
                |_, _| {},
                |_, _| {},
            );
            let proof = out[0].0.clone().unwrap();
            assert!(out.iter().all(|(p, _)| p.as_ref() == Ok(&proof)));
            assert_eq!(proof.roots.len(), parties);
            assert!(verify_split(&shape, &publics, b"stmt", regime, &proof));
            assert!(!verify_split(&shape, &publics, b"other", regime, &proof));
            assert!(!verify_split(&shape, &[f(36)], b"stmt", regime, &proof));

            let bytes = proof.to_bytes();
            assert_eq!(
                ZkHemSplitProof::from_bytes(&bytes, &shape, regime).as_ref(),
                Some(&proof)
            );
            assert!(
                ZkHemSplitProof::from_bytes(&bytes[..bytes.len() - 1], &shape, regime).is_none()
            );
            let mut swapped = proof.clone();
            swapped.roots.swap(0, 1);
            assert!(!verify_split(&shape, &publics, b"stmt", regime, &swapped));
            let mut wrong = proof.clone();
            wrong.row_values[0] += E::ONE;
            assert!(!verify_split(&shape, &publics, b"stmt", regime, &wrong));
        }
    }

    /// Range-checked bytes, a two-column table lookup and one multiplication row.
    fn lookup_relation(x: [u64; 3], square: u64) -> (Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        let p = cs.public_input(f(35));
        let squares: Vec<F> = (0..8u64).flat_map(|t| [f(t), f(t * t)]).collect();
        let table = cs.table(2, squares);
        let vars: Vec<Lc> = x.iter().map(|&v| cs.alloc(f(v)).into()).collect();
        for v in &vars {
            cs.enforce_byte(v);
        }
        cs.enforce_byte(&vars[0].plus(&vars[2]));
        let sq: Lc = cs.alloc(f(square)).into();
        cs.enforce_in_table(table, &[vars[0].clone(), sq]);
        let prod = cs.mul(&vars[0], &vars[1]);
        cs.enforce_equal(&prod.into(), &p.into());
        cs.finish()
    }

    #[test]
    fn a_quorum_proves_a_relation_with_lookups() {
        let regime = WhirSecurityRegime::default();
        let (shape, assignment) = lookup_relation([5, 7, 250], 25);
        assert!(shape.is_satisfied(&assignment));
        let publics = assignment[1..=shape.num_public].to_vec();
        for parties in [2usize, 3] {
            let out = threshold_prove(
                &shape,
                &assignment,
                b"stmt",
                parties,
                3,
                |_, _| {},
                |_, _| {},
            );
            let proof = out[0].0.clone().unwrap();
            assert!(out.iter().all(|(p, _)| p.as_ref() == Ok(&proof)));
            let lookup = proof.lookup.as_ref().unwrap();
            assert_eq!(lookup.roots.len(), parties);
            assert!(verify_split(&shape, &publics, b"stmt", regime, &proof));
            assert!(!verify_split(&shape, &publics, b"other", regime, &proof));

            let bytes = proof.to_bytes();
            assert_eq!(
                ZkHemSplitProof::from_bytes(&bytes, &shape, regime).as_ref(),
                Some(&proof)
            );
            assert!(
                ZkHemSplitProof::from_bytes(&bytes[..bytes.len() - 1], &shape, regime).is_none()
            );
            // Every part of the lookup proof is bound.
            type Mutation = fn(&mut SplitLookupProof);
            let mutations: [Mutation; 9] = [
                |l| l.roots.swap(0, 1),
                |l| l.roots[0].root[0] ^= 1,
                |l| l.mask_sum += E::ONE,
                |l| l.rounds[1][3] += E::ONE,
                |l| l.values[0] += E::ONE,
                |l| l.values[1] += E::ONE,
                |l| l.values[2] += E::ONE,
                |l| l.companion_claims[2] += E::ONE,
                |l| l.opening.shares[1].vals[0] += F::ONE,
            ];
            for (k, mutate) in mutations.iter().enumerate() {
                let mut bad = proof.clone();
                mutate(bad.lookup.as_mut().unwrap());
                assert!(
                    !verify_split(&shape, &publics, b"stmt", regime, &bad),
                    "mutation {k} accepted"
                );
            }
            let mut stripped = proof.clone();
            stripped.lookup = None;
            assert!(!verify_split(&shape, &publics, b"stmt", regime, &stripped));
        }
    }

    /// A looked-up value outside its table, a tuple that is not a table row and a wrong
    /// multiplicity each stop at the zero test: the rows hold, only the helper claim fails.
    #[test]
    fn a_failed_lookup_aborts_at_the_zero_test() {
        let (shape, good) = lookup_relation([5, 7, 250], 25);
        let mut wrong_count = good.clone();
        wrong_count[shape.lookups().unwrap().mult_var_base + 30] += F::ONE;
        let cases = [
            lookup_relation([5, 7, 251], 25).1,
            lookup_relation([5, 7, 250], 24).1,
            wrong_count,
        ];
        for (k, bad) in cases.iter().enumerate() {
            assert!(!shape.is_satisfied(bad), "case {k}");
            let out = threshold_prove(&shape, bad, b"stmt", 3, 4, |_, _| {}, |_, _| {});
            for (result, _) in &out {
                assert_eq!(
                    result.as_ref().err(),
                    Some(&ProveError::Unsatisfied),
                    "case {k}"
                );
            }
        }
        // Same number of rounds and of consumed material as an accepted run up to the
        // abort: the failing run stops before the companion claims.
        let ok = threshold_prove(&shape, &good, b"stmt", 3, 4, |_, _| {}, |_, _| {});
        let bad = threshold_prove(&shape, &cases[0], b"stmt", 3, 4, |_, _| {}, |_, _| {});
        assert_eq!(ok[0].1.triples_used, bad[0].1.triples_used);
        assert!(bad[0].1.rounds < ok[0].1.rounds);
    }

    /// A custodian that commits to a helper table other than its shares makes every
    /// custodian reject the assembled proof.
    #[test]
    fn a_wrong_helper_table_is_rejected_by_every_custodian() {
        let (shape, assignment) = lookup_relation([5, 7, 250], 25);
        // The second blended word a custodian sends is the helper table's.
        let words_sent = core::sync::atomic::AtomicUsize::new(0);
        let out = threshold_prove(
            &shape,
            &assignment,
            b"stmt",
            3,
            5,
            |_, _| {},
            |me, point| {
                if let (1, Fault::Word(word)) = (me, point)
                    && words_sent.fetch_add(1, core::sync::atomic::Ordering::Relaxed) == 1
                {
                    word[0] ^= 1;
                }
            },
        );
        for (result, _) in &out {
            assert_eq!(result.as_ref().err(), Some(&ProveError::Rejected));
        }
    }

    /// A shared assignment that does not satisfy the relation stops at the zero test in
    /// every custodian, before the companion claims or the blended word are sent.
    #[test]
    fn an_unsatisfying_assignment_aborts_at_the_zero_test() {
        let (shape, _) = small_relation(5);
        let (_, bad) = small_relation(6);
        let out = threshold_prove(&shape, &bad, b"stmt", 3, 2, |_, _| {}, |_, _| {});
        for (result, _) in &out {
            assert_eq!(result.as_ref().err(), Some(&ProveError::Unsatisfied));
        }
    }

    /// Rounds, material and checks of a run. The byte count is left out: the size of a
    /// Stage-0 multiproof depends on which fibers the transcript selects.
    fn pattern(stats: Stats) -> (u64, u64, u64, u64) {
        (
            stats.rounds,
            stats.triples_used,
            stats.randoms_used,
            stats.mac_checks,
        )
    }

    /// `x * y = 35` with a free Boolean: two witnesses for one statement.
    fn two_witness_relation(bit: u64) -> (Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        let p = cs.public_input(f(35));
        let x: Lc = cs.alloc(f(if bit == 0 { 5 } else { 7 })).into();
        let y: Lc = cs.alloc(f(if bit == 0 { 7 } else { 5 })).into();
        let prod = cs.mul(&x, &y);
        cs.enforce_equal(&prod.into(), &p.into());
        let b: Lc = cs.alloc(f(bit)).into();
        cs.enforce_boolean(&b);
        cs.finish()
    }

    /// A malicious custodian (party 2 of 3) deviates in one place. Every honest
    /// custodian aborts, at the same point and with the same error whichever of two
    /// witnesses of the same statement is shared, after the same number of rounds, MAC
    /// checks and consumed material.
    #[test]
    fn a_deviating_custodian_makes_every_honest_custodian_abort() {
        use super::super::engine::MpcError;
        #[derive(Clone, Copy, Debug, PartialEq)]
        enum Attack {
            Table,
            RoundShare,
            Word,
            Leaf,
            MacShare,
            ValueShare,
        }
        let expected = |attack: Attack| match attack {
            Attack::Table | Attack::Word | Attack::Leaf => ProveError::Rejected,
            _ => ProveError::Mpc(MpcError::MacCheck),
        };
        for attack in [
            Attack::Table,
            Attack::RoundShare,
            Attack::Word,
            Attack::Leaf,
            Attack::MacShare,
            Attack::ValueShare,
        ] {
            let mut traces = Vec::new();
            for bit in [0u64, 1] {
                let (shape, assignment) = two_witness_relation(bit);
                let secret = shape.num_public + 1;
                let out = threshold_prove(
                    &shape,
                    &assignment,
                    b"stmt",
                    3,
                    7,
                    |me, z| match attack {
                        Attack::MacShare if me == 2 => z[secret].m[0] += F::ONE,
                        Attack::ValueShare if me == 2 => z[secret].v += F::ONE,
                        _ => {}
                    },
                    |me, point| {
                        if me != 2 {
                            return;
                        }
                        match (attack, point) {
                            (Attack::Table, Fault::Table(table)) => table[secret] += F::ONE,
                            (Attack::RoundShare, Fault::RoundShare(share)) => share[1].v += E::ONE,
                            (Attack::Word, Fault::Word(bytes)) => bytes[64] ^= 1,
                            (Attack::Leaf, Fault::Leaves(leaves)) => leaves.vals[0] += F::ONE,
                            _ => {}
                        }
                    },
                );
                for (result, _) in &out[..2] {
                    assert_eq!(result.as_ref().err(), Some(&expected(attack)), "{attack:?}");
                }
                traces.push([pattern(out[0].1), pattern(out[1].1)]);
            }
            assert_eq!(traces[0], traces[1], "{attack:?}");
        }
    }

    /// Without a deviation both witnesses give accepted proofs with the same message
    /// pattern, and the two proofs differ (the masks do not repeat).
    #[test]
    fn two_witnesses_of_one_statement_give_the_same_message_pattern() {
        let regime = WhirSecurityRegime::default();
        let runs: Vec<_> = [0u64, 1]
            .into_iter()
            .map(|bit| {
                let (shape, assignment) = two_witness_relation(bit);
                let out = threshold_prove(&shape, &assignment, b"stmt", 3, 7, |_, _| {}, |_, _| {});
                let proof = out[0].0.clone().unwrap();
                assert!(verify_split(&shape, &[f(35)], b"stmt", regime, &proof));
                (proof, pattern(out[0].1))
            })
            .collect();
        assert_eq!(runs[0].1, runs[1].1);
        assert_ne!(runs[0].0, runs[1].0);
    }

    /// Threshold proofs of real ownership statements with dealer preprocessing.
    /// `cargo test --release -p dregg-sig-migrate --features std --lib --
    /// hem::collab::prover::tests::measure_threshold_ownership --ignored --nocapture`
    #[test]
    #[ignore = "measurement"]
    fn measure_threshold_ownership() {
        use super::super::verify_threshold_ownership;
        use crate::hem::relations::{
            KeySource, Lock, OwnershipStatement, OwnershipWitness, ownership_transcript,
            synthesize_ownership,
        };
        let regime = WhirSecurityRegime::default();
        let cases = [
            (
                "bitcoin-hash160",
                Lock::P2pkh,
                KeySource::Secp256k1Key,
                OwnershipWitness::secp256k1_key(&[0x11; 32]),
                3usize,
            ),
            (
                "ed25519-seed",
                Lock::Ed25519,
                KeySource::Ed25519Seed,
                OwnershipWitness::ed25519_seed(&[0x22; 32]),
                3,
            ),
            (
                "bitcoin-hash160",
                Lock::P2pkh,
                KeySource::Secp256k1Key,
                OwnershipWitness::secp256k1_key(&[0x11; 32]),
                5,
            ),
        ];
        let only = std::env::var("COLLAB_MEASURE_ONLY").ok();
        for (name, lock, source, witness, parties) in &cases {
            let label = std::format!("{name} N={parties}");
            if only.as_ref().is_some_and(|o| !label.contains(o.as_str())) {
                continue;
            }
            let st = OwnershipStatement::derive(*lock, source.clone(), witness, [5; 32], [6; 32], 9).unwrap();
            let (shape, assignment) = synthesize_ownership(&st, witness).unwrap();
            let (triples, randoms) = prover_demand(&shape, regime).unwrap();
            let layout = Layout::new(&shape, regime).unwrap();
            let t = std::time::Instant::now();
            let out = threshold_prove(
                &shape,
                &assignment,
                &ownership_transcript(&st, regime),
                *parties,
                3,
                |_, _| {},
                |_, _| {},
            );
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
            let stats = out[0].1;
            std::println!(
                "{label}: rows=2^{} vars={} cells=2^{} triples/party={triples} randoms/party={randoms} \
                 sent/party={} bytes rounds={} mac_checks={} proof={} bytes \
                 deal+prove wall={total_s:.1}s verify={verify_s:.2}s",
                shape.log_rows,
                shape.num_vars,
                layout.log_cells,
                stats.bytes_sent,
                stats.rounds,
                stats.mac_checks,
                bytes.len(),
            );
            assert_eq!(stats.triples_used as usize, triples);
            assert_eq!(stats.randoms_used as usize, randoms);
        }
    }
}
