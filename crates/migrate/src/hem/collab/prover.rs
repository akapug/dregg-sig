//! One custodian's side of the collaborative zk-Hem prover.
//!
//! The steps, what each opens and why each opening is safe are in the module comment of
//! [`super`]. Every custodian runs [`prove_party`] with its authenticated shares of the
//! assignment and ends with the same [`ZkHemSplitProof`], which it has verified.

use alloc::vec;
use alloc::vec::Vec;

use dregg_sig_agg::field::{Goldilocks, GoldilocksExt4, GoldilocksOps as _, build_eq_table_ext4};
use dregg_sig_agg::pcs::{
    CanopyCommitment, CanopyMultiProof, Stage0ShareOpening, WhirSecurityRegime,
    hypercube_to_monomial_coeffs_ext4, whir_commit_batch_secret_with_schedule,
    whir_open_blend_split, whir_stage0_open_share,
};
use dregg_sig_agg::zk_hem::protocol::{
    COL_DEGREE, COL_MASK_BITS, COMPANIONS, FrontMessages, Layout, MAX_SPLIT_COMMITTERS, ROW_DEGREE,
    ROW_MASK_BITS, ZkHemSplitProof, blend_claim, claim_kernel, mask_rows_full_rank, replay_front,
    split_transcript, verify_split,
};
use dregg_sig_agg::zk_hem::relation::Shape;
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
fn column_matrix(shape: &Shape, eq_rx: &[E], combine: &[E; 3], cells: usize) -> Vec<E> {
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

    // Commit to the value shares and to four companion tables known to this custodian only.
    let mut polys: Vec<Vec<F>> = Vec::with_capacity(1 + COMPANIONS);
    polys.push(table.iter().map(|s| s.v).collect());
    fault(Fault::Table(&mut polys[0]));
    for _ in 0..COMPANIONS {
        polys.push((0..cells).map(|_| e.local_base()).collect());
    }
    let mut salt_seed = [0u8; 32];
    for chunk in salt_seed.chunks_mut(8) {
        chunk.copy_from_slice(&e.local_base().to_le_bytes());
    }
    let (root, state) = whir_commit_batch_secret_with_schedule(polys, &salt_seed, &layout.schedule);
    dregg_sig_asm::volatile_fill(&mut salt_seed, 0u8);
    let mut roots = Vec::with_capacity(parties);
    for (from, bytes) in e.exchange(root.to_bytes().to_vec())?.iter().enumerate() {
        let (peer_root, used) = CanopyCommitment::from_bytes_canonical(bytes)
            .ok_or(ProveError::BadPeerMessage { from })?;
        if used != bytes.len() {
            return Err(ProveError::BadPeerMessage { from });
        }
        roots.push(peer_root);
    }

    // Steps 1 to 3.
    let mut tr = split_transcript(shape, &layout, statement, public_inputs, &roots);
    let tau: Vec<E> = (0..shape.log_rows)
        .map(|_| tr.squeeze_ext4(b"ZKHEM_TAU"))
        .collect();
    let row = row_sumcheck(e, &mut tr, &tau, row_base, &row_mask, fault)?;
    if !mask_rows_full_rank(shape, &row.point) {
        return Err(ProveError::MaskRankDeficient);
    }
    tr.absorb_ext4_slice(b"ZKHEM_ROW_VALUES", &row.values);
    let combine: [E; 3] = core::array::from_fn(|_| tr.squeeze_ext4(b"ZKHEM_COMBINE"));
    let matrix = column_matrix(
        shape,
        &build_eq_table_ext4(&row.point),
        &combine,
        1 << layout.var_bits,
    );
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
        },
    )
    .ok_or(ProveError::Rejected)?;
    let kernel = claim_kernel(&front.terms, cells);
    // The same functional on hypercube values: the transpose of the monomial transform.
    let mut dual = kernel[..cells].to_vec();
    for b in 0..layout.log_cells {
        for idx in 0..cells {
            if (idx >> b) & 1 == 0 {
                let upper = dual[idx | (1 << b)];
                dual[idx] -= upper;
            }
        }
    }

    // The linear claim must hold on the authenticated table before anything that depends
    // on it is opened: `rho * (<Z, K> - V)` for a uniform shared `rho` is zero or uniform.
    let gap = table
        .iter()
        .zip(&dual)
        .fold(Sh::ZERO, |acc, (s, &k)| acc + s.scale_ext(k))
        - e.public_ext(front.value);
    let blind = e.random_ext()?;
    let test = e.mul_ext(&[gap], &[blind])?;
    e.check()?;
    let verdict = e.open_ext(&test)?[0];
    e.check()?;
    if !verdict.is_zero() {
        return Err(ProveError::Unsatisfied);
    }
    dregg_sig_asm::volatile_fill(&mut table, Sb::ZERO);

    // Step 5: companion claims, then the blended word.
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
    let (scalars, claim) = blend_claim(&mut tr, front.value, &companion_claims);
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

    // Step 6: WHIR on the public word; every custodian opens its own Stage-0 leaves.
    let mut failure: Option<ProveError> = None;
    let opening = whir_open_blend_split(
        &roots,
        layout.log_cells,
        &layout.schedule,
        &scalars,
        hypercube_to_monomial_coeffs_ext4(&word),
        kernel,
        claim,
        &mut tr,
        &mut |fibers| {
            let mut own = whir_stage0_open_share(&state, fibers);
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

    /// Test helper that holds the assignment in the clear: deal authenticated shares of
    /// it and the preprocessing, then run every custodian. The path without a clear
    /// assignment is `super::super::prove_ownership_party`. `tamper` may alter a custodian's shares before it starts.
    pub(in super::super) fn deal_clear_assignment_and_prove(
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
            let out = deal_clear_assignment_and_prove(
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

    /// A shared assignment that does not satisfy the relation stops at the zero test in
    /// every custodian, before the companion claims or the blended word are sent.
    #[test]
    fn an_unsatisfying_assignment_aborts_at_the_zero_test() {
        let (shape, _) = small_relation(5);
        let (_, bad) = small_relation(6);
        let out =
            deal_clear_assignment_and_prove(&shape, &bad, b"stmt", 3, 2, |_, _| {}, |_, _| {});
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
                let out = deal_clear_assignment_and_prove(
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
                let out = deal_clear_assignment_and_prove(
                    &shape,
                    &assignment,
                    b"stmt",
                    3,
                    7,
                    |_, _| {},
                    |_, _| {},
                );
                let proof = out[0].0.clone().unwrap();
                assert!(verify_split(&shape, &[f(35)], b"stmt", regime, &proof));
                (proof, pattern(out[0].1))
            })
            .collect();
        assert_eq!(runs[0].1, runs[1].1);
        assert_ne!(runs[0].0, runs[1].0);
    }
}
