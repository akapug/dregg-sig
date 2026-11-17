//! Relations proved by the committed zk-Hem protocol in [`super::protocol`].
//!
//! A relation is a list of rows over one assignment vector `z` (`z[0] = 1`):
//!
//! * S-box rows `<a, z>^7 = <c, z>`,
//! * multiplication rows `<a, z> * <b, z> = <c, z>`.
//!
//! S-box rows come first, so the row selector is a prefix indicator the verifier evaluates
//! in `O(log rows)`. Public values enter as constants of the linear forms, so they are part
//! of the [`Shape`] and of its digest. Twelve masking rows over twelve masking variables are
//! appended by [`ConstraintSystem::finish`]; the prover fills those variables with fresh
//! uniform values (see [`MASK_ROWS`]).
//!
//! # Definitions
//!
//! A prover that holds the witness in shares cannot run a gadget's native arithmetic. A
//! builder made by [`ConstraintSystem::new_recording`] therefore keeps, for every
//! variable, how its value follows from earlier variables ([`Def`]); gadgets state it
//! with [`ConstraintSystem::alloc_defined`]. A variable from plain
//! [`ConstraintSystem::alloc`] is [`Def::Undefined`], and
//! [`Definitions::undefined`] lists those: a relation is usable by a threshold prover
//! only when that list is empty. Recording changes neither the rows nor the assignment.
//!
//! # Lookups
//!
//! A relation may also say that a tuple of linear forms is a row of a public table:
//!
//! * [`ConstraintSystem::enforce_byte`]: a linear form takes a value in `[0, 2^8)`, as a
//!   field element (no reduction modulo anything but the Goldilocks prime). Other ranges
//!   are compositions: a limb `v` of `w < 8` bits is `enforce_byte(v)` and
//!   `enforce_byte(2^(8 - w) v)`; a `16`-bit value is `lo + 2^8 hi` with both limbs
//!   checked.
//! * [`ConstraintSystem::table`] and [`ConstraintSystem::enforce_in_table`]:
//!   `(lc_1, .., lc_k)` is a row of a fixed table with `k` columns
//!   ([`ConstraintSystem::range_table`] is the one-column table `0..2^bits`).
//!
//! This is the interface asked for in the module comment of `dregg-sig-migrate`'s
//! `hem/curve.rs` ("Wanted from the constraint system").
//!
//! A lookup adds no row and no variable of its own. Per table row the relation gains one
//! variable, the number of lookups that hit that row (its multiplicity), which
//! [`ConstraintSystem::finish`] allocates and assigns. The lookups live in [`Lookups`], a
//! second public structure of the [`Shape`] bound into its digest: a list of *fractions*
//! `n_i / (alpha - v_i)` whose numerators and value tuples are linear forms of the
//! assignment,
//!
//! * `1 / (alpha - (t, lc_1, .., lc_k))` for a lookup into table `t`,
//! * `-m_r / (alpha - (t, row_r))` for row `r` of table `t` with multiplicity variable `m_r`,
//!
//! and the statement is that the fractions sum to zero as rational functions of `alpha`:
//! for every tuple value, the numerators of the fractions with that value sum to zero
//! ([`Lookups::holds`]). Over a field of characteristic larger than the number of lookups
//! this holds exactly when every looked-up tuple is a table row and every multiplicity is
//! the true count (`logup-2022-1530`, Lemma 5, which is stated for one column; the tuple
//! form with a table tag is the batching of its Section 3.4). How the protocol proves it,
//! and what that costs in soundness and in committed cells, is in [`super::protocol`].
//!
//! A relation without lookups has `Shape::lookups() == None`, the digest it had before
//! lookups existed, and the same proofs.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec;
use alloc::vec::Vec;

use crate::field::{Goldilocks, GoldilocksOps as _};
use crate::sponge::{
    POSEIDON2_HALF_EXT_ROUNDS, POSEIDON2_INT_ROUNDS, cshake256_static_midstate, keccak_f1600,
    poseidon2_apply_me, poseidon2_apply_mi, poseidon2_const_at, poseidon2_perm12, poseidon2_sbox7,
};

type F = Goldilocks;

/// Index into the assignment vector. `Var::ONE` is the constant `1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var(u32);

impl Var {
    pub const ONE: Var = Var(0);

    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Linear form over the assignment: terms sorted by variable, no zero coefficients.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Lc(Vec<(u32, F)>);

impl Lc {
    #[inline]
    pub fn zero() -> Self {
        Self(Vec::new())
    }

    #[inline]
    pub fn constant(c: F) -> Self {
        Self::term(Var::ONE, c)
    }

    #[inline]
    pub fn term(v: Var, coeff: F) -> Self {
        if coeff.is_zero() {
            Self::zero()
        } else {
            Self(vec![(v.0, coeff)])
        }
    }

    #[inline]
    pub fn terms(&self) -> &[(u32, F)] {
        &self.0
    }

    /// `sum_i scale_i * lc_i`.
    pub fn combine(parts: &[(F, &Lc)]) -> Self {
        let mut all: Vec<(u32, F)> = Vec::with_capacity(parts.iter().map(|(_, l)| l.0.len()).sum());
        for &(scale, lc) in parts {
            if !scale.is_zero() {
                all.extend(lc.0.iter().map(|&(v, c)| (v, c.const_mul(scale))));
            }
        }
        all.sort_unstable_by_key(|&(v, _)| v);
        let mut out: Vec<(u32, F)> = Vec::with_capacity(all.len());
        for (v, c) in all {
            match out.last_mut() {
                Some(last) if last.0 == v => last.1 += c,
                _ => out.push((v, c)),
            }
        }
        out.retain(|&(_, c)| !c.is_zero());
        Self(out)
    }

    pub fn plus(&self, rhs: &Lc) -> Self {
        let (a, b) = (&self.0, &rhs.0);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() && j < b.len() {
            if a[i].0 < b[j].0 {
                out.push(a[i]);
                i += 1;
            } else if a[i].0 > b[j].0 {
                out.push(b[j]);
                j += 1;
            } else {
                let c = a[i].1 + b[j].1;
                if !c.is_zero() {
                    out.push((a[i].0, c));
                }
                i += 1;
                j += 1;
            }
        }
        out.extend_from_slice(&a[i..]);
        out.extend_from_slice(&b[j..]);
        Self(out)
    }

    pub fn scaled(&self, k: F) -> Self {
        if k.is_zero() {
            return Self::zero();
        }
        Self(self.0.iter().map(|&(v, c)| (v, c.const_mul(k))).collect())
    }

    #[inline]
    pub fn minus(&self, rhs: &Lc) -> Self {
        self.plus(&rhs.scaled(F::ZERO - F::ONE))
    }

    #[inline]
    pub fn plus_const(&self, c: F) -> Self {
        self.plus(&Lc::constant(c))
    }
}

impl From<Var> for Lc {
    #[inline]
    fn from(v: Var) -> Self {
        Lc::term(v, F::ONE)
    }
}

/// Sparse matrix in compressed-row form.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Csr {
    ptr: Vec<u32>,
    col: Vec<u32>,
    val: Vec<F>,
}

impl Csr {
    fn new() -> Self {
        Self {
            ptr: vec![0],
            col: Vec::new(),
            val: Vec::new(),
        }
    }

    fn push_row(&mut self, lc: &Lc) {
        for &(v, c) in lc.terms() {
            self.col.push(v);
            self.val.push(c);
        }
        self.ptr.push(self.col.len() as u32);
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        self.ptr.len() - 1
    }

    #[inline]
    pub fn nnz(&self) -> usize {
        self.col.len()
    }

    /// `(column, coefficient)` pairs of row `i`.
    #[inline]
    pub fn row(&self, i: usize) -> impl Iterator<Item = (usize, F)> + '_ {
        let (lo, hi) = (self.ptr[i] as usize, self.ptr[i + 1] as usize);
        self.col[lo..hi]
            .iter()
            .zip(&self.val[lo..hi])
            .map(|(&c, &v)| (c as usize, v))
    }

    #[inline]
    pub fn row_dot(&self, i: usize, z: &[F]) -> F {
        self.row(i)
            .fold(F::ZERO, |acc, (c, v)| acc + v.const_mul(z[c]))
    }

    fn stream_into(&self, mut push: impl FnMut(&[u8])) {
        push(&(self.ptr.len() as u64).to_le_bytes());
        for &p in &self.ptr {
            push(&p.to_le_bytes());
        }
        for (&c, &v) in self.col.iter().zip(&self.val) {
            push(&c.to_le_bytes());
            push(&v.to_le_bytes());
        }
    }
}

/// Number of masking rows (and masking variables) appended to every relation.
///
/// With `p1, p2, p3` three groups of four masking variables, the rows are
/// `p1_k * 1 = p1_k`, `1 * p2_k = p2_k` and `p3_k * 2 = 2 p3_k`. Each group sits on one
/// two-variable corner of the row hypercube. At a sumcheck point `rx` the groups add
/// `(k1 e1 + k3 e3, k2 e2, k1 e1 + k2 e2 + 2 k3 e3)` to `(Az, Bz, Cz)(rx)`, where `e_g` is
/// the corner-weighted sum of group `g` and `k_g` its common weight. That map has
/// determinant `k1 k2 k3`, so when the corner weights have full base-field rank and the
/// `k_g` are nonzero, the three revealed values are uniform and independent of the rest of
/// the assignment.
pub const MASK_ROWS: usize = 12;

// ============================================================================
// Definitions of variables
// ============================================================================

/// Index of a [`Source`] in [`Definitions::sources`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceId(u32);

impl SourceId {
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// One coefficient of an integer written in base `2^8`: a linear form whose value under
/// any satisfying assignment is an integer in `[lo, hi]` (taken modulo the field prime to
/// its representative of least absolute value).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntCoef {
    pub lc: Lc,
    pub lo: i128,
    pub hi: i128,
}

/// A value several variables are read from. Integers `sum_k c_k 2^(8k)` are given by
/// their coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Source {
    /// Supplied from outside the relation (a secret the prover is given) as an integer
    /// of `bits` bits.
    Input { bits: u32 },
    /// The coefficients of the product of two polynomials given by their coefficients.
    PolyProduct { a: Vec<Lc>, b: Vec<Lc> },
    /// The canonical value of a linear form, which lies in `[0, 2^bits)`.
    Form { lc: Lc, bits: u32 },
    /// The integer `sum_j a_j b_j + c`, which lies in `[0, 2^bits)`; each `(a_j, b_j)`
    /// is a pair of integers multiplied as polynomials.
    Integer {
        products: Vec<(Vec<IntCoef>, Vec<IntCoef>)>,
        linear: Vec<IntCoef>,
        bits: u32,
    },
    /// The canonical residue of `(sum_j a_j b_j + c) / den` modulo the prime `modulus`
    /// (little-endian bytes). An empty `den` is one. A denominator that is zero modulo
    /// the prime has no value.
    Residue {
        products: Vec<(Vec<IntCoef>, Vec<IntCoef>)>,
        linear: Vec<IntCoef>,
        den: Vec<IntCoef>,
        modulus: Vec<u8>,
    },
    /// The slope of an affine addition that may be a doubling, as a canonical residue
    /// modulo the prime `modulus`: `num / den` where `den` is not zero modulo the prime
    /// (the chord), and `(sum_j a_j b_j + c) / tangent_den` where it is (the tangent).
    /// The gadget guarantees that `tangent_den` is not zero in that case.
    Slope {
        num: Vec<IntCoef>,
        den: Vec<IntCoef>,
        tangent_products: Vec<(Vec<IntCoef>, Vec<IntCoef>)>,
        tangent_linear: Vec<IntCoef>,
        tangent_den: Vec<IntCoef>,
        modulus: Vec<u8>,
    },
    /// The integer `num / divisor`, where the odd `divisor` (little-endian bytes) divides
    /// `num` exactly and the quotient lies in `[0, 2^bits)`.
    Quotient {
        num: Vec<IntCoef>,
        divisor: Vec<u8>,
        bits: u32,
    },
}

/// How the value of a variable follows from earlier variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Def {
    /// Allocated without a definition.
    Undefined,
    /// The constant one.
    One,
    /// A public input.
    Public,
    /// A masking variable appended by [`ConstraintSystem::finish`].
    Mask,
    /// `a b`.
    Product(Lc, Lc),
    /// `a^7`.
    Power7(Lc),
    /// `base + sum_j a_j b_j`.
    SumOfProducts { base: Lc, products: Vec<(Lc, Lc)> },
    /// `scale (num / den - minus)` in the field. The gadget guarantees `den != 0`.
    Ratio {
        num: Lc,
        den: Lc,
        minus: Lc,
        scale: F,
    },
    /// The inverse of `of`, or zero when `of` is zero; `of` lies in `[0, max]`.
    InverseOrZero { of: Lc, max: u32 },
    /// Coefficient `index` of a [`Source::PolyProduct`].
    Coefficient { product: SourceId, index: u32 },
    /// Bits `lo..lo + width` of an integer source, as one value.
    Bits {
        source: SourceId,
        lo: u32,
        width: u32,
    },
}

/// The definitions recorded by a [`ConstraintSystem::new_recording`] builder: one
/// [`Def`] per variable of the finished shape.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Definitions {
    pub vars: Vec<Def>,
    pub sources: Vec<Source>,
}

impl Definitions {
    /// Variables allocated without a definition.
    pub fn undefined(&self) -> Vec<usize> {
        (0..self.vars.len())
            .filter(|&i| self.vars[i] == Def::Undefined)
            .collect()
    }
}

/// Masking entries at the top of the fraction list of a relation with lookups, and half the
/// number of masking variables they use: entry `k` has a free numerator variable and a free
/// value variable (first tuple column), both uniform, and is not constrained. They make the
/// three values the lookup sumcheck reveals uniform, as the masking rows do for the row
/// values.
pub const LOOKUP_MASK_ENTRIES: usize = 4;

/// Handle of a public table registered with [`ConstraintSystem::table`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TableId(u32);

/// The lookups of a relation as a list of `2^log_entries` fractions (module comment).
/// Entry `i` has numerator `<num[i], z>` and the value tuple `(<den[c][i], z>)_c`; column
/// `0` is the table tag. Entries `0..num_checked()` are constrained; the last
/// [`LOOKUP_MASK_ENTRIES`] are masking entries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lookups {
    pub log_entries: usize,
    /// Lookups (entries `0..num_lookups`).
    pub num_lookups: usize,
    /// Table rows over all tables (entries `num_lookups..num_lookups + num_table_rows`).
    pub num_table_rows: usize,
    /// First multiplicity variable; one per table row, in entry order.
    pub mult_var_base: usize,
    pub num: Csr,
    pub den: Vec<Csr>,
}

impl Lookups {
    #[inline]
    pub fn num_entries(&self) -> usize {
        1usize << self.log_entries
    }

    /// Entries below this index are constrained and summed.
    #[inline]
    pub fn num_checked(&self) -> usize {
        self.num_entries() - LOOKUP_MASK_ENTRIES
    }

    /// Columns of a value tuple, the table tag included.
    #[inline]
    pub fn width(&self) -> usize {
        self.den.len()
    }

    /// Whether the fractions of `z` sum to zero as rational functions: for every tuple
    /// value the numerators add up to zero. Not constant time in `z`.
    pub fn holds(&self, z: &[F]) -> bool {
        let mut sums: BTreeMap<Vec<u64>, F> = BTreeMap::new();
        for i in 0..self.num_checked() {
            let n = self.num.row_dot(i, z);
            if n.is_zero() {
                continue;
            }
            let key: Vec<u64> = self
                .den
                .iter()
                .map(|m| m.row_dot(i, z).to_canonical_u64())
                .collect();
            *sums.entry(key).or_insert(F::ZERO) += n;
        }
        sums.values().all(|s| s.is_zero())
    }

    fn stream_into(&self, mut push: impl FnMut(&[u8])) {
        push(b"QSAG.ZKHEM.SHAPE.LOOKUP/v1");
        for n in [
            self.log_entries,
            self.num_lookups,
            self.num_table_rows,
            self.mult_var_base,
            self.den.len(),
        ] {
            push(&(n as u64).to_le_bytes());
        }
        self.num.stream_into(&mut push);
        for m in &self.den {
            m.stream_into(&mut push);
        }
    }
}

struct LookupTable {
    width: usize,
    /// Row-major canonical values.
    rows: Vec<u64>,
    /// How many lookups hit each row. Witness-dependent.
    mult: Vec<u64>,
}

/// Tag marking a variable allocated inside the 128-stride Poseidon2 S-box arena of a
/// hologram-aligned [`ConstraintSystem`].
const P2_VAR_TAG: u32 = 1u32 << 31;

/// Alignment metadata enabling $O(\log P)$ closed-form evaluation of the 106 interior S-box rows
/// (`rows 12..118`) of every aligned width-12 Poseidon2 permutation in a [`Shape`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HologramMeta {
    /// Number of 128-row / 128-var aligned Poseidon2 permutations at row prefix `[0..128*P)`.
    /// Zero for shapes built via [`ConstraintSystem::new`].
    pub poseidon2_perms: usize,
    /// Number of 128-variable blocks reserved for `[1, public_inputs...]` before the aligned
    /// Poseidon2 variable arena `[128 * pub_var_blocks .. 128 * (pub_var_blocks + P))`.
    pub pub_var_blocks: usize,
}

/// Public structure of a relation: row matrices over `num_vars` variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shape {
    /// `log2` of the padded row count.
    pub log_rows: usize,
    /// Rows `0..num_sbox` are S-box rows; all others are multiplication rows.
    pub num_sbox: usize,
    /// Variables, including the constant and the masking variables.
    pub num_vars: usize,
    /// Variables `1..=num_public` are public inputs: the verifier supplies their values and
    /// the protocol checks the committed cells against them.
    pub num_public: usize,
    /// First of the [`MASK_ROWS`] masking variables.
    pub mask_var_base: usize,
    pub a: Csr,
    pub b: Csr,
    pub c: Csr,
    hologram_meta: HologramMeta,
    lookups: Option<Lookups>,
    digest: [u8; 32],
}

impl Shape {
    /// The lookups of the relation; `None` when it has none.
    #[inline]
    pub fn lookups(&self) -> Option<&Lookups> {
        self.lookups.as_ref()
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        1usize << self.log_rows
    }

    /// First row of masking group `g in 0..3`.
    #[inline]
    pub fn mask_row_base(&self, g: usize) -> usize {
        self.num_rows() - 4 * (3 - g)
    }

    /// Binding digest of the whole relation, public constants included. Computed once by
    /// [`ConstraintSystem::finish`].
    #[inline]
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// Block-alignment metadata for Spark hologram factorization (`poseidon2_perms == 0` when
    /// constructed via [`ConstraintSystem::new`]).
    #[inline]
    pub fn hologram_meta(&self) -> HologramMeta {
        self.hologram_meta
    }

    /// Whether row `i` belongs to the residual sparse hologram (excluding the 106 universal
    /// interior S-box rows `12..118` and 10 zero padding rows `118..128` of aligned Poseidon2
    /// blocks, which are evaluated in $O(\log P)$ closed form).
    #[inline]
    pub fn is_residual_row(&self, row: usize) -> bool {
        let p = self.hologram_meta.poseidon2_perms;
        if p > 0 && row < 128 * p {
            (row & 127) < 12
        } else {
            true
        }
    }

    fn compute_digest(&self) -> [u8; 32] {
        const SHAPE_MIDSTATE: [u64; 25] = cshake256_static_midstate(b"QSAG.ZKHEM.SHAPE/v1");
        const RATE: usize = 136;

        let mut state = SHAPE_MIDSTATE;
        let mut buf = [0u8; RATE];
        let mut filled = 0usize;
        let xor_rate = |st: &mut [u64; 25], blk: &[u8; RATE]| {
            for (lane, chunk) in st.iter_mut().take(17).zip(blk.as_chunks::<8>().0) {
                *lane ^= u64::from_le_bytes(*chunk);
            }
        };
        let mut push = |mut data: &[u8]| {
            while !data.is_empty() {
                let take = (RATE - filled).min(data.len());
                buf[filled..filled + take].copy_from_slice(&data[..take]);
                filled += take;
                data = &data[take..];
                if filled == RATE {
                    xor_rate(&mut state, &buf);
                    keccak_f1600(&mut state);
                    filled = 0;
                }
            }
        };
        for n in [
            self.log_rows,
            self.num_sbox,
            self.num_vars,
            self.num_public,
            self.mask_var_base,
        ] {
            push(&(n as u64).to_le_bytes());
        }
        self.a.stream_into(&mut push);
        self.b.stream_into(&mut push);
        self.c.stream_into(&mut push);
        if let Some(lookups) = &self.lookups {
            lookups.stream_into(&mut push);
        }

        buf[filled..].fill(0);
        buf[filled] ^= 0x04;
        buf[RATE - 1] ^= 0x80;
        xor_rate(&mut state, &buf);
        keccak_f1600(&mut state);
        let mut out = [0u8; 32];
        for (lane, dst) in state.iter().take(4).zip(out.as_chunks_mut::<8>().0) {
            *dst = lane.to_le_bytes();
        }
        out
    }

    /// Whether `z` (with `z[0] = 1`) satisfies every row.
    pub fn is_satisfied(&self, z: &[F]) -> bool {
        z.len() == self.num_vars
            && z[0] == F::ONE
            && (0..self.num_rows()).all(|i| {
                let a = self.a.row_dot(i, z);
                let c = self.c.row_dot(i, z);
                if i < self.num_sbox {
                    poseidon2_sbox7(a) == c
                } else {
                    a.const_mul(self.b.row_dot(i, z)) == c
                }
            })
            && self.lookups.as_ref().is_none_or(|l| l.holds(z))
    }
}

/// Relation builder that carries an assignment alongside the rows.
///
/// The row structure must not depend on assigned values: the verifier rebuilds the [`Shape`]
/// by running the same synthesis on a placeholder assignment.
pub struct ConstraintSystem {
    values: Vec<F>,
    record_rows: bool,
    num_public: usize,
    hologram_aligned: bool,
    p2_perms: usize,
    p2_values: Vec<F>,
    p2_sbox: Vec<(Lc, Lc)>,
    sbox: Vec<(Lc, Lc)>,
    mul: Vec<(Lc, Lc, Lc)>,
    defs: Option<Definitions>,
    tables: Vec<LookupTable>,
    range_tables: Vec<(usize, TableId)>,
    lookups: Vec<(u32, Vec<Lc>)>,
    num_lookups: usize,
}

impl Default for ConstraintSystem {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstraintSystem {
    pub fn new() -> Self {
        Self {
            values: vec![F::ONE],
            record_rows: true,
            num_public: 0,
            hologram_aligned: false,
            p2_perms: 0,
            p2_values: Vec::new(),
            p2_sbox: Vec::new(),
            sbox: Vec::new(),
            mul: Vec::new(),
            defs: None,
            tables: Vec::new(),
            range_tables: Vec::new(),
            lookups: Vec::new(),
            num_lookups: 0,
        }
    }

    /// A builder that records a [`Def`] for every variable; close it with
    /// [`Self::finish_recorded`].
    pub fn new_recording() -> Self {
        let mut cs = Self::new();
        cs.defs = Some(Definitions {
            vars: vec![Def::One],
            sources: Vec::new(),
        });
        cs
    }

    /// Whether definitions are recorded.
    #[inline]
    pub fn is_recording(&self) -> bool {
        self.defs.is_some()
    }

    /// Register a [`Source`]. `make` runs only when recording; otherwise the returned
    /// index is a placeholder.
    pub fn source(&mut self, make: impl FnOnce() -> Source) -> SourceId {
        match &mut self.defs {
            Some(defs) => {
                defs.sources.push(make());
                SourceId(defs.sources.len() as u32 - 1)
            }
            None => SourceId(u32::MAX),
        }
    }

    /// Allocate a variable with the given assigned value and its definition. `def` runs
    /// only when recording.
    pub fn alloc_defined(&mut self, value: F, def: impl FnOnce() -> Def) -> Var {
        let var = self.alloc(value);
        if let Some(defs) = &mut self.defs {
            *defs.vars.last_mut().expect("just allocated") = def();
        }
        var
    }

    /// [`Self::finish`] with the recorded definitions.
    pub fn finish_recorded(mut self) -> (Shape, Vec<F>, Definitions) {
        assert!(
            !self.hologram_aligned,
            "recording a hologram-aligned relation"
        );
        // A multiplicity is a count over the whole witness, not a function of earlier
        // variables; no definition kind states it.
        assert!(self.num_lookups == 0, "recording a relation with lookups");
        let mut defs = self.defs.take().expect("a recording builder");
        let (shape, z) = self.finish();
        defs.vars.resize(shape.num_vars, Def::Mask);
        (shape, z, defs)
    }

    /// Relation builder that places [`poseidon2_perm`] S-box rows and S-box output variables on
    /// 128-row / 128-variable boundaries so [`super::protocol::ShapeHologram`] evaluates 90%+ of
    /// Poseidon2 matrix entries in $O(\log P)$ closed form.
    pub fn new_hologram_aligned() -> Self {
        let mut cs = Self::new();
        cs.hologram_aligned = true;
        cs
    }

    /// Re-evaluate a compiled relation's assignment without rebuilding its matrices.
    /// The resulting assignment must still be checked against the compiled shape.
    pub(crate) fn witness_only() -> Self {
        let mut cs = Self::new();
        cs.record_rows = false;
        cs
    }

    pub(crate) fn finish_assignment(mut self, shape: &Shape) -> Option<Vec<F>> {
        assert!(!self.record_rows && !self.hologram_aligned);
        self.push_multiplicities();
        if self.num_public != shape.num_public || self.values.len() != shape.mask_var_base {
            return None;
        }
        let masks = shape.num_vars - self.values.len();
        dregg_sig_core::wipe::secret_vec_reserve(&mut self.values, masks);
        self.values.resize(shape.num_vars, F::ZERO);
        Some(core::mem::take(&mut self.values))
    }

    pub(crate) fn fork_public_inputs(&self) -> Self {
        assert_eq!(self.values.len(), self.num_public + 1);
        assert!(self.p2_values.is_empty());
        assert!(self.defs.is_none(), "a recording builder is not forked");
        Self {
            values: self.values.clone(),
            record_rows: self.record_rows,
            num_public: self.num_public,
            hologram_aligned: self.hologram_aligned,
            p2_perms: 0,
            p2_values: Vec::new(),
            p2_sbox: Vec::new(),
            sbox: Vec::new(),
            mul: Vec::new(),
            defs: None,
            tables: self
                .tables
                .iter()
                .map(|t| LookupTable {
                    width: t.width,
                    rows: t.rows.clone(),
                    mult: vec![0; t.mult.len()],
                })
                .collect(),
            range_tables: self.range_tables.clone(),
            lookups: Vec::new(),
            num_lookups: 0,
        }
    }

    /// Append a disjoint circuit with the same public prefix, relocating private
    /// variables. Preserves the serial allocation/row order for canonical shapes.
    pub(crate) fn append(&mut self, mut other: Self) {
        assert_eq!(self.num_public, other.num_public);
        assert_eq!(self.record_rows, other.record_rows);
        assert_eq!(self.hologram_aligned, other.hologram_aligned);
        assert_eq!(
            &self.values[..=self.num_public],
            &other.values[..=other.num_public]
        );
        let offset = u32::try_from(self.values.len() - self.num_public - 1)
            .expect("relation variable limit");
        let p2_offset = u32::try_from(self.p2_values.len()).expect("poseidon2 variable limit");
        let relocate = |mut lc: Lc| {
            for (v, _) in &mut lc.0 {
                if *v & P2_VAR_TAG != 0 {
                    let raw = (*v & !P2_VAR_TAG)
                        .checked_add(p2_offset)
                        .expect("poseidon2 variable limit");
                    assert!(raw < P2_VAR_TAG, "poseidon2 variable limit");
                    *v = P2_VAR_TAG | raw;
                } else if *v as usize > self.num_public {
                    let next = v.checked_add(offset).expect("relation variable limit");
                    assert!(next < P2_VAR_TAG, "relation variable limit");
                    *v = next;
                }
            }
            lc
        };
        self.p2_sbox.extend(
            core::mem::take(&mut other.p2_sbox)
                .into_iter()
                .map(|(a, c)| (relocate(a), relocate(c))),
        );
        self.sbox.extend(
            core::mem::take(&mut other.sbox)
                .into_iter()
                .map(|(a, c)| (relocate(a), relocate(c))),
        );
        self.mul.extend(
            core::mem::take(&mut other.mul)
                .into_iter()
                .map(|(a, b, c)| (relocate(a), relocate(b), relocate(c))),
        );
        assert_eq!(
            self.tables.len(),
            other.tables.len(),
            "lookup tables are registered before a fork"
        );
        self.lookups.extend(
            core::mem::take(&mut other.lookups)
                .into_iter()
                .map(|(t, tuple)| (t, tuple.into_iter().map(relocate).collect())),
        );
        self.num_lookups += other.num_lookups;
        for (mine, theirs) in self.tables.iter_mut().zip(&mut other.tables) {
            for (m, o) in mine.mult.iter_mut().zip(&theirs.mult) {
                *m += o;
            }
            dregg_sig_asm::volatile_fill(&mut theirs.mult, 0u64);
        }
        self.p2_perms += other.p2_perms;
        dregg_sig_core::wipe::secret_vec_extend_from_slice(&mut self.p2_values, &other.p2_values);
        dregg_sig_asm::volatile_fill(&mut other.p2_values, F::ZERO);
        dregg_sig_core::wipe::secret_vec_extend_from_slice(
            &mut self.values,
            &other.values[self.num_public + 1..],
        );
    }

    /// Allocate a public input. All public inputs must be allocated before any other
    /// variable, so that they occupy variables `1..=num_public`.
    pub fn public_input(&mut self, value: F) -> Var {
        assert_eq!(
            self.values.len(),
            1 + self.num_public,
            "public inputs are allocated first"
        );
        assert!(
            self.p2_values.is_empty(),
            "public inputs are allocated first"
        );
        self.num_public += 1;
        self.alloc_defined(value, || Def::Public)
    }

    /// Allocate a free variable with the given assigned value.
    pub fn alloc(&mut self, value: F) -> Var {
        // Hiding callers allocate witness values here: growth erases the old storage.
        dregg_sig_core::wipe::secret_vec_push(&mut self.values, value);
        let idx = self.values.len() - 1;
        assert!(idx < P2_VAR_TAG as usize, "relation variable limit");
        if let Some(defs) = &mut self.defs {
            defs.vars.push(Def::Undefined);
        }
        Var(idx as u32)
    }

    pub fn eval(&self, lc: &Lc) -> F {
        lc.terms().iter().fold(F::ZERO, |acc, &(v, c)| {
            let val = if v & P2_VAR_TAG != 0 {
                self.p2_values[(v & !P2_VAR_TAG) as usize]
            } else {
                self.values[v as usize]
            };
            acc + c.const_mul(val)
        })
    }

    /// Fresh variable `y` with the row `a^7 = y`.
    pub fn sbox7(&mut self, a: &Lc) -> Var {
        let y = self.alloc_defined(poseidon2_sbox7(self.eval(a)), || Def::Power7(a.clone()));
        if self.record_rows {
            self.sbox.push((a.clone(), y.into()));
        }
        y
    }

    fn p2_sbox7(&mut self, a: &Lc) -> Var {
        if !self.hologram_aligned {
            return self.sbox7(a);
        }
        let val = poseidon2_sbox7(self.eval(a));
        dregg_sig_core::wipe::secret_vec_push(&mut self.p2_values, val);
        let idx = self.p2_values.len() - 1;
        assert!(idx < P2_VAR_TAG as usize, "poseidon2 variable limit");
        let y = Var(P2_VAR_TAG | (idx as u32));
        if self.record_rows {
            self.p2_sbox.push((a.clone(), y.into()));
        }
        y
    }

    fn finish_p2_perm_block(&mut self) {
        if !self.hologram_aligned {
            return;
        }
        for _ in 0..10 {
            dregg_sig_core::wipe::secret_vec_push(&mut self.p2_values, F::ZERO);
            if self.record_rows {
                self.p2_sbox.push((Lc::zero(), Lc::zero()));
            }
        }
        self.p2_perms += 1;
        debug_assert_eq!(self.p2_values.len(), 128 * self.p2_perms);
    }

    /// Fresh variable `y` with the row `a * b = y`.
    pub fn mul(&mut self, a: &Lc, b: &Lc) -> Var {
        let y = self.alloc_defined(self.eval(a).const_mul(self.eval(b)), || {
            Def::Product(a.clone(), b.clone())
        });
        if self.record_rows {
            self.mul.push((a.clone(), b.clone(), y.into()));
        }
        y
    }

    pub fn enforce_mul(&mut self, a: Lc, b: Lc, c: Lc) {
        if self.record_rows {
            self.mul.push((a, b, c));
        }
    }

    /// Row `lc * 1 = 0`.
    pub fn enforce_zero(&mut self, lc: Lc) {
        if self.record_rows {
            self.mul.push((lc, Lc::constant(F::ONE), Lc::zero()));
        }
    }

    pub fn enforce_equal(&mut self, a: &Lc, b: &Lc) {
        self.enforce_zero(a.minus(b));
    }

    /// Row `v * (1 - v) = 0`.
    pub fn enforce_boolean(&mut self, v: &Lc) {
        if self.record_rows {
            self.mul
                .push((v.clone(), Lc::constant(F::ONE).minus(v), Lc::zero()));
        }
    }

    /// `if bit { on_one } else { on_zero }`, one multiplication row. `bit` must be
    /// constrained Boolean by the caller.
    pub fn select(&mut self, bit: &Lc, on_one: &Lc, on_zero: &Lc) -> Lc {
        let delta = self.mul(bit, &on_one.minus(on_zero));
        on_zero.plus(&delta.into())
    }

    /// Register a public table of `rows.len() / width` distinct rows of `width` columns
    /// (row-major). Tables are part of the relation: register them in a fixed order.
    pub fn table(&mut self, width: usize, rows: Vec<F>) -> TableId {
        assert!(
            !self.hologram_aligned,
            "lookups are not supported in hologram-aligned relations"
        );
        assert!(width >= 1 && !rows.is_empty() && rows.len().is_multiple_of(width));
        let rows: Vec<u64> = rows.iter().map(|v| v.to_canonical_u64()).collect();
        let distinct: BTreeSet<&[u64]> = rows.chunks(width).collect();
        assert_eq!(
            distinct.len(),
            rows.len() / width,
            "table rows are distinct"
        );
        let id = u32::try_from(self.tables.len()).expect("lookup table limit");
        self.tables.push(LookupTable {
            width,
            mult: vec![0; rows.len() / width],
            rows,
        });
        TableId(id)
    }

    /// The one-column table `0..2^bits`, registered on first use.
    pub fn range_table(&mut self, bits: usize) -> TableId {
        if let Some(&(_, id)) = self.range_tables.iter().find(|(b, _)| *b == bits) {
            return id;
        }
        assert!((1..=16).contains(&bits), "range table of 1 to 16 bits");
        let rows: Vec<F> = (0..1u64 << bits).map(F::from_u64_reduced).collect();
        let id = self.table(1, rows);
        self.range_tables.push((bits, id));
        id
    }

    /// `(values_1, .., values_k)` is a row of `table`. No row and no variable is added; the
    /// table's multiplicity variables are allocated by [`Self::finish`].
    ///
    /// The multiplicity count scans the whole table with a fixed access pattern.
    pub fn enforce_in_table(&mut self, table: TableId, values: &[Lc]) {
        let mut tuple: Vec<u64> = values
            .iter()
            .map(|lc| self.eval(lc).to_canonical_u64())
            .collect();
        let t = &mut self.tables[table.0 as usize];
        assert_eq!(values.len(), t.width, "lookup tuple width");
        for (row, count) in t.rows.chunks(t.width).zip(&mut t.mult) {
            let diff = row.iter().zip(&tuple).fold(0u64, |d, (a, b)| d | (a ^ b));
            *count += ((diff | diff.wrapping_neg()) >> 63) ^ 1;
        }
        dregg_sig_asm::volatile_fill(&mut tuple, 0u64);
        self.num_lookups += 1;
        if self.record_rows {
            self.lookups.push((table.0, values.to_vec()));
        }
    }

    /// `0 <= value < 256` for the field element `value` itself: a lookup into
    /// [`Self::range_table`]`(8)`.
    pub fn enforce_byte(&mut self, value: &Lc) {
        let table = self.range_table(8);
        self.enforce_in_table(table, core::slice::from_ref(value));
    }

    /// How many lookups the relation holds (the cost metric beside [`Self::num_rows`]).
    #[inline]
    pub fn num_lookups(&self) -> usize {
        self.num_lookups
    }

    /// Allocate one variable per table row holding its multiplicity; returns the first.
    fn push_multiplicities(&mut self) -> usize {
        let base = self.values.len();
        for t in 0..self.tables.len() {
            for r in 0..self.tables[t].mult.len() {
                let count = F::from_u64_reduced(self.tables[t].mult[r]);
                self.alloc(count);
            }
        }
        base
    }

    /// The fraction list of the recorded lookups, with masking variables from `mask_base`.
    fn take_lookups(&mut self, mult_var_base: usize, mask_base: usize) -> Lookups {
        let lookups = core::mem::take(&mut self.lookups);
        let num_table_rows: usize = self.tables.iter().map(|t| t.mult.len()).sum();
        let width = 1 + self.tables.iter().map(|t| t.width).max().unwrap_or(0);
        let used = lookups.len() + num_table_rows;
        let log_entries = (used + LOOKUP_MASK_ENTRIES)
            .next_power_of_two()
            .trailing_zeros()
            .max(2) as usize;
        let empty = Lc::zero();
        let mut num = Csr::new();
        let mut den: Vec<Csr> = (0..width).map(|_| Csr::new()).collect();
        let tag = |t: usize| Lc::constant(F::from_u64_reduced(t as u64));
        for (t, tuple) in &lookups {
            num.push_row(&Lc::constant(F::ONE));
            den[0].push_row(&tag(*t as usize));
            for (c, col) in den[1..].iter_mut().enumerate() {
                col.push_row(tuple.get(c).unwrap_or(&empty));
            }
        }
        let mut var = mult_var_base;
        for (t, table) in self.tables.iter().enumerate() {
            for row in table.rows.chunks(table.width) {
                num.push_row(&Lc::term(Var(var as u32), F::ZERO - F::ONE));
                var += 1;
                den[0].push_row(&tag(t));
                for (c, col) in den[1..].iter_mut().enumerate() {
                    let cell = row.get(c).map_or(F::ZERO, |&v| F::from_u64_reduced(v));
                    col.push_row(&Lc::constant(cell));
                }
            }
        }
        let total = 1usize << log_entries;
        for _ in used..total - LOOKUP_MASK_ENTRIES {
            num.push_row(&empty);
            den.iter_mut().for_each(|col| col.push_row(&empty));
        }
        for k in 0..LOOKUP_MASK_ENTRIES {
            num.push_row(&Lc::term(Var((mask_base + k) as u32), F::ONE));
            den[0].push_row(&Lc::term(
                Var((mask_base + LOOKUP_MASK_ENTRIES + k) as u32),
                F::ONE,
            ));
            den[1..].iter_mut().for_each(|col| col.push_row(&empty));
        }
        Lookups {
            log_entries,
            num_lookups: lookups.len(),
            num_table_rows,
            mult_var_base,
            num,
            den,
        }
    }

    #[inline]
    pub fn num_rows(&self) -> usize {
        self.p2_sbox.len() + self.sbox.len() + self.mul.len()
    }

    /// Close the relation: append the masking variables and rows, pad the row count to a
    /// power of two. Returns the shape and the assignment, whose masking variables are zero
    /// until the prover overwrites them.
    pub fn finish(mut self) -> (Shape, Vec<F>) {
        assert!(self.record_rows);
        let one = Lc::constant(F::ONE);
        let two = Lc::constant(F::TWO);
        let empty = Lc::zero();

        if !self.hologram_aligned {
            let mult_var_base = self.push_multiplicities();
            let mask_var_base = self.values.len();
            let mask: Vec<Var> = (0..MASK_ROWS).map(|_| self.alloc(F::ZERO)).collect();
            // The masking variables of the fraction list follow the row masks, so the
            // prover's fill of `mask_var_base..` covers both.
            let lookups = (!self.tables.is_empty()).then(|| {
                for _ in 0..2 * LOOKUP_MASK_ENTRIES {
                    self.alloc(F::ZERO);
                }
                self.take_lookups(mult_var_base, mask_var_base + MASK_ROWS)
            });
            let used = self.num_rows();
            let log_rows = (used + MASK_ROWS)
                .next_power_of_two()
                .trailing_zeros()
                .max(4) as usize;
            let total = 1usize << log_rows;

            let num_sbox = self.sbox.len();
            let sbox = core::mem::take(&mut self.sbox);
            let mul = core::mem::take(&mut self.mul);
            let (mut a, mut b, mut c) = (Csr::new(), Csr::new(), Csr::new());
            for (ra, rc) in sbox {
                a.push_row(&ra);
                b.push_row(&empty);
                c.push_row(&rc);
            }
            for (ra, rb, rc) in mul {
                a.push_row(&ra);
                b.push_row(&rb);
                c.push_row(&rc);
            }
            for _ in used..total - MASK_ROWS {
                a.push_row(&empty);
                b.push_row(&empty);
                c.push_row(&empty);
            }
            for (k, &p) in mask.iter().enumerate() {
                let p: Lc = p.into();
                match k / 4 {
                    0 => {
                        a.push_row(&p);
                        b.push_row(&one);
                        c.push_row(&p);
                    }
                    1 => {
                        a.push_row(&one);
                        b.push_row(&p);
                        c.push_row(&p);
                    }
                    _ => {
                        a.push_row(&p);
                        b.push_row(&two);
                        c.push_row(&p.scaled(F::TWO));
                    }
                }
            }
            let z = core::mem::take(&mut self.values);
            let mut shape = Shape {
                log_rows,
                num_sbox,
                num_vars: z.len(),
                num_public: self.num_public,
                mask_var_base,
                a,
                b,
                c,
                hologram_meta: HologramMeta::default(),
                lookups,
                digest: [0; 32],
            };
            shape.digest = shape.compute_digest();
            return (shape, z);
        }

        let pub_prefix = 1 + self.num_public;
        let pub_var_blocks = pub_prefix.div_ceil(128);
        let p2_var_base = 128 * pub_var_blocks;
        let misc_var_base = p2_var_base + self.p2_values.len();
        let misc_len = self.values.len() - pub_prefix;
        let mask_var_base = misc_var_base + misc_len;
        let num_vars = mask_var_base + MASK_ROWS;

        let remap_var = |v: u32| -> u32 {
            if v & P2_VAR_TAG != 0 {
                (p2_var_base as u32) + (v & !P2_VAR_TAG)
            } else if (v as usize) < pub_prefix {
                v
            } else {
                (misc_var_base as u32) + (v - (pub_prefix as u32))
            }
        };
        let remap_lc = |lc: Lc| -> Lc {
            let mut terms: Vec<(u32, F)> =
                lc.0.into_iter()
                    .map(|(v, coeff)| (remap_var(v), coeff))
                    .collect();
            terms.sort_unstable_by_key(|&(v, _)| v);
            Lc(terms)
        };

        let used = self.num_rows();
        let num_sbox = self.p2_sbox.len() + self.sbox.len();
        let log_rows = (used + MASK_ROWS)
            .next_power_of_two()
            .trailing_zeros()
            .max(4) as usize;
        let total = 1usize << log_rows;

        let p2_sbox = core::mem::take(&mut self.p2_sbox);
        let sbox = core::mem::take(&mut self.sbox);
        let mul = core::mem::take(&mut self.mul);
        let (mut a, mut b, mut c) = (Csr::new(), Csr::new(), Csr::new());
        for (ra, rc) in p2_sbox.into_iter().chain(sbox) {
            a.push_row(&remap_lc(ra));
            b.push_row(&empty);
            c.push_row(&remap_lc(rc));
        }
        for (ra, rb, rc) in mul {
            a.push_row(&remap_lc(ra));
            b.push_row(&remap_lc(rb));
            c.push_row(&remap_lc(rc));
        }
        for _ in used..total - MASK_ROWS {
            a.push_row(&empty);
            b.push_row(&empty);
            c.push_row(&empty);
        }
        for k in 0..MASK_ROWS {
            let p = Lc::term(Var((mask_var_base + k) as u32), F::ONE);
            match k / 4 {
                0 => {
                    a.push_row(&p);
                    b.push_row(&one);
                    c.push_row(&p);
                }
                1 => {
                    a.push_row(&one);
                    b.push_row(&p);
                    c.push_row(&p);
                }
                _ => {
                    a.push_row(&p);
                    b.push_row(&two);
                    c.push_row(&p.scaled(F::TWO));
                }
            }
        }

        let mut z = Vec::new();
        dregg_sig_core::wipe::secret_vec_reserve(&mut z, num_vars);
        dregg_sig_core::wipe::secret_vec_extend_from_slice(&mut z, &self.values[..pub_prefix]);
        z.resize(p2_var_base, F::ZERO);
        dregg_sig_core::wipe::secret_vec_extend_from_slice(&mut z, &self.p2_values);
        dregg_sig_asm::volatile_fill(&mut self.p2_values, F::ZERO);
        self.p2_values = Vec::new();
        dregg_sig_core::wipe::secret_vec_extend_from_slice(&mut z, &self.values[pub_prefix..]);
        dregg_sig_asm::volatile_fill(&mut self.values, F::ZERO);
        self.values = Vec::new();
        z.resize(num_vars, F::ZERO);

        let mut shape = Shape {
            log_rows,
            num_sbox,
            num_vars,
            num_public: self.num_public,
            mask_var_base,
            a,
            b,
            c,
            hologram_meta: HologramMeta {
                poseidon2_perms: self.p2_perms,
                pub_var_blocks,
            },
            lookups: None,
            digest: [0; 32],
        };
        shape.digest = shape.compute_digest();
        (shape, z)
    }
}

/// The assignment may be a witness; a builder dropped without [`ConstraintSystem::finish`]
/// erases it.
impl Drop for ConstraintSystem {
    fn drop(&mut self) {
        dregg_sig_asm::volatile_fill(&mut self.values, F::ZERO);
        dregg_sig_asm::volatile_fill(&mut self.p2_values, F::ZERO);
        for table in &mut self.tables {
            dregg_sig_asm::volatile_fill(&mut table.mult, 0u64);
        }
    }
}

// ============================================================================
// Width-12 Poseidon2 gadgets (canonical profile of `crate::sponge`)
// ============================================================================

/// Dense matrix of a linear layer of `crate::sponge`, read off its action on unit vectors.
fn layer_matrix(layer: fn(&mut [F; 12])) -> [[F; 12]; 12] {
    let mut m = [[F::ZERO; 12]; 12];
    for j in 0..12 {
        let mut e = [F::ZERO; 12];
        e[j] = F::ONE;
        layer(&mut e);
        for i in 0..12 {
            m[i][j] = e[i];
        }
    }
    m
}

/// The permutation `crate::sponge::poseidon2_perm12` on linear forms: 118 S-box rows, no
/// other rows. Output lanes are linear forms over the last round's S-box outputs.
///
/// Inside the permutation every lane is a coefficient vector over a short local basis: the
/// twelve inputs, then the twelve outputs of the latest full round plus one output per
/// partial round since. A lane becomes a linear form only where an S-box row needs it.
pub fn poseidon2_perm(cs: &mut ConstraintSystem, st: &mut [Lc; 12]) {
    #[cfg(feature = "std")]
    let (me, mi) = {
        type Matrices = ([[F; 12]; 12], [[F; 12]; 12]);
        static MATRICES: std::sync::OnceLock<Matrices> = std::sync::OnceLock::new();
        MATRICES.get_or_init(|| {
            (
                layer_matrix(poseidon2_apply_me),
                layer_matrix(poseidon2_apply_mi),
            )
        })
    };
    #[cfg(not(feature = "std"))]
    let (me, mi) = (
        layer_matrix(poseidon2_apply_me),
        layer_matrix(poseidon2_apply_mi),
    );
    let external: Vec<Vec<F>> = me.iter().map(|row| row.to_vec()).collect();
    let form = |basis: &[Lc], coeffs: &[F], constant: F| -> Lc {
        let parts: Vec<(F, &Lc)> = coeffs.iter().copied().zip(basis).collect();
        Lc::combine(&parts).plus_const(constant)
    };

    let mut basis: Vec<Lc> = st.to_vec();
    let mut lanes = external.clone();
    for tag in [0u64, 1, 2] {
        if tag == 1 {
            for r in 0..POSEIDON2_INT_ROUNDS {
                let x = form(&basis, &lanes[0], poseidon2_const_at(1, r as u64, 0));
                basis.push(cs.p2_sbox7(&x).into());
                let n = basis.len();
                for lane in &mut lanes {
                    lane.resize(n, F::ZERO);
                }
                lanes[0].fill(F::ZERO);
                lanes[0][n - 1] = F::ONE;
                // `M_I = J + diag(d)`: every lane gets the lane sum plus `d_j` times itself.
                let mut sum = vec![F::ZERO; n];
                for lane in &lanes {
                    for (s, &c) in sum.iter_mut().zip(lane) {
                        *s += c;
                    }
                }
                for (j, lane) in lanes.iter_mut().enumerate() {
                    let d = mi[j][j] - F::ONE;
                    for (c, &s) in lane.iter_mut().zip(&sum) {
                        *c = c.const_mul(d) + s;
                    }
                }
            }
        } else {
            for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
                let outputs: Vec<Lc> = (0..12)
                    .map(|lane| {
                        let rc = poseidon2_const_at(tag, r as u64, lane as u64);
                        cs.p2_sbox7(&form(&basis, &lanes[lane], rc)).into()
                    })
                    .collect();
                basis = outputs;
                lanes = external.clone();
            }
        }
    }
    for (slot, lane) in st.iter_mut().zip(&lanes) {
        *slot = form(&basis, lane, F::ZERO);
    }
    cs.finish_p2_perm_block();
}

/// Universal 106-row (`12..118`) interior matrix coefficients of [`poseidon2_perm`].
pub(crate) struct Poseidon2InteriorTemplate {
    /// For each interior row `r_off in 0..106` (`row = 12 + r_off`), list of `(w, coeff)` in `A`
    /// where `w in 0..118` is the S-box output offset within the permutation's 128-var block.
    pub rows_a: Vec<Vec<(u8, F)>>,
    /// Round-constant (`Var::ONE`, col `0`) coefficient in `A` for each `r_off in 0..106`.
    pub const_a: [F; 106],
}

impl Poseidon2InteriorTemplate {
    fn build() -> Self {
        let mut cs = ConstraintSystem::new();
        let mut st: [Lc; 12] = core::array::from_fn(|_| cs.alloc(F::ZERO).into());
        poseidon2_perm(&mut cs, &mut st);
        assert_eq!(cs.sbox.len(), 118);
        let mut rows_a = Vec::with_capacity(106);
        let mut const_a = [F::ZERO; 106];
        for (r_off, (ra, rc)) in cs.sbox[12..118].iter().enumerate() {
            let mut terms = Vec::new();
            for &(v, coeff) in ra.terms() {
                if v == 0 {
                    const_a[r_off] = coeff;
                } else {
                    assert!(
                        (13..13 + 118).contains(&v),
                        "interior Poseidon2 row touched non-local variable {v}"
                    );
                    terms.push(((v - 13) as u8, coeff));
                }
            }
            assert_eq!(rc.terms(), &[((13 + 12 + r_off) as u32, F::ONE)]);
            rows_a.push(terms);
        }
        Self { rows_a, const_a }
    }

    #[inline]
    pub fn with<R>(run: impl FnOnce(&Self) -> R) -> R {
        #[cfg(feature = "std")]
        {
            static TEMPLATE: std::sync::OnceLock<Poseidon2InteriorTemplate> =
                std::sync::OnceLock::new();
            run(TEMPLATE.get_or_init(Self::build))
        }
        #[cfg(not(feature = "std"))]
        {
            let built = Self::build();
            run(&built)
        }
    }
}

/// Rate-6, capacity-6 sponge over [`poseidon2_perm`] with the padding of
/// `dregg-sig-cred::blind_vc::sponge12`: a `1` is added after a short final chunk, or in a
/// further block when the message length is a multiple of six. Returns the final state.
pub fn sponge12(cs: &mut ConstraintSystem, message: &[Lc]) -> [Lc; 12] {
    let mut state: [Lc; 12] = core::array::from_fn(|_| Lc::zero());
    for chunk in message.chunks(6) {
        for (lane, value) in state.iter_mut().zip(chunk) {
            *lane = lane.plus(value);
        }
        if chunk.len() < 6 {
            state[chunk.len()] = state[chunk.len()].plus_const(F::ONE);
        }
        poseidon2_perm(cs, &mut state);
    }
    if message.len().is_multiple_of(6) {
        state[0] = state[0].plus_const(F::ONE);
        poseidon2_perm(cs, &mut state);
    }
    state
}

/// [`sponge12`] on field values.
pub fn sponge12_native(message: &[F]) -> [F; 12] {
    let mut state = [F::ZERO; 12];
    for chunk in message.chunks(6) {
        for (lane, &value) in state.iter_mut().zip(chunk) {
            *lane += value;
        }
        if chunk.len() < 6 {
            state[chunk.len()] += F::ONE;
        }
        poseidon2_perm12(&mut state);
    }
    if message.len().is_multiple_of(6) {
        state[0] += F::ONE;
        poseidon2_perm12(&mut state);
    }
    state
}

#[cfg(test)]
mod tests {
    use super::*;

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    #[test]
    fn canonical_rate6_sponge_matches_accelerator_at_boundaries() {
        for n in [0, 1, 5, 6, 7, 11, 12, 13, 32] {
            let words: Vec<u64> = (0..n).map(|i| i as u64 * 7919 + 17).collect();
            let message: Vec<F> = words.iter().copied().map(F::from_u64_reduced).collect();
            let native = sponge12_native(&message);
            assert_eq!(
                native.map(|x| x.to_canonical_u64()),
                dregg_sig_accel::poseidon2::sponge12_rate6(&words)
            );
            let mut cs = ConstraintSystem::new();
            let inputs: Vec<Lc> = message.iter().map(|&v| cs.alloc(v).into()).collect();
            let out = sponge12(&mut cs, &inputs);
            assert_eq!(out.map(|v| cs.eval(&v)), native);
            let (shape, assignment) = cs.finish();
            assert!(shape.is_satisfied(&assignment));
        }
    }

    #[test]
    fn permutation_gadget_matches_native_and_uses_only_sbox_rows() {
        let mut cs = ConstraintSystem::new();
        let input: [F; 12] = core::array::from_fn(|i| f(1000 + 7 * i as u64));
        let mut st: [Lc; 12] = core::array::from_fn(|i| cs.alloc(input[i]).into());
        poseidon2_perm(&mut cs, &mut st);
        let mut native = input;
        poseidon2_perm12(&mut native);
        for (lc, want) in st.iter().zip(native) {
            assert_eq!(cs.eval(lc), want);
        }
        assert_eq!(cs.num_rows(), 118);
        // The gadget relies on the internal layer being all-ones plus a diagonal.
        let mi = layer_matrix(poseidon2_apply_mi);
        for (i, row) in mi.iter().enumerate() {
            for (j, &entry) in row.iter().enumerate() {
                assert!(i == j || entry == F::ONE);
            }
        }
        let (shape, z) = cs.finish();
        assert_eq!(shape.num_sbox, 118);
        assert!(shape.is_satisfied(&z));
        let mut bad = z.clone();
        bad[20] += F::ONE;
        assert!(!shape.is_satisfied(&bad));
    }

    #[test]
    fn sponge_gadget_matches_native_for_every_padding_case() {
        for len in [1usize, 5, 6, 7, 12, 16, 39] {
            let msg: Vec<F> = (0..len).map(|i| f(3 + 11 * i as u64)).collect();
            let mut cs = ConstraintSystem::new();
            let lcs: Vec<Lc> = msg.iter().map(|&v| cs.alloc(v).into()).collect();
            let out = sponge12(&mut cs, &lcs);
            let want = sponge12_native(&msg);
            for (lc, w) in out.iter().zip(want) {
                assert_eq!(cs.eval(lc), w, "message length {len}");
            }
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
        }
    }

    #[test]
    fn recording_keeps_the_relation_and_names_every_definition() {
        let build = |mut cs: ConstraintSystem| {
            let public: Lc = cs.public_input(f(6)).into();
            let x: Lc = cs
                .alloc_defined(f(2), || Def::Bits {
                    source: SourceId(0),
                    lo: 0,
                    width: 2,
                })
                .into();
            let y: Lc = cs.mul(&x, &x.plus_const(f(1))).into();
            cs.enforce_equal(&y, &public);
            let loose = cs.alloc(f(9));
            (cs, loose)
        };
        let (plain, _) = build(ConstraintSystem::new());
        let (shape, z) = plain.finish();
        let (mut recording, loose) = build(ConstraintSystem::new_recording());
        let source = recording.source(|| Source::Input { bits: 2 });
        assert_eq!(source.index(), 0);
        let (shape2, z2, defs) = recording.finish_recorded();
        assert_eq!((shape.digest(), &z), (shape2.digest(), &z2));
        assert_eq!(defs.vars.len(), shape.num_vars);
        assert_eq!(defs.vars[0], Def::One);
        assert_eq!(defs.vars[1], Def::Public);
        assert!(matches!(defs.vars[2], Def::Bits { width: 2, .. }));
        assert!(matches!(defs.vars[3], Def::Product(..)));
        assert_eq!(defs.undefined(), vec![loose.index()]);
        assert!(
            defs.vars[shape.mask_var_base..]
                .iter()
                .all(|d| *d == Def::Mask)
        );
        // A builder that does not record never runs the closures.
        let mut cs = ConstraintSystem::new();
        cs.alloc_defined(f(1), || unreachable!());
        cs.source(|| unreachable!());
    }

    #[test]
    fn lookups_add_no_rows_and_their_shape_is_value_independent() {
        let build = |x: [u64; 3]| {
            let mut cs = ConstraintSystem::new();
            let pairs: Vec<F> = (0..5u64).flat_map(|t| [f(t), f(10 * t)]).collect();
            let table = cs.table(2, pairs);
            let a: Lc = cs.alloc(f(x[0])).into();
            let b: Lc = cs.alloc(f(x[1])).into();
            let c: Lc = cs.alloc(f(x[2])).into();
            cs.enforce_byte(&a);
            cs.enforce_byte(&a.plus(&b));
            cs.enforce_in_table(table, &[b.clone(), c]);
            assert_eq!((cs.num_rows(), cs.num_lookups()), (0, 3));
            cs.finish()
        };
        let (shape, z) = build([200, 3, 30]);
        let (shape2, z2) = build([0, 4, 40]);
        assert_eq!(shape, shape2);
        assert_eq!(shape.digest(), shape2.digest());
        assert!(shape.is_satisfied(&z) && shape.is_satisfied(&z2));
        let lookups = shape.lookups().unwrap();
        assert_eq!(lookups.num_lookups, 3);
        assert_eq!(lookups.num_table_rows, 5 + 256);
        assert_eq!(lookups.width(), 3);
        assert_eq!(
            shape.num_vars,
            1 + 3 + 261 + MASK_ROWS + 2 * LOOKUP_MASK_ENTRIES
        );
        // Multiplicities: table 0 (pairs) row 3, table 1 (bytes) rows 200 and 203.
        let m = |row: usize| z[lookups.mult_var_base + row];
        assert_eq!(
            (m(3), m(5 + 200), m(5 + 203), m(5 + 3)),
            (f(1), f(1), f(1), f(0))
        );
        // The masking variables are free.
        let mut masked = z.clone();
        for slot in &mut masked[shape.mask_var_base..] {
            *slot = f(0xBEEF);
        }
        assert!(shape.is_satisfied(&masked));
        // Out of range, off the table, a pair from the wrong row, a wrong multiplicity.
        for bad in [[200, 56, 0], [256, 0, 0], [1, 5, 50], [1, 3, 40]] {
            let (_, z) = build(bad);
            assert!(!shape.is_satisfied(&z), "{bad:?}");
        }
        let mut wrong = z.clone();
        wrong[lookups.mult_var_base + 5 + 7] = f(1);
        assert!(!shape.is_satisfied(&wrong));
        // A table tag separates the tables: byte 3 is not the pair (3, 0) of table 0.
        let mut swapped = z;
        swapped[lookups.mult_var_base + 5 + 203] = f(0);
        swapped[lookups.mult_var_base + 5 + 200] = f(2);
        assert!(!shape.is_satisfied(&swapped));
    }

    #[test]
    fn lookups_are_bound_into_the_digest_and_absent_without_tables() {
        let build = |range: bool, second: u64| {
            let mut cs = ConstraintSystem::new();
            let a: Lc = cs.alloc(f(7)).into();
            let b: Lc = cs.alloc(f(second)).into();
            cs.enforce_boolean(&b);
            if range {
                cs.enforce_byte(&a);
            }
            cs.finish().0
        };
        let plain = build(false, 1);
        assert!(plain.lookups().is_none());
        let with = build(true, 1);
        assert_ne!(plain.digest(), with.digest());
        // The lookup adds no row; it adds the multiplicities and eight masking variables.
        assert_eq!(
            (plain.log_rows, plain.a.nnz()),
            (with.log_rows, with.a.nnz())
        );
        assert_eq!(
            with.num_vars,
            plain.num_vars + 256 + 2 * LOOKUP_MASK_ENTRIES
        );
        // Two relations that differ only in which form is looked up.
        let other = {
            let mut cs = ConstraintSystem::new();
            let _a: Lc = cs.alloc(f(7)).into();
            let b: Lc = cs.alloc(f(1)).into();
            cs.enforce_boolean(&b);
            cs.enforce_byte(&b);
            cs.finish().0
        };
        assert_eq!(
            (other.a.clone(), other.num_vars),
            (with.a.clone(), with.num_vars)
        );
        assert_ne!(other.digest(), with.digest());
    }

    #[test]
    fn witness_only_and_forked_synthesis_reproduce_the_multiplicities() {
        let synth = |cs: &mut ConstraintSystem, x: u64| {
            let v: Lc = cs.alloc(f(x)).into();
            cs.enforce_byte(&v);
            cs.enforce_byte(&v.plus_const(f(1)));
        };
        let serial = {
            let mut cs = ConstraintSystem::new();
            cs.range_table(8);
            synth(&mut cs, 5);
            synth(&mut cs, 6);
            cs.finish()
        };
        let forked = {
            let mut cs = ConstraintSystem::new();
            cs.range_table(8);
            let mut left = cs.fork_public_inputs();
            let mut right = cs.fork_public_inputs();
            synth(&mut left, 5);
            synth(&mut right, 6);
            cs.append(left);
            cs.append(right);
            cs.finish()
        };
        assert_eq!(serial, forked);
        assert!(serial.0.is_satisfied(&serial.1));
        let mut cs = ConstraintSystem::witness_only();
        cs.range_table(8);
        synth(&mut cs, 5);
        synth(&mut cs, 6);
        assert_eq!(cs.finish_assignment(&serial.0), Some(serial.1.clone()));
        let base = serial.0.lookups().unwrap().mult_var_base;
        assert_eq!([5, 6, 7].map(|r| serial.1[base + r]), [f(1), f(2), f(1)]);
    }

    #[test]
    fn masking_rows_hold_for_any_mask_values_and_shape_is_value_independent() {
        let build = |x: u64| {
            let mut cs = ConstraintSystem::new();
            let v = cs.alloc(f(x));
            let y = cs.sbox7(&v.into());
            let b = cs.alloc(f(1));
            cs.enforce_boolean(&b.into());
            let _ = cs.select(&b.into(), &y.into(), &v.into());
            cs.finish()
        };
        let (shape, mut z) = build(5);
        let (shape2, _) = build(99);
        assert_eq!(shape, shape2);
        assert_eq!(shape.digest(), shape2.digest());
        for k in 0..MASK_ROWS {
            z[shape.mask_var_base + k] = f(0xDEAD_0000 + k as u64);
        }
        assert!(shape.is_satisfied(&z));
        assert_eq!(shape.mask_row_base(2) + 4, shape.num_rows());
    }
}
