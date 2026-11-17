//! Shared witness generation: from authenticated shares of a relation's secret inputs to
//! authenticated shares of its whole assignment, with no custodian seeing a value.
//!
//! The relation's builder records, for every variable, how it follows from earlier ones
//! (`dregg_sig_agg::zk_hem::relation::Definitions`). [`generate`] walks the variables in
//! order and computes each definition on shares. It is written against [`Backend`], the
//! few operations of the authenticated engine it uses; [`Count`] runs the same code on no
//! values at all to size the preprocessing ([`demand`]).
//!
//! # Subprotocols
//!
//! Every value is an authenticated additive share over Goldilocks (`p = 2^64 - 2^32 + 1`).
//!
//! * **Random bits.** A preprocessed uniform `[a]`, one product `[a^2]`, open `a^2`, and
//!   `[b] = ([a] / sqrt(a^2) + 1) / 2` for the fixed square root. This is the random-bit
//!   protocol of SPDZ preprocessing (Damgård, Keller, Larraia, Pastro, Scholl, Smart,
//!   "Practical covertly secure MPC for dishonest majority", ESORICS 2013, Section 5,
//!   as restated in `paperbin/2020-edabits-mixed-arithmetic-binary-338`, Section 2); `a^2`
//!   is uniform over the squares whatever `b` is.
//! * **Bit decomposition** of a shared `x < 2^m` ([`Witgen::decompose`]). The mask is a
//!   value whose bits are shared random bits, which is what an edaBit is
//!   (`2020-edabits-mixed-arithmetic-binary-338`, Section 3; here both halves live in the
//!   one field, so no cut-and-choose between domains is needed). Two cases:
//!   * `m <= 22`: `r` of `m + 40` bits, open `c = x + r` (no wrap), and the low `m` bits of
//!     `c - r` by a borrow chain with one product per bit. `c` is within `2^-40` of
//!     uniform on its range: statistical masking.
//!   * otherwise: `r` of 64 bits whose top 32 bits are not all ones (checked by opening
//!     their product, which depends on the mask alone), so `r <= p - 2`. Open
//!     `c = x + r mod p`, which is uniform up to `2^-64`. The wrap `beta = [c < r]` and
//!     `D = c - r mod 2^64` come from one 64-step borrow chain, and
//!     `x = D + beta - 2^32 beta` because `p = 2^64 - 2^32 + 1`: one more chain. This is
//!     the comparison-with-a-public-value step of
//!     `paperbin/2021-rabbit-efficient-comparison-119` (Section 4.1, "LTC"), specialised to
//!     this prime; no slack, so it is exact for every `x < p`.
//! * **Integers.** An integer is a polynomial in `2^8` whose coefficients are shares with
//!   public intervals. [`Witgen::normalize`] turns it into bits by a carry chain, one
//!   decomposition per coefficient. Products of two such integers are computed at as many
//!   points as the product has coefficients and interpolated ([`Witgen::poly_mul`]), one
//!   secure product per coefficient.
//! * **Reduction modulo a public prime** `q` ([`Witgen::canonical`]): bits of the integer
//!   (plus a public multiple of `q` that makes it non-negative), then the bits above the
//!   limbs of `q` are folded down with the public constants `2^i mod q` and normalized
//!   again until that stops shortening the value, then conditional subtractions of
//!   `2^j q` by a borrow chain and a selection.
//! * **Division modulo `q`** (a slope `num / den`): a shared `rho` of `|q| + 40` random
//!   bits, the integer `den rho + q S` for a shared `S` of 40 bits more than the quotient
//!   is opened in full and gives `w = den rho mod q`, which is within `2^-40` of uniform
//!   when `den != 0 mod q`; then `num rho w^-1 mod q` by the reduction above with the
//!   public constants `2^i w^-1 mod q`. This is the masked inversion of Bar-Ilan and
//!   Beaver (PODC 1989) carried out on limbs.
//! * **Exact division** by an odd public `q` of an integer `N = Q q` with `Q < 2^k`:
//!   `Q = N q^-1 mod 2^k`, from the low `k` bits of `N`.
//! * **Field ratio** `num / den` and **inverse-or-zero** of a value in a small range:
//!   masked inversion in Goldilocks, and the interpolating polynomial through
//!   `(0, 0), (i, 1 / i)`.
//!
//! # What is opened, and why it tells nothing
//!
//! Beaver openings; `a^2` of random-bit generation; the top-bits product of an exact
//! mask; `x + r` of a decomposition; `den r` of a field ratio; the integer
//! `den rho + q S + K q` of a division. The first four are functions of fresh
//! preprocessed values alone or are masked by one. The last two are masked only when the
//! shared value behind them is the one the protocol defines, so [`Backend::check`] (the
//! batch MAC check) runs before each of them: a custodian that sent a wrong share in any
//! earlier opening is caught there, before a value that its error could have steered is
//! opened. That ordering is this module's own argument; the engine's guarantee it rests on
//! (an opening that differs from the shared value fails the check except with probability
//! `2^-126`) is SPDZ's.
//!
//! One predicate of the witness is revealed by design: a division whose denominator is
//! zero modulo `q` aborts with [`WitgenError::ZeroDenominator`]. For the ownership
//! relations that is the chord slope of an addition whose two points have equal `x`. The
//! gadget's complete addition handles that case with the tangent; here the quorum aborts
//! instead, which tells the custodians that the key is one of the few scalars for which
//! the last window meets the accumulated point.
//!
//! The statistical parameter is 40 bits per masked opening.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::ops::{Add, Sub};

use dregg_sig_agg::field::Goldilocks;
use dregg_sig_agg::zk_hem::relation::{Def, Definitions, IntCoef, Lc, Shape, Source};

use super::engine::{Engine, MpcError, Sb};
use super::net::Transport;

type F = Goldilocks;

/// Statistical masking parameter, in bits.
pub const SIGMA: u32 = 40;
/// Largest width decomposed with a statistical mask.
const STAT_MAX: u32 = 62 - SIGMA;
/// Opened values after which the batch MAC check runs.
const CHECK_EVERY: usize = 1 << 15;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WitgenError {
    Mpc(MpcError),
    /// The definitions do not belong to the shape, or a variable has no definition, or one
    /// outside what this generator computes (the variable or source index is given).
    Unsupported {
        index: usize,
    },
    /// The supplied inputs do not match the relation's input sources.
    Inputs,
    /// A division by a value that is zero. Reveals that fact about the witness.
    ZeroDenominator,
    /// An opened value that the protocol defines as a bit is not one.
    NotABit,
}

impl From<MpcError> for WitgenError {
    fn from(e: MpcError) -> Self {
        Self::Mpc(e)
    }
}

/// The operations of the authenticated engine that witness generation uses.
pub trait Backend {
    type S: Copy + Add<Output = Self::S> + Sub<Output = Self::S>;
    fn scale(s: Self::S, k: F) -> Self::S;
    fn public(&self, c: F) -> Self::S;
    fn random(&mut self) -> Result<Self::S, MpcError>;
    fn mul(&mut self, xs: &[Self::S], ys: &[Self::S]) -> Result<Vec<Self::S>, MpcError>;
    fn open(&mut self, xs: &[Self::S]) -> Result<Vec<F>, MpcError>;
    fn check(&mut self) -> Result<(), MpcError>;
    /// Whether opened values are placeholders (see [`Count`]).
    fn counting(&self) -> bool {
        false
    }
}

impl<T: Transport> Backend for Engine<T> {
    type S = Sb;
    fn scale(s: Sb, k: F) -> Sb {
        s.scale(k)
    }
    fn public(&self, c: F) -> Sb {
        Engine::public(self, c)
    }
    fn random(&mut self) -> Result<Sb, MpcError> {
        Engine::random(self)
    }
    fn mul(&mut self, xs: &[Sb], ys: &[Sb]) -> Result<Vec<Sb>, MpcError> {
        Engine::mul(self, xs, ys)
    }
    fn open(&mut self, xs: &[Sb]) -> Result<Vec<F>, MpcError> {
        Engine::open(self, xs)
    }
    fn check(&mut self) -> Result<(), MpcError> {
        Engine::check(self)
    }
}

/// A share that carries no value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unit;

impl Add for Unit {
    type Output = Unit;
    fn add(self, _: Unit) -> Unit {
        Unit
    }
}

impl Sub for Unit {
    type Output = Unit;
    fn sub(self, _: Unit) -> Unit {
        Unit
    }
}

/// A backend with no values: it counts what [`generate`] would consume. Every opening
/// reads as zero, which is the branch of each chain that uses the most products, so the
/// counts are upper bounds; the retries of random-bit and mask generation (probability
/// `2^-64` and `2^-32` each) are not counted.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Count {
    pub triples: usize,
    pub randoms: usize,
    pub opened: usize,
    pub rounds: usize,
    pub checks: usize,
}

impl Backend for Count {
    type S = Unit;
    fn scale(_: Unit, _: F) -> Unit {
        Unit
    }
    fn public(&self, _: F) -> Unit {
        Unit
    }
    fn random(&mut self) -> Result<Unit, MpcError> {
        self.randoms += 1;
        Ok(Unit)
    }
    fn mul(&mut self, xs: &[Unit], _: &[Unit]) -> Result<Vec<Unit>, MpcError> {
        self.triples += xs.len();
        self.opened += 2 * xs.len();
        self.rounds += 1;
        Ok(vec![Unit; xs.len()])
    }
    fn open(&mut self, xs: &[Unit]) -> Result<Vec<F>, MpcError> {
        self.opened += xs.len();
        self.rounds += 1;
        Ok(vec![F::ZERO; xs.len()])
    }
    fn check(&mut self) -> Result<(), MpcError> {
        self.checks += 1;
        Ok(())
    }
    fn counting(&self) -> bool {
        true
    }
}

// ============================================================================
// Public integers
// ============================================================================

/// A non-negative integer, little-endian 64-bit words, no leading zero word.
type Nat = Vec<u64>;

fn nat_trim(mut a: Nat) -> Nat {
    while a.last() == Some(&0) {
        a.pop();
    }
    a
}

fn nat_from_le(bytes: &[u8]) -> Nat {
    let mut out = vec![0u64; bytes.len().div_ceil(8)];
    for (i, &b) in bytes.iter().enumerate() {
        out[i / 8] |= u64::from(b) << (8 * (i % 8));
    }
    nat_trim(out)
}

fn nat_bit(a: &[u64], i: usize) -> u64 {
    a.get(i / 64).map_or(0, |w| (w >> (i % 64)) & 1)
}

fn nat_byte(a: &[u64], k: usize) -> u64 {
    a.get(k / 8).map_or(0, |w| (w >> (8 * (k % 8))) & 0xff)
}

fn nat_bitlen(a: &[u64]) -> usize {
    match a.iter().rposition(|&w| w != 0) {
        Some(i) => 64 * i + 64 - a[i].leading_zeros() as usize,
        None => 0,
    }
}

fn nat_cmp(a: &[u64], b: &[u64]) -> Ordering {
    let n = a.len().max(b.len());
    for i in (0..n).rev() {
        let (x, y) = (
            a.get(i).copied().unwrap_or(0),
            b.get(i).copied().unwrap_or(0),
        );
        if x != y {
            return x.cmp(&y);
        }
    }
    Ordering::Equal
}

fn nat_add(a: &[u64], b: &[u64]) -> Nat {
    let n = a.len().max(b.len());
    let mut out = Vec::with_capacity(n + 1);
    let mut carry = 0u128;
    for i in 0..n {
        let s = u128::from(a.get(i).copied().unwrap_or(0))
            + u128::from(b.get(i).copied().unwrap_or(0))
            + carry;
        out.push(s as u64);
        carry = s >> 64;
    }
    out.push(carry as u64);
    nat_trim(out)
}

/// `a - b` for `a >= b`.
fn nat_sub(a: &[u64], b: &[u64]) -> Nat {
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0u64;
    for (i, &x) in a.iter().enumerate() {
        let y = b.get(i).copied().unwrap_or(0);
        let (d, b1) = x.overflowing_sub(y);
        let (d, b2) = d.overflowing_sub(borrow);
        out.push(d);
        borrow = u64::from(b1 | b2);
    }
    debug_assert_eq!(borrow, 0);
    nat_trim(out)
}

fn nat_mul(a: &[u64], b: &[u64]) -> Nat {
    let mut out = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            let t = u128::from(x) * u128::from(y) + u128::from(out[i + j]) + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        out[i + b.len()] = carry as u64;
    }
    nat_trim(out)
}

fn nat_shl(a: &[u64], k: usize) -> Nat {
    let (w, s) = (k / 64, k % 64);
    let mut out = vec![0u64; a.len() + w + 1];
    for (i, &x) in a.iter().enumerate() {
        out[i + w] |= x << s;
        if s != 0 {
            out[i + w + 1] |= x >> (64 - s);
        }
    }
    nat_trim(out)
}

/// Quotient and remainder by a nonzero `d`, bit by bit.
fn nat_divrem(a: &[u64], d: &[u64]) -> (Nat, Nat) {
    let bits = nat_bitlen(a);
    let mut q = vec![0u64; a.len()];
    let mut r: Nat = Vec::new();
    for i in (0..bits).rev() {
        r = nat_shl(&r, 1);
        if nat_bit(a, i) == 1 {
            if r.is_empty() {
                r.push(1);
            } else {
                r[0] |= 1;
            }
        }
        if nat_cmp(&r, d) != Ordering::Less {
            r = nat_sub(&r, d);
            q[i / 64] |= 1 << (i % 64);
        }
    }
    (nat_trim(q), r)
}

fn nat_mulmod(a: &[u64], b: &[u64], p: &[u64]) -> Nat {
    nat_divrem(&nat_mul(a, b), p).1
}

/// `a^-1 mod p` for a prime `p` and `a != 0 mod p`.
fn nat_invmod(a: &[u64], p: &[u64]) -> Nat {
    let e = nat_sub(p, &[2]);
    let mut acc: Nat = vec![1];
    for i in (0..nat_bitlen(&e)).rev() {
        acc = nat_mulmod(&acc, &acc, p);
        if nat_bit(&e, i) == 1 {
            acc = nat_mulmod(&acc, a, p);
        }
    }
    acc
}

/// `acc += v 2^(8 byte_pos)` modulo `2^(64 acc.len())`.
fn nat_add_signed(acc: &mut [u64], v: i128, byte_pos: usize) {
    let (neg, mag) = (v < 0, v.unsigned_abs());
    let (w, s) = (byte_pos / 8, 8 * (byte_pos % 8));
    let (lo, hi) = (mag as u64, (mag >> 64) as u64);
    let words = if s == 0 {
        [lo, hi, 0]
    } else {
        [lo << s, (lo >> (64 - s)) | (hi << s), hi >> (64 - s)]
    };
    let mut carry = 0u64;
    for (k, slot) in acc.iter_mut().enumerate().skip(w) {
        let add = words.get(k - w).copied().unwrap_or(0);
        if neg {
            let (d, b1) = slot.overflowing_sub(add);
            let (d, b2) = d.overflowing_sub(carry);
            *slot = d;
            carry = u64::from(b1 | b2);
        } else {
            let (d, c1) = slot.overflowing_add(add);
            let (d, c2) = d.overflowing_add(carry);
            *slot = d;
            carry = u64::from(c1 | c2);
        }
        if k - w >= 3 && carry == 0 {
            break;
        }
    }
}

fn f_signed(v: i128) -> F {
    let m = F::from_u64_reduced((v.unsigned_abs() % 0xFFFF_FFFF_0000_0001u128) as u64);
    if v < 0 { F::ZERO - m } else { m }
}

fn pow2(i: usize) -> F {
    F::TWO.pow(i as u64)
}

/// The square root of a nonzero square, the same one for every caller (Tonelli-Shanks;
/// `p - 1 = 2^32 (2^32 - 1)` and 7 generates the multiplicative group). `None` for a
/// value that is not a square.
fn sqrt(v: F) -> Option<F> {
    const Q: u64 = (1 << 32) - 1;
    let mut x = v.pow(Q.div_ceil(2));
    let mut t = v.pow(Q);
    let mut c = F::from_u64_reduced(7).pow(Q);
    let mut m = 32;
    while t != F::ONE {
        let (mut i, mut tt) = (0, t);
        while tt != F::ONE {
            tt = tt * tt;
            i += 1;
            if i == m {
                return None;
            }
        }
        let mut b = c;
        for _ in 0..m - i - 1 {
            b = b * b;
        }
        x *= b;
        c = b * b;
        t *= c;
        m = i;
    }
    Some(x)
}

/// Row `k`, column `j`: coefficient `k` of the Lagrange polynomial of point `j` among the
/// points `0, .., n - 1`.
fn interpolation_matrix(n: usize) -> Vec<Vec<F>> {
    let pt = |j: usize| F::from_u64_reduced(j as u64);
    // master(t) = prod (t - j)
    let mut master = vec![F::ONE];
    for j in 0..n {
        let mut next = vec![F::ZERO; master.len() + 1];
        for (k, &c) in master.iter().enumerate() {
            next[k + 1] += c;
            next[k] -= c * pt(j);
        }
        master = next;
    }
    let mut out = vec![vec![F::ZERO; n]; n];
    for j in 0..n {
        // quotient = master / (t - j), by synthetic division from the top.
        let mut quotient = vec![F::ZERO; n];
        let mut carry = F::ZERO;
        for k in (0..n).rev() {
            carry = master[k + 1] + carry * pt(j);
            quotient[k] = carry;
        }
        let at = quotient
            .iter()
            .rev()
            .fold(F::ZERO, |acc, &c| acc * pt(j) + c);
        let inv = at.inv();
        for (row, &q) in out.iter_mut().zip(&quotient) {
            row[j] = q * inv;
        }
    }
    out
}

// ============================================================================
// Shared integers
// ============================================================================

/// An integer `sum_k c_k 2^(8k)` with shared coefficients in public intervals.
struct Int<S> {
    c: Vec<S>,
    lo: Vec<i128>,
    hi: Vec<i128>,
}

impl<S: Copy> Int<S> {
    fn len(&self) -> usize {
        self.c.len()
    }
}

const COEF_BOUND: i128 = 1 << 62;

/// A public prime modulus.
struct Modulus {
    p: Nat,
    bits: usize,
    limbs: usize,
    /// `p = sum digit 2^(8 position)` with digits in `[-128, 127]`.
    digits: Vec<(usize, i64)>,
}

impl Modulus {
    fn new(bytes_le: &[u8]) -> Self {
        let p = nat_from_le(bytes_le);
        let mut digits = Vec::new();
        let mut carry = 0i64;
        for (k, &b) in bytes_le.iter().enumerate() {
            let mut d = i64::from(b) + carry;
            carry = 0;
            if d > 127 {
                d -= 256;
                carry = 1;
            }
            if d != 0 {
                digits.push((k, d));
            }
        }
        if carry != 0 {
            digits.push((bytes_le.len(), carry));
        }
        Self {
            bits: nat_bitlen(&p),
            limbs: bytes_le.len(),
            p,
            digits,
        }
    }
}

/// One custodian's (or the counter's) run of witness generation.
pub struct Witgen<'a, B: Backend> {
    b: &'a mut B,
    matrices: BTreeMap<usize, Vec<Vec<F>>>,
    unchecked: usize,
    zero: B::S,
    one: B::S,
}

impl<'a, B: Backend> Witgen<'a, B> {
    pub fn new(b: &'a mut B) -> Self {
        let (zero, one) = (b.public(F::ZERO), b.public(F::ONE));
        Self {
            b,
            matrices: BTreeMap::new(),
            unchecked: 0,
            zero,
            one,
        }
    }

    fn mul(&mut self, xs: &[B::S], ys: &[B::S]) -> Result<Vec<B::S>, WitgenError> {
        self.unchecked += 2 * xs.len();
        Ok(self.b.mul(xs, ys)?)
    }

    fn mul1(&mut self, x: B::S, y: B::S) -> Result<B::S, WitgenError> {
        Ok(self.mul(&[x], &[y])?[0])
    }

    fn open(&mut self, xs: &[B::S]) -> Result<Vec<F>, WitgenError> {
        self.unchecked += xs.len();
        Ok(self.b.open(xs)?)
    }

    fn check(&mut self) -> Result<(), WitgenError> {
        self.unchecked = 0;
        Ok(self.b.check()?)
    }

    fn eval(&self, z: &[B::S], lc: &Lc) -> B::S {
        lc.terms()
            .iter()
            .fold(self.zero, |acc, &(v, c)| acc + B::scale(z[v as usize], c))
    }

    /// Shared uniform bits.
    pub fn random_bits(&mut self, n: usize) -> Result<Vec<B::S>, WitgenError> {
        let half = F::TWO.inv();
        let mut out = Vec::with_capacity(n);
        while out.len() < n {
            let a: Vec<B::S> = (0..n - out.len())
                .map(|_| self.b.random())
                .collect::<Result<_, _>>()?;
            let squares = self.mul(&a, &a)?;
            let opened = self.open(&squares)?;
            for (&a, &v) in a.iter().zip(&opened) {
                if self.b.counting() {
                    out.push(a);
                } else if v != F::ZERO {
                    let Some(root) = sqrt(v) else {
                        // The square of a shared value was opened as a non-square: some
                        // opening was wrong. The check names it; the value opened
                        // depends on preprocessed values only.
                        self.check()?;
                        return Err(WitgenError::NotABit);
                    };
                    out.push(B::scale(a, root.inv() * half) + self.b.public(half));
                }
            }
        }
        Ok(out)
    }

    /// 64 shared random bits whose value is at most `p - 2`.
    fn exact_mask(&mut self) -> Result<Vec<B::S>, WitgenError> {
        loop {
            let bits = self.random_bits(64)?;
            let mut level: Vec<B::S> = bits[32..].to_vec();
            while level.len() > 1 {
                let (xs, ys): (Vec<B::S>, Vec<B::S>) =
                    level.chunks_exact(2).map(|p| (p[0], p[1])).unzip();
                level = self.mul(&xs, &ys)?;
            }
            let all_ones = self.open(&level)?[0];
            if self.b.counting() || all_ones == F::ZERO {
                return Ok(bits);
            }
        }
    }

    /// `(c - r) mod 2^len` for the public `c` and shared bits `r`, with the final borrow.
    fn sub_from_public(
        &mut self,
        c: u64,
        r: &[B::S],
        len: usize,
    ) -> Result<(Vec<B::S>, B::S), WitgenError> {
        let mut out = Vec::with_capacity(len);
        let mut borrow = self.zero;
        for (i, &ri) in r.iter().enumerate().take(len) {
            let both = self.mul1(ri, borrow)?;
            let xor = ri + borrow - B::scale(both, F::TWO);
            if (c >> i) & 1 == 1 {
                out.push(self.one - xor);
                borrow = both;
            } else {
                out.push(xor);
                borrow = ri + borrow - both;
            }
        }
        Ok((out, borrow))
    }

    /// The bits of `x`, which lies in `[0, 2^m)` and is below the field prime; `m <= 64`.
    pub fn decompose(&mut self, x: B::S, m: u32) -> Result<Vec<B::S>, WitgenError> {
        assert!(m <= 64);
        let m = m as usize;
        if m == 0 {
            return Ok(Vec::new());
        }
        let pack = |bits: &[B::S]| {
            bits.iter()
                .enumerate()
                .fold(x, |acc, (i, &b)| acc + B::scale(b, pow2(i)))
        };
        if m as u32 <= STAT_MAX {
            let r = self.random_bits(m + SIGMA as usize)?;
            let c = self.open(&[pack(&r)])?[0].to_canonical_u64();
            return Ok(self.sub_from_public(c, &r, m)?.0);
        }
        let r = self.exact_mask()?;
        let c = self.open(&[pack(&r)])?[0].to_canonical_u64();
        let (d, beta) = self.sub_from_public(c, &r, 64)?;
        // x = D + beta - 2^32 beta.
        let mut out = Vec::with_capacity(m);
        let mut carry = beta;
        for &di in d.iter().take(m.min(32)) {
            let both = self.mul1(di, carry)?;
            out.push(di + carry - B::scale(both, F::TWO));
            carry = both;
        }
        let mut borrow = beta - carry;
        for &di in d.iter().take(m).skip(32) {
            let both = self.mul1(di, borrow)?;
            out.push(di + borrow - B::scale(both, F::TWO));
            borrow = borrow - both;
        }
        Ok(out)
    }

    fn matrix(&mut self, n: usize) -> &Vec<Vec<F>> {
        self.matrices
            .entry(n)
            .or_insert_with(|| interpolation_matrix(n))
    }

    /// Coefficients of the product of two polynomials, one secure product each.
    pub fn poly_mul(&mut self, a: &[B::S], b: &[B::S]) -> Result<Vec<B::S>, WitgenError> {
        let n = a.len() + b.len() - 1;
        let at = |poly: &[B::S], s: usize| {
            let s = F::from_u64_reduced(s as u64);
            poly.iter()
                .rev()
                .fold(self.zero, |acc, &c| B::scale(acc, s) + c)
        };
        let xs: Vec<B::S> = (0..n).map(|s| at(a, s)).collect();
        let ys: Vec<B::S> = (0..n).map(|s| at(b, s)).collect();
        let values = self.mul(&xs, &ys)?;
        let zero = self.zero;
        let matrix = self.matrix(n);
        Ok(matrix
            .iter()
            .map(|row| {
                row.iter()
                    .zip(&values)
                    .fold(zero, |acc, (&k, &v)| acc + B::scale(v, k))
            })
            .collect())
    }

    fn int_of(&self, z: &[B::S], coefs: &[IntCoef]) -> Int<B::S> {
        Int {
            c: coefs.iter().map(|c| self.eval(z, &c.lc)).collect(),
            lo: coefs.iter().map(|c| c.lo).collect(),
            hi: coefs.iter().map(|c| c.hi).collect(),
        }
    }

    fn int_of_bits(&self, bits: &[B::S]) -> Int<B::S> {
        let c: Vec<B::S> = bits
            .chunks(8)
            .map(|limb| {
                limb.iter()
                    .enumerate()
                    .fold(self.zero, |acc, (t, &b)| acc + B::scale(b, pow2(t)))
            })
            .collect();
        Int {
            lo: vec![0; c.len()],
            hi: bits.chunks(8).map(|l| (1i128 << l.len()) - 1).collect(),
            c,
        }
    }

    fn int_add(&self, a: &Int<B::S>, b: &Int<B::S>) -> Int<B::S> {
        let n = a.len().max(b.len());
        let get = |x: &Int<B::S>, k: usize| match x.c.get(k) {
            Some(&c) => (c, x.lo[k], x.hi[k]),
            None => (self.zero, 0, 0),
        };
        let mut out = Int {
            c: Vec::with_capacity(n),
            lo: Vec::with_capacity(n),
            hi: Vec::with_capacity(n),
        };
        for k in 0..n {
            let (x, y) = (get(a, k), get(b, k));
            out.c.push(x.0 + y.0);
            out.lo.push(x.1 + y.1);
            out.hi.push(x.2 + y.2);
        }
        out
    }

    fn int_mul(&mut self, a: &Int<B::S>, b: &Int<B::S>) -> Result<Int<B::S>, WitgenError> {
        let wide = WitgenError::Unsupported { index: usize::MAX };
        let n = a.len() + b.len() - 1;
        let (mut lo, mut hi) = (vec![0i128; n], vec![0i128; n]);
        for i in 0..a.len() {
            for j in 0..b.len() {
                let corners = [
                    a.lo[i].checked_mul(b.lo[j]),
                    a.lo[i].checked_mul(b.hi[j]),
                    a.hi[i].checked_mul(b.lo[j]),
                    a.hi[i].checked_mul(b.hi[j]),
                ];
                let mut least = i128::MAX;
                let mut most = i128::MIN;
                for c in corners {
                    let c = c.ok_or(wide)?;
                    least = least.min(c);
                    most = most.max(c);
                }
                lo[i + j] = lo[i + j].checked_add(least).ok_or(wide)?;
                hi[i + j] = hi[i + j].checked_add(most).ok_or(wide)?;
            }
        }
        if lo.iter().any(|&v| v <= -COEF_BOUND) || hi.iter().any(|&v| v >= COEF_BOUND) {
            return Err(wide);
        }
        Ok(Int {
            c: self.poly_mul(&a.c, &b.c)?,
            lo,
            hi,
        })
    }

    /// `sum_j a_j b_j + linear`.
    fn int_expr(
        &mut self,
        z: &[B::S],
        products: &[(Vec<IntCoef>, Vec<IntCoef>)],
        linear: &[IntCoef],
    ) -> Result<Int<B::S>, WitgenError> {
        let mut acc = self.int_of(z, linear);
        for (a, b) in products {
            let (a, b) = (self.int_of(z, a), self.int_of(z, b));
            let product = self.int_mul(&a, &b)?;
            acc = self.int_add(&acc, &product);
        }
        Ok(acc)
    }

    /// The least `K` with `x + K q >= 0` over the intervals (as `K q`), and the largest
    /// value `x + K q` can take.
    fn lift(x: &Int<B::S>, q: &Modulus) -> (Nat, Nat) {
        let words = x.len() / 8 + 4;
        let (mut neg, mut pos) = (vec![0u64; words], vec![0u64; words]);
        for k in 0..x.len() {
            nat_add_signed(&mut neg, (-x.lo[k]).max(0), k);
            nat_add_signed(&mut pos, x.hi[k].max(0), k);
        }
        let (quotient, rest) = nat_divrem(&neg, &q.p);
        let k = if rest.is_empty() {
            quotient
        } else {
            nat_add(&quotient, &[1])
        };
        let kq = nat_mul(&k, &q.p);
        let most = nat_add(&nat_trim(pos), &kq);
        (kq, most)
    }

    /// The low `out_bits` bits of the integer `x + add`, which is non-negative.
    fn normalize(
        &mut self,
        x: &Int<B::S>,
        add: &[u64],
        out_bits: usize,
    ) -> Result<Vec<B::S>, WitgenError> {
        let limbs = out_bits.div_ceil(8);
        let mut constant = vec![0u64; limbs / 8 + 4];
        for (slot, &w) in constant.iter_mut().zip(add) {
            *slot = w;
        }
        for k in 0..x.len().min(limbs) {
            nat_add_signed(&mut constant, x.lo[k], k);
        }
        let mut out = Vec::with_capacity(8 * limbs);
        let (mut carry, mut carry_max) = (self.zero, 0u128);
        for k in 0..limbs {
            let digit = nat_byte(&constant, k);
            if k >= x.len() && carry_max == 0 {
                out.extend((0..8).map(|t| self.b.public(F::from_u64_reduced((digit >> t) & 1))));
                continue;
            }
            let mut t = carry + self.b.public(F::from_u64_reduced(digit));
            let mut most = carry_max + 255;
            if k < x.len() {
                t = t + x.c[k] - self.b.public(f_signed(x.lo[k]));
                most += (x.hi[k] - x.lo[k]) as u128;
            }
            if most >= 1 << 63 {
                return Err(WitgenError::Unsupported { index: usize::MAX });
            }
            let m = 128 - most.leading_zeros();
            let mut bits = self.decompose(t, m)?;
            bits.resize(bits.len().max(8), self.zero);
            carry = bits[8..]
                .iter()
                .enumerate()
                .fold(self.zero, |acc, (i, &b)| acc + B::scale(b, pow2(i)));
            carry_max = most >> 8;
            out.extend_from_slice(&bits[..8]);
        }
        out.truncate(out_bits);
        Ok(out)
    }

    /// `bits >= c ? bits - c : bits` for the public `c`.
    fn conditional_sub(&mut self, bits: &[B::S], c: &[u64]) -> Result<Vec<B::S>, WitgenError> {
        if nat_bitlen(c) > bits.len() {
            return Ok(bits.to_vec());
        }
        let mut diff = Vec::with_capacity(bits.len());
        let mut borrow = self.zero;
        for (i, &v) in bits.iter().enumerate() {
            let both = self.mul1(v, borrow)?;
            let xor = v + borrow - B::scale(both, F::TWO);
            if nat_bit(c, i) == 1 {
                diff.push(self.one - xor);
                borrow = self.one - v + both;
            } else {
                diff.push(xor);
                borrow = borrow - both;
            }
        }
        // A final borrow means `bits < c`: keep `bits`.
        let deltas: Vec<B::S> = bits.iter().zip(&diff).map(|(&v, &d)| v - d).collect();
        let keep = self.mul(&vec![borrow; bits.len()], &deltas)?;
        Ok(diff.iter().zip(&keep).map(|(&d, &k)| d + k).collect())
    }

    /// The canonical residue modulo `q` of the integer with the given bits and bound.
    fn reduce_bits(
        &mut self,
        mut bits: Vec<B::S>,
        mut most: Nat,
        q: &Modulus,
        scale: Option<&[u64]>,
    ) -> Result<Vec<B::S>, WitgenError> {
        let base = 8 * q.limbs;
        let mut scale = scale.map(<[u64]>::to_vec);
        loop {
            // weights[i]: what bit `i` contributes, modulo q.
            let first = if scale.is_some() { 0 } else { base };
            if bits.len() <= first {
                break;
            }
            let mut weight = match &scale {
                Some(s) => nat_divrem(s, &q.p).1,
                None => nat_divrem(&nat_shl(&[1], base), &q.p).1,
            };
            let mut next_most: Nat = if scale.is_some() {
                Vec::new()
            } else {
                nat_sub(&nat_shl(&[1], base), &[1])
            };
            let kept = if scale.is_some() {
                0
            } else {
                base.min(bits.len())
            };
            let mut folded = self.int_of_bits(&bits[..kept]);
            folded.c.resize(q.limbs, self.zero);
            folded.lo.resize(q.limbs, 0);
            folded.hi.resize(q.limbs, 0);
            for &bit in &bits[first..] {
                for j in 0..q.limbs {
                    let byte = nat_byte(&weight, j);
                    if byte != 0 {
                        folded.c[j] = folded.c[j] + B::scale(bit, F::from_u64_reduced(byte));
                    }
                    // With an opened scale the weights are not known in advance; the
                    // widths then come from their bound, so that what is consumed does
                    // not depend on the opened value.
                    folded.hi[j] += if scale.is_some() {
                        255
                    } else {
                        i128::from(byte)
                    };
                }
                next_most = nat_add(&next_most, if scale.is_some() { &q.p } else { &weight });
                weight = nat_shl(&weight, 1);
                if nat_cmp(&weight, &q.p) != Ordering::Less {
                    weight = nat_sub(&weight, &q.p);
                }
            }
            if scale.is_none() && nat_bitlen(&next_most) >= bits.len() {
                break;
            }
            scale = None;
            bits = self.normalize(&folded, &[], nat_bitlen(&next_most))?;
            most = next_most;
        }
        let count = nat_divrem(&most, &q.p).0;
        for j in (0..nat_bitlen(&count)).rev() {
            bits = self.conditional_sub(&bits, &nat_shl(&q.p, j))?;
        }
        bits.resize(q.bits, self.zero);
        Ok(bits)
    }

    /// The canonical residue of `x` modulo `q`, as bits.
    fn canonical(&mut self, x: &Int<B::S>, q: &Modulus) -> Result<Vec<B::S>, WitgenError> {
        let (kq, most) = Self::lift(x, q);
        let bits = self.normalize(x, &kq, nat_bitlen(&most))?;
        self.reduce_bits(bits, most, q, None)
    }

    /// `x mod q`, opened. The integer that is opened is `x + (K + S) q` for a shared
    /// uniform `S` with [`SIGMA`] bits more than the quotient of `x` can have.
    fn open_residue(&mut self, x: &Int<B::S>, q: &Modulus) -> Result<Nat, WitgenError> {
        let (_, most) = Self::lift(x, q);
        let quotient_bits = nat_bitlen(&nat_divrem(&most, &q.p).0) + 1;
        let s_bits = self.random_bits(quotient_bits + SIGMA as usize)?;
        let s = self.int_of_bits(&s_bits);
        let mut qs = Int {
            c: vec![self.zero; s.len() + q.limbs + 1],
            lo: vec![0; s.len() + q.limbs + 1],
            hi: vec![0; s.len() + q.limbs + 1],
        };
        for &(pos, digit) in &q.digits {
            for k in 0..s.len() {
                let d = i128::from(digit);
                qs.c[k + pos] = qs.c[k + pos] + B::scale(s.c[k], f_signed(d));
                qs.lo[k + pos] += (d * s.hi[k]).min(0);
                qs.hi[k + pos] += (d * s.hi[k]).max(0);
            }
        }
        let masked = self.int_add(x, &qs);
        let (kq, most) = Self::lift(&masked, q);
        let bits = self.normalize(&masked, &kq, nat_bitlen(&most))?;
        self.check()?;
        let opened = self.open(&bits)?;
        let mut value = vec![0u64; opened.len() / 64 + 1];
        for (i, &v) in opened.iter().enumerate() {
            match v.to_canonical_u64() {
                0 => {}
                1 => value[i / 64] |= 1 << (i % 64),
                _ => return Err(WitgenError::NotABit),
            }
        }
        Ok(nat_divrem(&value, &q.p).1)
    }

    /// The canonical residue of `num / den` modulo `q`, as bits.
    fn quotient_mod(
        &mut self,
        num: &Int<B::S>,
        den: &Int<B::S>,
        q: &Modulus,
    ) -> Result<Vec<B::S>, WitgenError> {
        let rho_bits = self.random_bits(q.bits + SIGMA as usize)?;
        let rho = self.int_of_bits(&rho_bits);
        let masked_den = self.int_mul(den, &rho)?;
        let w = self.open_residue(&masked_den, q)?;
        let inverse = if self.b.counting() {
            vec![1]
        } else if w.is_empty() {
            return Err(WitgenError::ZeroDenominator);
        } else {
            nat_invmod(&w, &q.p)
        };
        let masked_num = self.int_mul(num, &rho)?;
        let (kq, most) = Self::lift(&masked_num, q);
        let bits = self.normalize(&masked_num, &kq, nat_bitlen(&most))?;
        self.reduce_bits(bits, most, q, Some(&inverse))
    }

    /// `N / q` for an integer `N` that `q` divides, with the quotient below `2^bits`.
    fn exact_quotient(
        &mut self,
        num: &Int<B::S>,
        q: &Modulus,
        bits: usize,
    ) -> Result<Vec<B::S>, WitgenError> {
        if bits > 56 {
            return Err(WitgenError::Unsupported { index: usize::MAX });
        }
        let low = self.normalize(num, &[], bits)?;
        // q^-1 mod 2^64 by Newton's iteration.
        let q0 = q.p[0];
        let mut inverse = q0;
        for _ in 0..6 {
            inverse = inverse.wrapping_mul(2u64.wrapping_sub(q0.wrapping_mul(inverse)));
        }
        let mask = (1u64 << bits) - 1;
        let (mut sum, mut most) = (self.zero, 0u128);
        for (i, &bit) in low.iter().enumerate() {
            let weight = (inverse << i) & mask;
            sum = sum + B::scale(bit, F::from_u64_reduced(weight));
            most += u128::from(weight);
        }
        let mut out = self.decompose(sum, 128 - most.leading_zeros())?;
        out.resize(bits, self.zero);
        Ok(out)
    }

    /// The inverse of `x`, or zero; `x` lies in `[0, max]`.
    fn inverse_or_zero(&mut self, x: B::S, max: usize) -> Result<B::S, WitgenError> {
        let mut powers = vec![self.one, x];
        while powers.len() <= max {
            let have = powers.len();
            let upto = (2 * have - 1).min(max + 1);
            let xs: Vec<B::S> = (have..upto).map(|k| powers[k / 2]).collect();
            let ys: Vec<B::S> = (have..upto).map(|k| powers[k - k / 2]).collect();
            powers.extend(self.mul(&xs, &ys)?);
        }
        let zero = self.zero;
        let matrix = self.matrix(max + 1);
        Ok((1..=max).fold(zero, |acc, k| {
            let coefficient = (1..=max).fold(F::ZERO, |c, j| {
                c + matrix[k][j] * F::from_u64_reduced(j as u64).inv()
            });
            acc + B::scale(powers[k], coefficient)
        }))
    }

    fn source(
        &mut self,
        z: &[B::S],
        source: &Source,
        input: Option<&Vec<B::S>>,
    ) -> Result<Vec<B::S>, WitgenError> {
        let unsupported = WitgenError::Unsupported { index: usize::MAX };
        match source {
            Source::Input { bits } => match input {
                Some(shares) if shares.len() == *bits as usize => Ok(shares.clone()),
                _ => Err(WitgenError::Inputs),
            },
            Source::PolyProduct { a, b } => {
                let a: Vec<B::S> = a.iter().map(|lc| self.eval(z, lc)).collect();
                let b: Vec<B::S> = b.iter().map(|lc| self.eval(z, lc)).collect();
                self.poly_mul(&a, &b)
            }
            Source::Form { lc, bits } => {
                if *bits > 64 {
                    return Err(unsupported);
                }
                let x = self.eval(z, lc);
                self.decompose(x, *bits)
            }
            Source::Integer {
                products,
                linear,
                bits,
            } => {
                let x = self.int_expr(z, products, linear)?;
                self.normalize(&x, &[], *bits as usize)
            }
            Source::Residue {
                products,
                linear,
                den,
                modulus,
            } => {
                let q = Modulus::new(modulus);
                let num = self.int_expr(z, products, linear)?;
                if den.is_empty() {
                    self.canonical(&num, &q)
                } else {
                    let den = self.int_of(z, den);
                    self.quotient_mod(&num, &den, &q)
                }
            }
            Source::Quotient { num, divisor, bits } => {
                let q = Modulus::new(divisor);
                let num = self.int_of(z, num);
                self.exact_quotient(&num, &q, *bits as usize)
            }
        }
    }

    /// Shares of the assignment of `shape`, whose variables are defined by `defs`.
    /// `inputs[k]` holds the bit shares of the relation's `k`-th input source. The masking
    /// variables are left zero.
    pub fn run(
        &mut self,
        shape: &Shape,
        defs: &Definitions,
        public_inputs: &[F],
        inputs: &[Vec<B::S>],
    ) -> Result<Vec<B::S>, WitgenError> {
        let unsupported = |index: usize| WitgenError::Unsupported { index };
        if defs.vars.len() != shape.num_vars || public_inputs.len() != shape.num_public {
            return Err(unsupported(0));
        }
        let max_var = |lc: &Lc| {
            lc.terms()
                .iter()
                .map(|&(v, _)| v as usize)
                .max()
                .unwrap_or(0)
        };
        let mut z = vec![self.zero; shape.num_vars];
        z[0] = self.one;
        for (slot, &v) in z[1..].iter_mut().zip(public_inputs) {
            *slot = self.b.public(v);
        }
        let mut sources: Vec<Option<Vec<B::S>>> = vec![None; defs.sources.len()];
        let mut next_input = 0;
        let stop = shape.mask_var_base;
        let mut i = 1 + shape.num_public;
        while i < stop {
            if self.unchecked >= CHECK_EVERY {
                self.check()?;
            }
            match &defs.vars[i] {
                Def::Product(..) => {
                    let (mut xs, mut ys) = (Vec::new(), Vec::new());
                    let mut end = i;
                    while end < stop {
                        match &defs.vars[end] {
                            Def::Product(a, b) if max_var(a) < i && max_var(b) < i => {
                                xs.push(self.eval(&z, a));
                                ys.push(self.eval(&z, b));
                                end += 1;
                            }
                            _ => break,
                        }
                    }
                    if end == i {
                        return Err(unsupported(i));
                    }
                    let products = self.mul(&xs, &ys)?;
                    z[i..end].copy_from_slice(&products);
                    i = end;
                    continue;
                }
                Def::Ratio { .. } => {
                    let mut run = Vec::new();
                    let mut end = i;
                    while end < stop {
                        match &defs.vars[end] {
                            Def::Ratio {
                                num,
                                den,
                                minus,
                                scale,
                            } if [num, den, minus].iter().all(|lc| max_var(lc) < i) => {
                                run.push((
                                    self.eval(&z, num),
                                    self.eval(&z, den),
                                    self.eval(&z, minus),
                                    *scale,
                                ));
                                end += 1;
                            }
                            _ => break,
                        }
                    }
                    if end == i {
                        return Err(unsupported(i));
                    }
                    let n = run.len();
                    let masks: Vec<B::S> =
                        (0..n).map(|_| self.b.random()).collect::<Result<_, _>>()?;
                    let mut xs: Vec<B::S> = run.iter().map(|r| r.1).collect();
                    xs.extend(run.iter().map(|r| r.0));
                    let ys: Vec<B::S> = masks.iter().chain(&masks).copied().collect();
                    let masked = self.mul(&xs, &ys)?;
                    // A denominator can only be what the definitions say once every
                    // earlier opening is known to be right.
                    self.check()?;
                    let opened = self.open(&masked[..n])?;
                    for (k, r) in run.iter().enumerate() {
                        let inverse = if self.b.counting() {
                            F::ONE
                        } else if opened[k] == F::ZERO {
                            return Err(WitgenError::ZeroDenominator);
                        } else {
                            opened[k].inv()
                        };
                        z[i + k] = B::scale(masked[n + k], inverse * r.3) - B::scale(r.2, r.3);
                    }
                    i = end;
                    continue;
                }
                Def::SumOfProducts { base, products } => {
                    let xs: Vec<B::S> = products.iter().map(|(a, _)| self.eval(&z, a)).collect();
                    let ys: Vec<B::S> = products.iter().map(|(_, b)| self.eval(&z, b)).collect();
                    let terms = self.mul(&xs, &ys)?;
                    z[i] = terms.iter().fold(self.eval(&z, base), |acc, &t| acc + t);
                }
                Def::Power7(a) => {
                    let a = self.eval(&z, a);
                    let a2 = self.mul1(a, a)?;
                    let a4 = self.mul1(a2, a2)?;
                    let a6 = self.mul1(a4, a2)?;
                    z[i] = self.mul1(a6, a)?;
                }
                Def::InverseOrZero { of, max } => {
                    let x = self.eval(&z, of);
                    z[i] = self.inverse_or_zero(x, *max as usize)?;
                }
                Def::Coefficient { product: id, index } => {
                    let id = id.index();
                    if id >= sources.len() {
                        return Err(unsupported(i));
                    }
                    if sources[id].is_none() {
                        sources[id] = Some(self.source(&z, &defs.sources[id], None)?);
                    }
                    z[i] = *sources[id]
                        .as_ref()
                        .and_then(|c| c.get(*index as usize))
                        .ok_or(unsupported(i))?;
                }
                Def::Bits {
                    source: id,
                    lo,
                    width,
                } => {
                    let id = id.index();
                    if id >= sources.len() {
                        return Err(unsupported(i));
                    }
                    if sources[id].is_none() {
                        let input = match &defs.sources[id] {
                            Source::Input { .. } => {
                                next_input += 1;
                                inputs.get(next_input - 1)
                            }
                            _ => None,
                        };
                        sources[id] = Some(self.source(&z, &defs.sources[id], input)?);
                    }
                    let bits = sources[id].as_ref().expect("just computed");
                    z[i] = (0..*width as usize).fold(self.zero, |acc, t| {
                        match bits.get(*lo as usize + t) {
                            Some(&b) => acc + B::scale(b, pow2(t)),
                            None => acc,
                        }
                    });
                }
                Def::Undefined | Def::One | Def::Public | Def::Mask => {
                    return Err(unsupported(i));
                }
            }
            i += 1;
        }
        if next_input != inputs.len() {
            return Err(WitgenError::Inputs);
        }
        self.check()?;
        Ok(z)
    }
}

/// Bit counts of the relation's input sources, in the order [`generate`] takes them.
pub fn input_bits(defs: &Definitions) -> Vec<usize> {
    defs.sources
        .iter()
        .filter_map(|s| match s {
            Source::Input { bits } => Some(*bits as usize),
            _ => None,
        })
        .collect()
}

/// What one custodian's [`generate`] consumes at most: triples, uniform values, and the
/// counts of opened values, rounds and MAC checks.
pub fn demand(shape: &Shape, defs: &Definitions) -> Result<Count, WitgenError> {
    let mut count = Count::default();
    let inputs: Vec<Vec<Unit>> = input_bits(defs)
        .into_iter()
        .map(|bits| vec![Unit; bits])
        .collect();
    let public = vec![F::ZERO; shape.num_public];
    Witgen::new(&mut count).run(shape, defs, &public, &inputs)?;
    Ok(count)
}

/// One custodian's side of witness generation: authenticated shares of the assignment of
/// `shape` from authenticated shares of the bits of its inputs.
pub fn generate<T: Transport>(
    e: &mut Engine<T>,
    shape: &Shape,
    defs: &Definitions,
    public_inputs: &[F],
    inputs: &[Vec<Sb>],
) -> Result<Vec<Sb>, WitgenError> {
    Witgen::new(e).run(shape, defs, public_inputs, inputs)
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use dregg_sig_agg::zk_hem::SeedStream;

    /// The clear reference: the same code on plain field values.
    pub(in super::super) struct Plain {
        stream: SeedStream,
        pub count: Count,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(in super::super) struct Clear(pub F);

    impl Add for Clear {
        type Output = Clear;
        fn add(self, r: Clear) -> Clear {
            Clear(self.0 + r.0)
        }
    }

    impl Sub for Clear {
        type Output = Clear;
        fn sub(self, r: Clear) -> Clear {
            Clear(self.0 - r.0)
        }
    }

    impl Plain {
        pub(in super::super) fn new(tag: u8) -> Self {
            Self {
                stream: SeedStream::new(b"DREGG.TEST.WITGEN", &[tag; 32]),
                count: Count::default(),
            }
        }
    }

    impl Backend for Plain {
        type S = Clear;
        fn scale(s: Clear, k: F) -> Clear {
            Clear(s.0 * k)
        }
        fn public(&self, c: F) -> Clear {
            Clear(c)
        }
        fn random(&mut self) -> Result<Clear, MpcError> {
            self.count.randoms += 1;
            Ok(Clear(self.stream.next_base()))
        }
        fn mul(&mut self, xs: &[Clear], ys: &[Clear]) -> Result<Vec<Clear>, MpcError> {
            self.count.triples += xs.len();
            Ok(xs.iter().zip(ys).map(|(x, y)| Clear(x.0 * y.0)).collect())
        }
        fn open(&mut self, xs: &[Clear]) -> Result<Vec<F>, MpcError> {
            Ok(xs.iter().map(|x| x.0).collect())
        }
        fn check(&mut self) -> Result<(), MpcError> {
            Ok(())
        }
    }

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    fn value(bits: &[Clear]) -> Nat {
        let mut out = vec![0u64; bits.len() / 64 + 1];
        for (i, b) in bits.iter().enumerate() {
            let v = b.0.to_canonical_u64();
            assert!(v <= 1, "bit {i} is {v}");
            out[i / 64] |= v << (i % 64);
        }
        nat_trim(out)
    }

    const SECP_P: [u8; 32] = {
        let mut p = [0xff; 32];
        p[0] = 0x2f;
        p[1] = 0xfc;
        p[4] = 0xfe;
        p
    };
    const ED_P: [u8; 32] = {
        let mut p = [0xff; 32];
        p[0] = 0xed;
        p[31] = 0x7f;
        p
    };

    #[test]
    fn public_integer_arithmetic_and_square_roots() {
        let mut s = SeedStream::new(b"DREGG.TEST.WITGEN", &[1; 32]);
        for _ in 0..200 {
            let a = s.next_base();
            if a != F::ZERO {
                let r = sqrt(a * a).unwrap();
                assert!(r == a || r == F::ZERO - a);
                assert_eq!(sqrt(a * a), sqrt((F::ZERO - a) * (F::ZERO - a)));
                // 7 generates the group, so 7 a^2 is not a square.
                assert_eq!(sqrt(f(7) * a * a), None);
            }
        }
        for p in [SECP_P, ED_P] {
            let q = Modulus::new(&p);
            let mut back = vec![0u64; 6];
            for &(pos, d) in &q.digits {
                nat_add_signed(&mut back, i128::from(d), pos);
            }
            assert_eq!(nat_trim(back), q.p);
            for _ in 0..5 {
                let a: Nat = (0..4).map(|_| s.next_base().to_canonical_u64()).collect();
                let a = nat_divrem(&a, &q.p).1;
                let inverse = nat_invmod(&a, &q.p);
                assert_eq!(nat_mulmod(&a, &inverse, &q.p), vec![1]);
                let (quotient, rest) = nat_divrem(&nat_mul(&a, &a), &q.p);
                assert_eq!(nat_add(&nat_mul(&quotient, &q.p), &rest), nat_mul(&a, &a));
            }
        }
        let m = interpolation_matrix(5);
        // 3 t^4 - t + 7 at 0..5, back to its coefficients.
        let values: Vec<F> = (0..5u64).map(|t| f(3 * t.pow(4) + 7) - f(t)).collect();
        let coefficients: Vec<F> = m
            .iter()
            .map(|row| {
                row.iter()
                    .zip(&values)
                    .fold(F::ZERO, |a, (&k, &v)| a + k * v)
            })
            .collect();
        assert_eq!(
            coefficients,
            [f(7), F::ZERO - F::ONE, F::ZERO, F::ZERO, f(3)]
        );
    }

    #[test]
    fn decomposition_is_exact_at_every_width_and_boundary() {
        let mut plain = Plain::new(2);
        let mut s = SeedStream::new(b"DREGG.TEST.WITGEN", &[3; 32]);
        let mut w = Witgen::new(&mut plain);
        for m in [1u32, 2, 8, 22, 23, 31, 32, 33, 40, 63, 64] {
            let top = if m == 64 {
                0xFFFF_FFFF_0000_0000
            } else {
                (1u64 << m) - 1
            };
            let mut cases = vec![0, 1, top, top - 1, top / 2];
            cases.extend((0..12).map(|_| s.next_base().to_canonical_u64() & top));
            for x in cases {
                let x = x.min(top);
                let bits = w.decompose(Clear(f(x)), m).unwrap();
                assert_eq!(bits.len(), m as usize);
                assert_eq!(value(&bits), nat_trim(vec![x]), "m={m} x={x}");
            }
        }
        // The counter is an upper bound on what a real run uses.
        let used = w.b.count;
        let mut count = Count::default();
        let mut c = Witgen::new(&mut count);
        for m in [1u32, 2, 8, 22, 23, 31, 32, 33, 40, 63, 64] {
            for _ in 0..17 {
                c.decompose(Unit, m).unwrap();
            }
        }
        assert!(count.triples >= used.triples && count.triples <= used.triples + used.triples / 4);
        assert!(count.randoms <= used.randoms && count.randoms + 64 * 8 >= used.randoms);
    }

    fn int(values: &[i128], lo: i128, hi: i128) -> Int<Clear> {
        Int {
            c: values.iter().map(|&v| Clear(f_signed(v))).collect(),
            lo: vec![lo; values.len()],
            hi: vec![hi; values.len()],
        }
    }

    fn int_value(values: &[i128]) -> (Nat, Nat) {
        let mut pos = vec![0u64; values.len() / 8 + 4];
        let mut neg = pos.clone();
        for (k, &v) in values.iter().enumerate() {
            nat_add_signed(if v < 0 { &mut neg } else { &mut pos }, v.abs(), k);
        }
        (nat_trim(pos), nat_trim(neg))
    }

    #[test]
    fn residues_quotients_and_inverses_match_public_arithmetic() {
        let mut s = SeedStream::new(b"DREGG.TEST.WITGEN", &[4; 32]);
        let mut plain = Plain::new(5);
        let mut w = Witgen::new(&mut plain);
        let mut limbs = |n: usize, lo: i128, hi: i128| -> Vec<i128> {
            (0..n)
                .map(|_| lo + (s.next_base().to_canonical_u64() as i128) % (hi - lo + 1))
                .collect()
        };
        for p in [SECP_P, ED_P] {
            let q = Modulus::new(&p);
            for round in 0..3 {
                // A product of two integers minus a third, with signed wide coefficients.
                let (a, b) = (limbs(32, 0, 255), limbs(32, -255, 255));
                let c = limbs(40, -(1 << 40), 1 << 40);
                let (ia, ib, ic) = (
                    int(&a, 0, 255),
                    int(&b, -255, 255),
                    int(&c, -(1 << 40), 1 << 40),
                );
                let product = w.int_mul(&ia, &ib).unwrap();
                let x = w.int_add(&product, &ic);
                let (ap, an) = int_value(&a);
                let (bp, bn) = int_value(&b);
                let (cp, cn) = int_value(&c);
                let reduce = |pos: &Nat, neg: &Nat| {
                    let (pos, neg) = (nat_divrem(pos, &q.p).1, nat_divrem(neg, &q.p).1);
                    nat_divrem(&nat_sub(&nat_add(&pos, &q.p), &neg), &q.p).1
                };
                let (am, bm, cm) = (reduce(&ap, &an), reduce(&bp, &bn), reduce(&cp, &cn));
                let want = nat_divrem(&nat_add(&nat_mulmod(&am, &bm, &q.p), &cm), &q.p).1;
                let got = w.canonical(&x, &q).unwrap();
                assert_eq!(got.len(), q.bits);
                assert_eq!(value(&got), want, "residue, round {round}");

                // The same over a denominator.
                let d = limbs(32, -255, 255);
                let id = int(&d, -255, 255);
                let (dp, dn) = int_value(&d);
                let dm = reduce(&dp, &dn);
                let got = w.quotient_mod(&x, &id, &q).unwrap();
                assert_eq!(
                    value(&got),
                    nat_mulmod(&want, &nat_invmod(&dm, &q.p), &q.p),
                    "quotient, round {round}"
                );
            }
            // A zero denominator is refused.
            let zero = int(&[0; 32], -255, 255);
            let one = int(&[1], 0, 255);
            assert_eq!(
                w.quotient_mod(&one, &zero, &q).err(),
                Some(WitgenError::ZeroDenominator)
            );

            // Exact division: N = Q q with Q < 2^27, coefficients shifted off their digits.
            let quotient = 0x5a5_1234u64;
            let n = nat_mul(&[quotient], &q.p);
            let mut coefficients: Vec<i128> = (0..36).map(|k| nat_byte(&n, k) as i128).collect();
            coefficients[0] += 256 * 1000;
            coefficients[1] -= 1000;
            coefficients[2] -= 256 * 77;
            coefficients[3] += 77;
            let num = int(&coefficients, -(1 << 20), 1 << 20);
            let got = w.exact_quotient(&num, &q, 27).unwrap();
            assert_eq!(value(&got), vec![quotient]);
        }
        for max in [1usize, 2, 5, 40] {
            for x in 0..=max as u64 {
                let got = w.inverse_or_zero(Clear(f(x)), max).unwrap();
                assert_eq!(got.0, f(x).inv_or_zero(), "max={max} x={x}");
            }
        }
    }

    use crate::hem::relations::{
        Bip32Root, Ed25519ExtendedKey, KeySource, Lock, OwnershipStatement, OwnershipWitness,
        PathSpec, bip32_derive, ownership_auxiliary_inputs, ownership_definitions,
        ownership_shape, synthesize_ownership,
    };

    fn statement(lock: Lock, source: KeySource, witness: &OwnershipWitness) -> OwnershipStatement {
        OwnershipStatement::derive(lock, source, witness, [5; 32], [6; 32], 9)
            .expect("a witness for the statement")
    }

    /// The property a threshold prover needs of a relation: no variable without a
    /// definition, and the recorded relation is the one the verifier builds.
    #[test]
    fn every_ownership_statement_defines_every_variable() {
        const H: u32 = 1 << 31;
        let key = OwnershipWitness::secp256k1_key(&[0x11; 32]);
        let mut extended = [0u8; 96];
        extended[0] = 8;
        extended[31] = 0x40;
        extended[40] = 3;
        let mut cases = vec![
            statement(Lock::P2pkhUncompressed, KeySource::Secp256k1Key, &key),
            statement(Lock::P2shP2wpkh, KeySource::Secp256k1Key, &key),
            statement(Lock::Ethereum, KeySource::Secp256k1Key, &key),
            statement(Lock::TaprootKeyPath, KeySource::Secp256k1Key, &key),
            statement(
                Lock::TaprootScriptTree,
                KeySource::Secp256k1Key,
                &OwnershipWitness::secp256k1_key(&[0x11; 32]).with_merkle_root([3; 32]),
            ),
            statement(
                Lock::BlsWithdrawal,
                KeySource::Bls12381Key,
                &OwnershipWitness::bls12_381_key(&[0x13; 32]),
            ),
            statement(
                Lock::P2pkh,
                KeySource::Bip32 {
                    root: Bip32Root::Seed,
                    path: PathSpec::Public(vec![H, 1]),
                },
                &OwnershipWitness::seed(&[7; 16]),
            ),
            statement(
                Lock::P2pkh,
                KeySource::Bip32 {
                    root: Bip32Root::Seed,
                    path: PathSpec::Hidden { max_depth: 1 },
                },
                &OwnershipWitness::seed(&[7; 16]).with_path(&[H + 2]),
            ),
            statement(
                Lock::Ed25519,
                KeySource::Slip10 {
                    path: PathSpec::Public(vec![H]),
                },
                &OwnershipWitness::seed(&[7; 16]),
            ),
            statement(
                Lock::Ed25519,
                KeySource::Bip32Ed25519 { path: vec![1] },
                &OwnershipWitness::ed25519_extended_key(&Ed25519ExtendedKey(extended)),
            ),
        ];
        cases.extend(reference_cases().into_iter().map(|(st, _, _)| st));
        for st in &cases {
            let (shape, defs) = ownership_definitions(st).unwrap();
            assert_eq!(shape.digest(), ownership_shape(st).unwrap().digest());
            assert_eq!(defs.vars.len(), shape.num_vars);
            assert_eq!(
                defs.undefined(),
                Vec::<usize>::new(),
                "{:?} {:?}",
                st.lock,
                st.source
            );
            assert!(matches!(defs.sources.first(), Some(Source::Input { .. })));
        }
    }

    /// The two statements the threshold prover is exercised on, with their witness and
    /// the witness secret.
    pub(in super::super) fn reference_cases() -> Vec<(OwnershipStatement, OwnershipWitness, Vec<u8>)>
    {
        let key = OwnershipWitness::secp256k1_key(&[0x11; 32]);
        let seed = OwnershipWitness::ed25519_seed(&[0x22; 32]);
        vec![
            (
                statement(Lock::P2pkh, KeySource::Secp256k1Key, &key),
                key,
                vec![0x11; 32],
            ),
            (
                statement(Lock::Ed25519, KeySource::Ed25519Seed, &seed),
                seed,
                vec![0x22; 32],
            ),
        ]
    }

    /// Statements whose relation takes inputs besides the secret, with their witness, the
    /// secret, the hidden path and the script-tree root: a master seed with a public
    /// path (`m/44'`), a longer seed with a hidden path under a Taproot script tree, a
    /// SLIP-0010 seed with a hidden path, and an extended key with a hidden public step.
    #[allow(clippy::type_complexity)]
    pub(in super::super) fn derived_cases() -> Vec<(
        OwnershipStatement,
        OwnershipWitness,
        Vec<u8>,
        Vec<u32>,
        Option<[u8; 32]>,
    )> {
        const H: u32 = 1 << 31;
        let mut out = Vec::new();
        let seed = vec![0x31; 16];
        let witness = OwnershipWitness::seed(&seed);
        let source = KeySource::Bip32 {
            root: Bip32Root::Seed,
            path: PathSpec::Public(vec![H + 44]),
        };
        out.push((
            statement(Lock::P2pkh, source, &witness),
            witness,
            seed,
            Vec::new(),
            None,
        ));
        let seed: Vec<u8> = (0..33).map(|i| 0x40 + i as u8).collect();
        let (path, root) = (vec![H + 86], [0x5a; 32]);
        let witness = OwnershipWitness::seed(&seed)
            .with_path(&path)
            .with_merkle_root(root);
        let source = KeySource::Bip32 {
            root: Bip32Root::Seed,
            path: PathSpec::Hidden { max_depth: 2 },
        };
        out.push((
            statement(Lock::TaprootScriptTree, source, &witness),
            witness,
            seed,
            path,
            Some(root),
        ));
        let seed = vec![0x77; 64];
        let path = vec![H + 5];
        let witness = OwnershipWitness::seed(&seed).with_path(&path);
        let source = KeySource::Slip10 {
            path: PathSpec::Hidden { max_depth: 1 },
        };
        out.push((
            statement(Lock::Ed25519, source, &witness),
            witness,
            seed,
            path,
            None,
        ));
        let node = bip32_derive(&[0x21; 32], &[H]).unwrap();
        let secret = [node.private_key, node.chain_code].concat();
        let path = vec![7];
        let witness = OwnershipWitness::extended_key(&node).with_path(&path);
        let source = KeySource::Bip32 {
            root: Bip32Root::ExtendedKey,
            path: PathSpec::Hidden { max_depth: 1 },
        };
        out.push((
            statement(Lock::P2pkh, source, &witness),
            witness,
            secret,
            path,
            None,
        ));
        out
    }

    /// The inputs of a relation as plain values: the secret padded to the first input's
    /// width, then the auxiliary inputs.
    fn clear_inputs(defs: &Definitions, secret: &[u8], auxiliary: &[Vec<bool>]) -> Vec<Vec<Clear>> {
        let widths = input_bits(defs);
        assert_eq!(widths.len(), 1 + auxiliary.len());
        assert!(widths[0] >= 8 * secret.len());
        let mut first: Vec<Clear> = (0..8 * secret.len())
            .map(|i| Clear(f(u64::from((secret[i / 8] >> (i % 8)) & 1))))
            .collect();
        first.resize(widths[0], Clear(F::ZERO));
        let mut out = vec![first];
        for (bits, &width) in auxiliary.iter().zip(&widths[1..]) {
            assert_eq!(bits.len(), width);
            out.push(bits.iter().map(|&b| Clear(f(u64::from(b)))).collect());
        }
        out
    }

    /// Seeds of hidden length, hidden paths and script-tree roots: the auxiliary inputs
    /// are the ones the gadgets allocate, in their order, so the definitions evaluated on
    /// the secret and those inputs give the gadget's assignment.
    #[test]
    fn auxiliary_inputs_reproduce_the_gadget_assignment() {
        const H: u32 = 1 << 31;
        for (st, witness, secret, path, root) in derived_cases() {
            let (shape, assignment) = synthesize_ownership(&st, &witness).unwrap();
            let (recorded, defs) = ownership_definitions(&st).unwrap();
            assert_eq!(recorded.digest(), shape.digest());
            let auxiliary =
                ownership_auxiliary_inputs(&st, secret.len(), &path, root.as_ref()).unwrap();
            let inputs = clear_inputs(&defs, &secret, &auxiliary);
            let run = |inputs: &[Vec<Clear>]| {
                Witgen::new(&mut Plain::new(6)).run(
                    &shape,
                    &defs,
                    &st.public_inputs().unwrap(),
                    inputs,
                )
            };
            let z = run(&inputs).unwrap();
            let wrong = (0..shape.mask_var_base).find(|&i| z[i].0 != assignment[i]);
            assert_eq!(wrong.map(|i| (i, defs.vars[i].clone())), None, "{:?}", st.source);

            // The auxiliary inputs matter: flipping the first or the last of them moves
            // the assignment (or leaves the relation without one).
            for k in [1, inputs.len() - 1] {
                let mut other = inputs.clone();
                other[k][0] = Clear(F::ONE - other[k][0].0);
                assert!(run(&other).map_or(true, |o| o != z), "input {k}");
            }

            // What does not fit the statement is refused.
            let aux = |bytes: usize, path: &[u32], root: Option<&[u8; 32]>| {
                ownership_auxiliary_inputs(&st, bytes, path, root)
            };
            assert_eq!(aux(secret.len(), &path, root.as_ref()), Some(auxiliary));
            assert_eq!(aux(15, &path, root.as_ref()), None);
            assert_eq!(aux(65, &path, root.as_ref()), None);
            let long = [path.clone(), vec![H, H, H]].concat();
            assert_eq!(aux(secret.len(), &long, root.as_ref()), None);
            let flipped = if root.is_some() { None } else { Some(&[1u8; 32]) };
            assert_eq!(aux(secret.len(), &path, flipped), None);
        }
        // A SLIP-0010 path has hardened steps only.
        let (st, _, secret, _, _) = derived_cases().swap_remove(2);
        assert_eq!(ownership_auxiliary_inputs(&st, secret.len(), &[5], None), None);
    }

    /// The definitions mean what the gadgets compute: evaluated on plain values from the
    /// secret alone they give the gadget's assignment, variable for variable.
    #[test]
    fn definitions_reproduce_the_gadget_assignment() {
        for (st, witness, secret) in reference_cases() {
            let (shape, assignment) = synthesize_ownership(&st, &witness).unwrap();
            let (recorded, defs) = ownership_definitions(&st).unwrap();
            assert_eq!(recorded.digest(), shape.digest());
            assert_eq!(input_bits(&defs), [8 * secret.len()]);
            let bits: Vec<Clear> = (0..8 * secret.len())
                .map(|i| Clear(f(u64::from((secret[i / 8] >> (i % 8)) & 1))))
                .collect();
            let mut plain = Plain::new(6);
            let z = Witgen::new(&mut plain)
                .run(
                    &shape,
                    &defs,
                    &st.public_inputs().unwrap(),
                    core::slice::from_ref(&bits),
                )
                .unwrap();
            let wrong = (0..shape.mask_var_base).find(|&i| z[i].0 != assignment[i]);
            assert_eq!(wrong.map(|i| (i, defs.vars[i].clone())), None);
            let bound = demand(&shape, &defs).unwrap();
            std::println!(
                "{:?}: vars={} used triples={} randoms={}; bound triples={} randoms={} rounds={} checks={}",
                st.lock,
                shape.num_vars,
                plain.count.triples,
                plain.count.randoms,
                bound.triples,
                bound.randoms,
                bound.rounds,
                bound.checks,
            );
            assert!(bound.triples >= plain.count.triples && bound.randoms >= plain.count.randoms);
            assert!(bound.triples <= plain.count.triples + plain.count.triples / 8);

            // A wrong input bit gives a different assignment, and too few inputs are refused.
            let mut flipped = bits.clone();
            flipped[3] = Clear(F::ONE - flipped[3].0);
            let other = Witgen::new(&mut Plain::new(6)).run(
                &shape,
                &defs,
                &st.public_inputs().unwrap(),
                &[flipped],
            );
            assert!(other.map_or(true, |o| o != z));
            assert_eq!(
                Witgen::new(&mut Plain::new(6))
                    .run(
                        &shape,
                        &defs,
                        &st.public_inputs().unwrap(),
                        &[bits[1..].to_vec()]
                    )
                    .err(),
                Some(WitgenError::Inputs)
            );
        }
    }

    use super::super::engine::{Dealer, Engine, Preprocessing};
    use super::super::net::{ChannelLink, Framed, NetError, channel_mesh};
    use crate::hem::curve::{Lazy, Modulus as CurveModulus};
    use crate::hem::hash::{add_wide, alloc_bits, maj, pack_bits, xor3};
    use dregg_sig_agg::zk_hem::relation::ConstraintSystem;

    /// A relation over a 4-byte secret that uses the hash and curve gadgets: Boolean
    /// functions, a wide addition, and a product modulo the secp256k1 base prime.
    fn small_recorded(secret: &[u8; 4]) -> (Shape, Vec<F>, Definitions) {
        let mut cs = ConstraintSystem::new_recording();
        let public: Lc = cs
            .public_input(f(u64::from(secret[0]) * u64::from(secret[1])))
            .into();
        let bits = alloc_bits(&mut cs, secret);
        let product = cs.mul(&pack_bits(&bits[..8]), &pack_bits(&bits[8..16]));
        cs.enforce_equal(&product.into(), &public);
        let sum = add_wide(&mut cs, &bits[..16], &bits[16..]);
        let mixed: Vec<Lc> = (0..16)
            .map(|i| {
                let x = xor3(&mut cs, &bits[i], &bits[i + 16], &sum[i]);
                maj(&mut cs, &x, &bits[i], &sum[i])
            })
            .collect();
        let field = CurveModulus::secp256k1_base();
        let reduced = field.mul(&mut cs, &Lazy::from_bits(&bits), &Lazy::from_bits(&mixed));
        field.enforce_canonical(&mut cs, &reduced);
        cs.finish_recorded()
    }

    /// A transport that flips one bit of its `at`-th outgoing message.
    struct Faulty<T> {
        inner: T,
        sent: usize,
        at: usize,
    }

    impl<T: Transport> Transport for Faulty<T> {
        fn parties(&self) -> usize {
            self.inner.parties()
        }
        fn me(&self) -> usize {
            self.inner.me()
        }
        fn send(&mut self, to: usize, payload: &[u8]) -> Result<(), NetError> {
            self.sent += 1;
            if self.sent - 1 == self.at && !payload.is_empty() {
                let mut wrong = payload.to_vec();
                wrong[0] ^= 1;
                return self.inner.send(to, &wrong);
            }
            self.inner.send(to, payload)
        }
        fn recv(&mut self, from: usize) -> Result<Vec<u8>, NetError> {
            self.inner.recv(from)
        }
    }

    /// Every custodian on its own thread; custodian 1 flips a bit of its `fault`-th
    /// message. Returns each custodian's result with its round count.
    fn run_engines<R: Send>(
        preps: Vec<Preprocessing>,
        fault: Option<usize>,
        party: impl Fn(&mut Engine<Faulty<Framed<ChannelLink>>>) -> R + Sync,
    ) -> Vec<(R, u64)> {
        let session = [4u8; 32];
        let mesh = channel_mesh(session, preps.len());
        std::thread::scope(|scope| {
            let handles: Vec<_> = mesh
                .into_iter()
                .zip(preps)
                .enumerate()
                .map(|(p, (net, prep))| {
                    let party = &party;
                    scope.spawn(move || {
                        let net = Faulty {
                            inner: net,
                            sent: 0,
                            at: fault.filter(|_| p == 1).unwrap_or(usize::MAX),
                        };
                        let mut e = Engine::new(net, prep, &session, &[p as u8 + 50; 32]);
                        let out = party(&mut e);
                        (out, e.stats.rounds)
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    }

    fn deal_bits(dealer: &mut Dealer, parties: usize, secret: &[u8]) -> Vec<Vec<Sb>> {
        let mut out = vec![Vec::new(); parties];
        for i in 0..8 * secret.len() {
            let bit = f(u64::from((secret[i / 8] >> (i % 8)) & 1));
            for (p, s) in dealer.share(bit).into_iter().enumerate() {
                out[p].push(s);
            }
        }
        out
    }

    #[test]
    fn custodians_compute_the_assignment_on_shares() {
        let secret = [0xa7, 0x3c, 0xf1, 0x5e];
        let (shape, assignment, defs) = small_recorded(&secret);
        assert!(shape.is_satisfied(&assignment));
        assert_eq!(defs.undefined(), Vec::<usize>::new());
        let need = demand(&shape, &defs).unwrap();
        let publics = assignment[1..=shape.num_public].to_vec();
        for parties in [2usize, 3] {
            let mut dealer = Dealer::new(parties, &[parties as u8; 32]);
            let inputs = deal_bits(&mut dealer, parties, &secret);
            let preps = dealer.preprocessing(need.triples, need.randoms);
            let out = run_engines(preps, None, |e| {
                let z = generate(e, &shape, &defs, &publics, &[inputs[e.me()].clone()]).unwrap();
                assert_eq!(e.remaining(), (0, 0), "demand is exact");
                assert!(!e.has_pending());
                z
            });
            for i in 0..shape.mask_var_base {
                let value = out.iter().fold(F::ZERO, |acc, (z, _)| acc + z[i].v);
                assert_eq!(value, assignment[i], "variable {i}");
            }
            // A single custodian's shares of the secret's bits are not the bits.
            let first = 1 + shape.num_public;
            let own = (first..first + 32)
                .filter(|&i| out[1].0[i].v == assignment[i])
                .count();
            assert_eq!(own, 0);
        }
    }

    #[test]
    fn a_wrong_message_makes_every_honest_custodian_abort_at_the_same_point() {
        let need = {
            let (shape, _, defs) = small_recorded(&[1, 2, 3, 4]);
            demand(&shape, &defs).unwrap()
        };
        // Message indices of custodian 1 (two peers, so two sends a round) spread over
        // the run: random-bit squares, masked openings, Beaver openings, check rounds.
        let total = 2 * need.rounds;
        let mut aborted = 0;
        for at in [
            0,
            1,
            2,
            5,
            40,
            41,
            total / 7,
            total / 3,
            total / 2,
            total - total / 5,
        ] {
            let mut rounds = Vec::new();
            for secret in [[0xa7, 0x3c, 0xf1, 0x5e], [0x19, 0x80, 0x02, 0xff]] {
                let (shape, assignment, defs) = small_recorded(&secret);
                let publics = assignment[1..=shape.num_public].to_vec();
                let mut dealer = Dealer::new(3, &[7; 32]);
                let inputs = deal_bits(&mut dealer, 3, &secret);
                let preps = dealer.preprocessing(need.triples, need.randoms);
                let out = run_engines(preps, Some(at), |e| {
                    generate(e, &shape, &defs, &publics, &[inputs[e.me()].clone()]).map(|_| ())
                });
                for p in [0, 2] {
                    assert!(
                        matches!(out[p].0, Err(WitgenError::Mpc(_))),
                        "message {at}: custodian {p} got {:?}",
                        out[p].0
                    );
                }
                // The custodian that detects the fault first; the other may only see it
                // leave.
                let closed = |r: &Result<(), WitgenError>| {
                    matches!(r, Err(WitgenError::Mpc(MpcError::Net(_))))
                };
                let first = if closed(&out[0].0) || (!closed(&out[2].0) && out[2].1 < out[0].1) {
                    2
                } else {
                    0
                };
                assert!(!closed(&out[first].0));
                rounds.push((out[first].1, out[first].0));
            }
            // Where and how the fault is detected does not depend on the secret.
            assert_eq!(rounds[0], rounds[1], "message {at}");
            aborted += 1;
        }
        assert_eq!(aborted, 10);
    }

    #[test]
    fn a_wrong_input_share_is_caught_before_the_assignment_is_used() {
        let secret = [0xa7, 0x3c, 0xf1, 0x5e];
        let (shape, assignment, defs) = small_recorded(&secret);
        let need = demand(&shape, &defs).unwrap();
        let publics = assignment[1..=shape.num_public].to_vec();
        let mut dealer = Dealer::new(3, &[8; 32]);
        let inputs = deal_bits(&mut dealer, 3, &secret);
        let preps = dealer.preprocessing(need.triples, need.randoms);
        let out = run_engines(preps, None, |e| {
            let mut mine = inputs[e.me()].clone();
            if e.me() == 1 {
                // A different value under the old MAC share.
                mine[9].v += F::ONE;
            }
            generate(e, &shape, &defs, &publics, &[mine]).map(|_| ())
        });
        for (result, _) in &out {
            assert_eq!(*result, Err(WitgenError::Mpc(MpcError::MacCheck)));
        }
    }
}
