//! Non-native field arithmetic and fixed-base scalar multiplication for secp256k1 and
//! Ed25519 over the Goldilocks constraint system of `dregg_sig_agg::zk_hem::relation`.
//!
//! # Representation
//!
//! An integer is a polynomial in `t = 2^8` whose coefficients are linear forms, each with a
//! proven integer interval `[lo, hi]` (`Coef`). A fresh witness is 8-bit limbs, one row per
//! bit. Sums and differences are free and only widen the intervals. A product of two such
//! polynomials costs one row per coefficient (`mul_poly`): the coefficient variables are
//! fixed by evaluating both sides at as many points as there are coefficients.
//!
//! # Reduction and its overflow bound
//!
//! `x = 0 (mod p)` is proved as the integer identity `x + K p - q p = 0` with `q` a
//! bit-decomposed witness and `K` a public offset that makes `q` non-negative
//! (`enforce_zero_mod`). The identity is checked limb group by limb group with carries.
//! Every carry is range-checked to an interval derived from the coefficient intervals, and
//! the builder asserts, for every group equation, that the absolute value of its left side
//! over all admitted values is below the Goldilocks prime. A group equation that holds in
//! the field therefore holds over the integers. No step relies on a wrap not happening by
//! accident: if an interval is too wide, synthesis panics.
//!
//! # Scalar multiplication
//!
//! `[k]G = [2k]H` with `H = [1/2]G`. The low 252 scalar bits are cut into 21 windows of 12
//! bits. A window with value `u` contributes the odd multiple `(2u + 1 - 2^12) 2^lo` of `H`,
//! so its table holds 2^11 points and the top window bit selects the sign of `y`. The last
//! window (4 bits) is unsigned and carries the constant `2^252 - 1` that the signed windows
//! leave over. Every partial sum `S` of signed windows is an odd integer with
//! `|S| < 2^lo <= |T|` for the next addend `T`, and `|S| + |T| < 2^252 <` group order, so
//! `S != +-T` and neither is zero: the incomplete chord formula is exact there for every
//! Boolean input. The last addition can meet `S = T` or `S = -T`; it carries the extra
//! tangent-compatible equation of `add_step`, which makes doubling exact and leaves
//! `S = -T` (scalar `= 0 mod` order) unsatisfiable.
//!
//! The accumulator keeps `y` unreduced, as `lambda (x_T - x_3) - y_T`, so one addition
//! costs two reduced witnesses (`lambda`, `x_3`) and two quotients.
//!
//! A table lookup resolves the low 8 index bits through their 247 subset products, where
//! every table column is a linear form, and the high 3 bits by 7 rows per output. No table
//! entry is addressed by a witness value: the assignment is computed by evaluating those
//! forms.
//!
//! # Witness handling
//!
//! Native arithmetic on witness values is branch-free with fixed iteration counts. Its
//! stack temporaries are not erased. Without `std` the window tables (about 43,000 points
//! per curve) are rebuilt on every call.

use alloc::vec;
use alloc::vec::Vec;

use dregg_sig_agg::field::Goldilocks;
use dregg_sig_agg::zk_hem::relation::{ConstraintSystem, Lc};

type F = Goldilocks;
type U256 = [u64; 4];
const WIDE: usize = 9;
type Wide = [u64; WIDE];

/// The Goldilocks prime.
const PG: i128 = 0xFFFF_FFFF_0000_0001;
/// Largest absolute coefficient bound a polynomial may carry.
const COEF_BOUND: i128 = 1 << 62;
/// Signed windows are this wide; the table index is the low 11 bits.
const SIGNED_WINDOW: usize = 12;
/// Table index bits resolved by subset products; the rest select among sub-tables.
const LOW_INDEX_BITS: usize = 8;
/// A looked-up `y` is delivered in chunks of this many limbs.
const Y_CHUNK_LIMBS: usize = 6;
const SCALAR_BITS: usize = 256;

// ============================================================================
// Fixed-width integers (branch-free where a witness can reach them)
// ============================================================================

#[inline(always)]
fn adc(a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + c as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let t = (a as u128).wrapping_sub(b as u128 + borrow as u128);
    (t as u64, ((t >> 64) as u64) & 1)
}

#[inline(always)]
fn mac(acc: u64, a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = acc as u128 + (a as u128) * (b as u128) + c as u128;
    (t as u64, (t >> 64) as u64)
}

fn u256_add(a: &U256, b: &U256) -> (U256, u64) {
    let mut out = [0u64; 4];
    let mut c = 0;
    for i in 0..4 {
        (out[i], c) = adc(a[i], b[i], c);
    }
    (out, c)
}

fn u256_sub(a: &U256, b: &U256) -> (U256, u64) {
    let mut out = [0u64; 4];
    let mut c = 0;
    for i in 0..4 {
        (out[i], c) = sbb(a[i], b[i], c);
    }
    (out, c)
}

/// `a` where `mask` is all ones, `b` where it is zero.
#[inline(always)]
fn u256_select(mask: u64, a: &U256, b: &U256) -> U256 {
    core::array::from_fn(|i| (a[i] & mask) | (b[i] & !mask))
}

/// All ones if `a == 0`.
#[inline(always)]
fn u256_zero_mask(a: &U256) -> u64 {
    let or = a[0] | a[1] | a[2] | a[3];
    ((or | or.wrapping_neg()) >> 63).wrapping_sub(1)
}

fn u256_from_bytes(bytes: &[u8; 32]) -> U256 {
    core::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}

fn u256_to_bytes(a: &U256) -> [u8; 32] {
    let mut out = [0u8; 32];
    for i in 0..4 {
        out[8 * i..8 * i + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    out
}

fn u256_bitlen(a: &U256) -> usize {
    for i in (0..4).rev() {
        if a[i] != 0 {
            return 64 * i + 64 - a[i].leading_zeros() as usize;
        }
    }
    0
}

fn wide_from(a: &U256) -> Wide {
    let mut out = [0u64; WIDE];
    out[..4].copy_from_slice(a);
    out
}

fn wide_add(a: &Wide, b: &Wide) -> Wide {
    let mut out = [0u64; WIDE];
    let mut c = 0;
    for i in 0..WIDE {
        (out[i], c) = adc(a[i], b[i], c);
    }
    out
}

fn wide_sub(a: &Wide, b: &Wide) -> Wide {
    let mut out = [0u64; WIDE];
    let mut c = 0;
    for i in 0..WIDE {
        (out[i], c) = sbb(a[i], b[i], c);
    }
    out
}

/// Low `64 * WIDE` bits of the product.
fn wide_mul_lo(a: &Wide, b: &Wide) -> Wide {
    let mut out = [0u64; WIDE];
    for i in 0..WIDE {
        let mut c = 0;
        for j in 0..WIDE - i {
            (out[i + j], c) = mac(out[i + j], a[i], b[j], c);
        }
    }
    out
}

/// `w += v << (8 * byte_pos)` for `v < 2^64`.
fn wide_add_shifted(w: &mut Wide, v: u128, byte_pos: usize) {
    debug_assert!(v < 1 << 64);
    let word = byte_pos / 8;
    let x = v << (8 * (byte_pos % 8));
    let parts = [x as u64, (x >> 64) as u64];
    let mut c = 0;
    for i in word..WIDE {
        let add = if i - word < 2 { parts[i - word] } else { 0 };
        (w[i], c) = adc(w[i], add, c);
    }
}

fn wide_bitlen(a: &Wide) -> usize {
    for i in (0..WIDE).rev() {
        if a[i] != 0 {
            return 64 * i + 64 - a[i].leading_zeros() as usize;
        }
    }
    0
}

/// Quotient and remainder by a 256-bit divisor. Public operands only.
fn wide_divrem(n: &Wide, d: &U256) -> (Wide, U256) {
    let mut q = [0u64; WIDE];
    let mut r = [0u64; 5];
    for bit in (0..64 * WIDE).rev() {
        for i in (1..5).rev() {
            r[i] = (r[i] << 1) | (r[i - 1] >> 63);
        }
        r[0] = (r[0] << 1) | ((n[bit / 64] >> (bit % 64)) & 1);
        let mut t = [0u64; 5];
        let mut borrow = 0;
        for i in 0..5 {
            let di = if i < 4 { d[i] } else { 0 };
            (t[i], borrow) = sbb(r[i], di, borrow);
        }
        if borrow == 0 {
            r = t;
            q[bit / 64] |= 1 << (bit % 64);
        }
    }
    (q, [r[0], r[1], r[2], r[3]])
}

fn wide_to_bytes(a: &Wide) -> [u8; 8 * WIDE] {
    let mut out = [0u8; 8 * WIDE];
    for i in 0..WIDE {
        out[8 * i..8 * i + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    out
}

/// Field element of a small signed public integer.
fn f_int(v: i128) -> F {
    let m = F::from_u128_reduced(v.unsigned_abs());
    if v < 0 { -m } else { m }
}

// ============================================================================
// Modulus: native arithmetic and reduction data
// ============================================================================

/// An odd modulus below `2^256` with its native (Montgomery) arithmetic and the data the
/// reduction gadget needs.
#[derive(Clone)]
pub struct Modulus {
    p: U256,
    bits: usize,
    n0: u64,
    r2: U256,
    one: U256,
    m256: U256,
    /// `p^-1 mod 2^(64 * WIDE)`.
    pinv: Wide,
    /// `p = sum coeff * 2^(8 * position)`, with few terms for the pseudo-Mersenne moduli.
    sparse: Vec<(usize, i64)>,
    /// Limbs of a reduced element.
    limbs: usize,
    /// `fold[k - limbs]`: signed digits `(position, digit)` of `2^(8k) mod p` for the limb
    /// positions `k >= limbs` that a product can reach.
    fold: Vec<Vec<(usize, i64)>>,
}

impl Modulus {
    fn build(p: U256, sparse: Vec<(usize, i64)>) -> Self {
        assert!(
            p[0] & 1 == 1 && u256_bitlen(&p) > 128,
            "unsupported modulus"
        );
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p[0].wrapping_mul(inv)));
        }
        let mut m = Self {
            p,
            bits: u256_bitlen(&p),
            n0: inv.wrapping_neg(),
            r2: [0; 4],
            one: [0; 4],
            m256: [0; 4],
            pinv: [0; WIDE],
            sparse,
            limbs: u256_bitlen(&p).div_ceil(8),
            fold: Vec::new(),
        };
        let mut r = [1u64, 0, 0, 0];
        for _ in 0..256 {
            r = m.madd(&r, &r);
        }
        m.one = r;
        for _ in 0..256 {
            r = m.madd(&r, &r);
        }
        m.r2 = r;
        m.m256 = m.mont(&[256, 0, 0, 0]);

        let pw = wide_from(&p);
        let mut x = [0u64; WIDE];
        x[0] = inv;
        let mut two = [0u64; WIDE];
        two[0] = 2;
        for _ in 0..4 {
            x = wide_mul_lo(&x, &wide_sub(&two, &wide_mul_lo(&pw, &x)));
        }
        let mut unit = [0u64; WIDE];
        unit[0] = 1;
        assert_eq!(wide_mul_lo(&pw, &x), unit);
        m.pinv = x;

        let (mut pos, mut neg) = ([0u64; WIDE], [0u64; WIDE]);
        for &(k, c) in &m.sparse {
            let target = if c >= 0 { &mut pos } else { &mut neg };
            wide_add_shifted(target, c.unsigned_abs() as u128, k);
        }
        assert_eq!(
            wide_sub(&pos, &neg),
            pw,
            "sparse form does not evaluate to p"
        );

        // Digits of 2^(8k) mod p, centred to [-128, 127] below the top limb.
        let mut v = [1u64, 0, 0, 0];
        for _ in 0..8 * m.limbs {
            v = m.madd(&v, &v);
        }
        for _ in 0..m.limbs + 8 {
            let bytes = u256_to_bytes(&v);
            let mut digits = Vec::new();
            let mut carry = 0i64;
            for (i, &b) in bytes.iter().enumerate().take(m.limbs) {
                let mut d = b as i64 + carry;
                carry = 0;
                if d >= 128 && i + 1 < m.limbs {
                    d -= 256;
                    carry = 1;
                }
                if d != 0 {
                    digits.push((i, d));
                }
            }
            m.fold.push(digits);
            for _ in 0..8 {
                v = m.madd(&v, &v);
            }
        }
        m
    }

    /// Any odd modulus of more than 128 bits, given little-endian.
    pub fn new(p_le: &[u8; 32]) -> Self {
        let sparse = p_le
            .iter()
            .enumerate()
            .filter(|&(_, &b)| b != 0)
            .map(|(k, &b)| (k, b as i64))
            .collect();
        Self::build(u256_from_bytes(p_le), sparse)
    }

    /// `2^256 - 2^32 - 977`.
    pub fn secp256k1_base() -> Self {
        Self::build(
            crate::secp256k1_ct::SECP_P,
            vec![(32, 1), (4, -1), (1, -3), (0, -209)],
        )
    }

    /// The secp256k1 group order.
    pub fn secp256k1_order() -> Self {
        Self::new(&u256_to_bytes(&crate::secp256k1_ct::SECP_N))
    }

    /// `2^255 - 19`.
    pub fn curve25519_base() -> Self {
        Self::build(ED_P, vec![(31, 128), (0, -19)])
    }

    /// The order of the Ed25519 base point.
    pub fn ed25519_order() -> Self {
        Self::new(&u256_to_bytes(&ED_L))
    }

    /// Bit length of the modulus; every [`Element`] has this many bits.
    pub fn bits(&self) -> usize {
        self.bits
    }

    fn mmul(&self, a: &U256, b: &U256) -> U256 {
        let p = &self.p;
        let mut t = [0u64; 6];
        for &ai in a {
            let mut c = 0;
            for j in 0..4 {
                (t[j], c) = mac(t[j], ai, b[j], c);
            }
            let (s, c2) = adc(t[4], c, 0);
            t[4] = s;
            t[5] = c2;
            let m = t[0].wrapping_mul(self.n0);
            let (_, mut c) = mac(t[0], m, p[0], 0);
            for j in 1..4 {
                (t[j - 1], c) = mac(t[j], m, p[j], c);
            }
            let (s, c2) = adc(t[4], c, 0);
            t[3] = s;
            t[4] = t[5] + c2;
        }
        let r = [t[0], t[1], t[2], t[3]];
        let (d, borrow) = u256_sub(&r, p);
        let take = (t[4] | (1 - borrow)).wrapping_neg();
        u256_select(take, &d, &r)
    }

    fn madd(&self, a: &U256, b: &U256) -> U256 {
        let (s, c) = u256_add(a, b);
        let (d, borrow) = u256_sub(&s, &self.p);
        u256_select((c | (1 - borrow)).wrapping_neg(), &d, &s)
    }

    fn msub(&self, a: &U256, b: &U256) -> U256 {
        let (d, borrow) = u256_sub(a, b);
        let (e, _) = u256_add(&d, &self.p);
        u256_select(borrow.wrapping_neg(), &e, &d)
    }

    fn mont(&self, a: &U256) -> U256 {
        self.mmul(a, &self.r2)
    }

    fn canon(&self, a: &U256) -> U256 {
        self.mmul(a, &[1, 0, 0, 0])
    }

    /// `a^(p-2)`: the inverse, or zero for zero. The exponent is public.
    fn inv(&self, a: &U256) -> U256 {
        let (e, _) = u256_sub(&self.p, &[2, 0, 0, 0]);
        let mut acc = self.one;
        for i in (0..256).rev() {
            acc = self.mmul(&acc, &acc);
            if (e[i / 64] >> (i % 64)) & 1 == 1 {
                acc = self.mmul(&acc, a);
            }
        }
        acc
    }

    /// An integer congruent to `d` with at most `limbs` coefficients: every coefficient at
    /// a position `k >= limbs` is replaced by itself times the digits of `2^(8k) mod p`.
    /// No rows; the intervals follow by interval arithmetic.
    fn fold(&self, d: &Poly) -> Poly {
        let mut out = Poly(d.0[..self.limbs.min(d.0.len())].to_vec());
        out.0.resize(self.limbs, Coef::zero());
        for (k, c) in d.0.iter().enumerate().skip(self.limbs) {
            let digits = self
                .fold
                .get(k - self.limbs)
                .expect("operand too long to fold");
            for &(j, digit) in digits {
                let slot = &mut out.0[j];
                let digit = digit as i128;
                slot.lc = slot.lc.plus(&c.lc.scaled(f_int(digit)));
                slot.lo += (c.lo * digit).min(c.hi * digit);
                slot.hi += (c.lo * digit).max(c.hi * digit);
            }
        }
        out
    }

    fn small(&self, v: u64) -> U256 {
        self.mont(&[v, 0, 0, 0])
    }

    /// Residue (Montgomery form) of the integer a polynomial holds under the current
    /// assignment.
    fn poly_value(&self, cs: &ConstraintSystem, poly: &Poly) -> U256 {
        let mut acc = [0u64; 4];
        for c in poly.0.iter().rev() {
            let v = coef_value(cs, c);
            let sign = v >> 127;
            let mag = ((v ^ sign) - sign) as u64;
            let m = self.mont(&[mag, 0, 0, 0]);
            let term = u256_select(sign as u64, &self.msub(&[0; 4], &m), &m);
            acc = self.madd(&self.mmul(&acc, &self.m256), &term);
        }
        acc
    }
}

const ED_P: U256 = [
    0xffff_ffff_ffff_ffed,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x7fff_ffff_ffff_ffff,
];
const ED_L: U256 = [
    0x5812_631a_5cf5_d3ed,
    0x14de_f9de_a2f7_9cd6,
    0,
    0x1000_0000_0000_0000,
];
/// `v` of the Montgomery base point `(9, v)` that maps to the RFC 8032 base point.
const ED_BASE_V: U256 = [
    0xd616_3a5d_8131_2c14,
    0x6dc2_b281_9283_9e4d,
    0x1fe1_22d3_88b7_2eb3,
    0x5f51_e65e_475f_794b,
];
/// The square root of `-486664` with `x = c u / v` on the Edwards curve.
const ED_SQRT_M486664: U256 = [
    0xcc6e_04aa_ff45_7e06,
    0xc5a1_d3d1_4b7d_1a82,
    0xd27b_08dc_03fc_4f7e,
    0x0f26_edf4_60a0_06bb,
];
const ED_MONT_A: u64 = 486662;

// ============================================================================
// Bounded polynomials
// ============================================================================

/// A linear form with a proven integer interval for its value.
#[derive(Clone)]
struct Coef {
    lc: Lc,
    lo: i128,
    hi: i128,
}

impl Coef {
    fn constant(v: i128) -> Self {
        Self {
            lc: Lc::constant(f_int(v)),
            lo: v,
            hi: v,
        }
    }

    fn zero() -> Self {
        Self {
            lc: Lc::zero(),
            lo: 0,
            hi: 0,
        }
    }
}

/// The integer of a coefficient under the current assignment: the representative of its
/// field value that lies in the coefficient's interval.
fn coef_value(cs: &ConstraintSystem, c: &Coef) -> i128 {
    let x = cs.eval(&c.lc).to_canonical_u64() as i128;
    let wrap = (c.hi - x) >> 127;
    x - (wrap & PG)
}

/// The integer `sum coef_k 2^(8k)`.
#[derive(Clone, Default)]
struct Poly(Vec<Coef>);

impl Poly {
    fn constant_bytes(bytes: &[u8]) -> Self {
        Self(bytes.iter().map(|&b| Coef::constant(b as i128)).collect())
    }

    fn zip(&self, rhs: &Poly, sign: i128) -> Poly {
        let n = self.0.len().max(rhs.0.len());
        let mut out = Vec::with_capacity(n);
        for k in 0..n {
            let a = self.0.get(k).cloned().unwrap_or_else(Coef::zero);
            out.push(match rhs.0.get(k) {
                None => a,
                Some(b) if sign > 0 => Coef {
                    lc: a.lc.plus(&b.lc),
                    lo: a.lo + b.lo,
                    hi: a.hi + b.hi,
                },
                Some(b) => Coef {
                    lc: a.lc.minus(&b.lc),
                    lo: a.lo - b.hi,
                    hi: a.hi - b.lo,
                },
            });
        }
        Poly(out)
    }

    fn add(&self, rhs: &Poly) -> Poly {
        self.zip(rhs, 1)
    }

    fn sub(&self, rhs: &Poly) -> Poly {
        self.zip(rhs, -1)
    }

    fn scale(&self, k: i64) -> Poly {
        let kf = f_int(k as i128);
        let k = k as i128;
        Poly(
            self.0
                .iter()
                .map(|c| Coef {
                    lc: c.lc.scaled(kf),
                    lo: (c.lo * k).min(c.hi * k),
                    hi: (c.lo * k).max(c.hi * k),
                })
                .collect(),
        )
    }

    /// Product with a public non-negative integer given in bytes: no rows.
    fn mul_const(&self, bytes: &[u8]) -> Poly {
        let n = self.0.len() + bytes.len() - 1;
        let mut out = Vec::with_capacity(n);
        for k in 0..n {
            let mut parts: Vec<(F, &Lc)> = Vec::new();
            let (mut lo, mut hi) = (0i128, 0i128);
            for (j, &b) in bytes.iter().enumerate() {
                if b == 0 || j > k || k - j >= self.0.len() {
                    continue;
                }
                let c = &self.0[k - j];
                parts.push((F::from_u64_reduced(b as u64), &c.lc));
                lo += c.lo * b as i128;
                hi += c.hi * b as i128;
            }
            out.push(Coef {
                lc: Lc::combine(&parts),
                lo,
                hi,
            });
        }
        Poly(out)
    }

    /// Whether this is already a limb vector: 8-bit coefficients, at most 32 of them.
    fn is_limb_form(&self) -> bool {
        self.0.len() <= 32 && self.0.iter().all(|c| c.lo >= 0 && c.hi <= 255)
    }
}

/// `a(t) b(t)` with one fresh variable and one row per coefficient.
///
/// The rows state `a(s) b(s) = c(s)` at `deg + 1` points `s` (zero, infinity and small
/// integers of both signs), so `c = a b` as polynomials over the field. Each coefficient
/// interval is the interval sum of the term products and is asserted to stay below
/// [`COEF_BOUND`], which is where the field value pins the integer.
fn mul_poly(cs: &mut ConstraintSystem, a: &Poly, b: &Poly) -> Poly {
    let (la, lb) = (a.0.len(), b.0.len());
    assert!(la > 0 && lb > 0);
    let n = la + lb - 1;
    for c in a.0.iter().chain(&b.0) {
        assert!(c.lo > -(1 << 40) && c.hi < (1 << 40), "factor too wide");
    }
    let mut av: Vec<F> = a.0.iter().map(|c| cs.eval(&c.lc)).collect();
    let mut bv: Vec<F> = b.0.iter().map(|c| cs.eval(&c.lc)).collect();
    let mut out = Vec::with_capacity(n);
    for k in 0..n {
        let mut v = F::ZERO;
        let (mut lo, mut hi) = (0i128, 0i128);
        for i in k.saturating_sub(lb - 1)..=k.min(la - 1) {
            let (x, y) = (&a.0[i], &b.0[k - i]);
            v += av[i].const_mul(bv[k - i]);
            let c = [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi];
            lo += c.iter().copied().min().unwrap();
            hi += c.iter().copied().max().unwrap();
        }
        assert!(lo > -COEF_BOUND && hi < COEF_BOUND, "product too wide");
        out.push(Coef {
            lc: cs.alloc(v).into(),
            lo,
            hi,
        });
    }
    dregg_sig_core::wipe::wipe_goldilocks(&mut av);
    dregg_sig_core::wipe::wipe_goldilocks(&mut bv);

    cs.enforce_mul(a.0[0].lc.clone(), b.0[0].lc.clone(), out[0].lc.clone());
    if n >= 2 {
        cs.enforce_mul(
            a.0[la - 1].lc.clone(),
            b.0[lb - 1].lc.clone(),
            out[n - 1].lc.clone(),
        );
    }
    for e in 0..n.saturating_sub(2) {
        let s = f_int(if e % 2 == 0 {
            (e / 2 + 1) as i128
        } else {
            -((e / 2 + 1) as i128)
        });
        let mut pows = Vec::with_capacity(n);
        let mut acc = F::ONE;
        for _ in 0..n {
            pows.push(acc);
            acc = acc.const_mul(s);
        }
        let at = |p: &[Coef]| {
            let parts: Vec<(F, &Lc)> = pows.iter().copied().zip(p.iter().map(|c| &c.lc)).collect();
            Lc::combine(&parts)
        };
        cs.enforce_mul(at(&a.0), at(&b.0), at(&out));
    }
    Poly(out)
}

// ============================================================================
// Bit-decomposed witnesses
// ============================================================================

/// A witness in `[0, 2^bits)`: 8-bit limbs and their bits, one row per bit.
///
/// It is a residue representative, not necessarily the canonical one; see
/// [`Modulus::enforce_canonical`].
#[derive(Clone)]
pub struct Element {
    /// Little-endian limbs; limb `i` holds bits `8i..8i+8`.
    pub bytes_le: Vec<Lc>,
    /// Little-endian bits.
    pub bits_le: Vec<Lc>,
}

impl Element {
    fn poly(&self) -> Poly {
        let nbits = self.bits_le.len();
        Poly(
            self.bytes_le
                .iter()
                .enumerate()
                .map(|(i, lc)| Coef {
                    lc: lc.clone(),
                    lo: 0,
                    hi: (1i128 << (nbits - 8 * i).min(8)) - 1,
                })
                .collect(),
        )
    }

    /// The value as an unreduced operand.
    pub fn lazy(&self) -> Lazy {
        Lazy(self.poly())
    }
}

/// Allocate `value mod 2^nbits`. Each limb is one variable; its low bits are variables and
/// its top bit is the linear form that completes it, so a limb costs as many rows as bits.
fn alloc_int(cs: &mut ConstraintSystem, value_le: &[u8], nbits: usize) -> Element {
    let mut bytes_le = Vec::with_capacity(nbits.div_ceil(8));
    let mut bits_le = Vec::with_capacity(nbits);
    for i in 0..nbits.div_ceil(8) {
        let width = (nbits - 8 * i).min(8);
        let byte = value_le.get(i).copied().unwrap_or(0) & (0xffu16 >> (8 - width)) as u8;
        if width == 1 {
            let bit: Lc = cs.alloc(F::from_u64_reduced(byte as u64)).into();
            cs.enforce_boolean(&bit);
            bits_le.push(bit.clone());
            bytes_le.push(bit);
            continue;
        }
        let limb: Lc = cs.alloc(F::from_u64_reduced(byte as u64)).into();
        let mut top = limb.clone();
        for k in 0..width - 1 {
            let bit = cs.alloc(F::from_u64_reduced(((byte >> k) & 1) as u64));
            cs.enforce_boolean(&bit.into());
            top = top.minus(&Lc::term(bit, F::from_u64_reduced(1 << k)));
            bits_le.push(bit.into());
        }
        let top = top.scaled(F::from_u64_reduced(1 << (width - 1)).inv());
        cs.enforce_boolean(&top);
        bits_le.push(top);
        bytes_le.push(limb);
    }
    Element { bytes_le, bits_le }
}

/// An unreduced integer operand: sums, differences and constants are free.
#[derive(Clone)]
pub struct Lazy(Poly);

impl Lazy {
    /// A public constant, little-endian.
    pub fn constant(value_le: &[u8]) -> Self {
        Self(Poly::constant_bytes(value_le))
    }

    /// Bits the caller has constrained Boolean, little-endian.
    pub fn from_bits(bits_le: &[Lc]) -> Self {
        Self(Poly(
            bits_le
                .chunks(8)
                .map(|chunk| {
                    let parts: Vec<(F, &Lc)> = chunk
                        .iter()
                        .enumerate()
                        .map(|(k, b)| (F::from_u64_reduced(1 << k), b))
                        .collect();
                    Coef {
                        lc: Lc::combine(&parts),
                        lo: 0,
                        hi: (1 << chunk.len()) - 1,
                    }
                })
                .collect(),
        ))
    }

    pub fn add(&self, rhs: &Lazy) -> Lazy {
        Lazy(self.0.add(&rhs.0))
    }

    pub fn sub(&self, rhs: &Lazy) -> Lazy {
        Lazy(self.0.sub(&rhs.0))
    }

    /// Multiply by a small public integer.
    pub fn scale(&self, k: i32) -> Lazy {
        Lazy(self.0.scale(k as i64))
    }
}

impl Modulus {
    /// A fresh witness of [`Self::bits`] bits holding `value_le mod 2^bits`.
    pub fn alloc(&self, cs: &mut ConstraintSystem, value_le: &[u8; 32]) -> Element {
        alloc_int(cs, value_le, self.bits)
    }

    /// The canonical residue of `a` under the current assignment, little-endian.
    pub fn value(&self, cs: &ConstraintSystem, a: &Lazy) -> [u8; 32] {
        u256_to_bytes(&self.canon(&self.poly_value(cs, &a.0)))
    }

    /// A fresh element congruent to `a`.
    pub fn reduce(&self, cs: &mut ConstraintSystem, a: &Lazy) -> Element {
        let value = self.value(cs, a);
        let out = alloc_int(cs, &value, self.bits);
        enforce_zero_mod(cs, self, &out.poly().sub(&a.0));
        out
    }

    /// A fresh element congruent to `a b`.
    pub fn mul(&self, cs: &mut ConstraintSystem, a: &Lazy, b: &Lazy) -> Element {
        let product = mul_poly(cs, &a.0, &b.0);
        self.reduce(cs, &Lazy(product))
    }

    /// `a = 0 (mod p)`.
    pub fn enforce_zero(&self, cs: &mut ConstraintSystem, a: &Lazy) {
        enforce_zero_mod(cs, self, &a.0);
    }

    /// `a = b (mod p)`.
    pub fn enforce_equal(&self, cs: &mut ConstraintSystem, a: &Lazy, b: &Lazy) {
        enforce_zero_mod(cs, self, &a.0.sub(&b.0));
    }

    /// `a <= p - 1`, which makes `a` the unique representative of its residue.
    pub fn enforce_canonical(&self, cs: &mut ConstraintSystem, a: &Element) {
        let (pm1, _) = u256_sub(&self.p, &[1, 0, 0, 0]);
        enforce_le_const(cs, &a.bits_le, &u256_to_bytes(&pm1));
    }
}

// ============================================================================
// Reduction
// ============================================================================

/// Enforce that the integer `d` is a multiple of the modulus. Returns the quotient witness
/// (shifted by the public offset that makes it non-negative).
///
/// With `[lo_k, hi_k]` the coefficient intervals, `K = ceil(sum max(-lo_k, 0) 2^(8k) / p)`
/// and the quotient is range-checked to the bit length of `K + floor(sum hi_k 2^(8k) / p)`.
/// The identity `d + K p - q p = 0` is then split into groups of consecutive coefficients.
/// Group `g` with value `V_g` and incoming carry `c_(g-1)` defines the outgoing carry as the
/// linear form `(V_g + c_(g-1)) / 2^(8 len)`, which is range-checked by bits to an interval
/// that contains every integer the quotient `(V_g + c_(g-1)) / 2^(8 len)` can take. The
/// group length is the largest for which
/// `|V_g + c_(g-1) - 2^(8 len) c_g| < 2^64 - 2^32 + 1` over the admitted intervals, so the
/// range check on the form implies the integer equation. The last group must be zero.
fn enforce_zero_mod(cs: &mut ConstraintSystem, m: &Modulus, d: &Poly) -> Element {
    let folded;
    let d = if d.0.len() > m.limbs {
        folded = m.fold(d);
        &folded
    } else {
        d
    };
    assert!(d.0.len() <= 8 * WIDE - 6, "operand too long");
    let (mut pos, mut neg) = ([0u64; WIDE], [0u64; WIDE]);
    for (k, c) in d.0.iter().enumerate() {
        assert!(c.lo <= c.hi && c.lo > -COEF_BOUND && c.hi < COEF_BOUND);
        if c.hi > 0 {
            wide_add_shifted(&mut pos, c.hi as u128, k);
        }
        if c.lo < 0 {
            wide_add_shifted(&mut neg, (-c.lo) as u128, k);
        }
    }
    let pw = wide_from(&m.p);
    let mut pm1 = pw;
    pm1[0] -= 1;
    let (offset, _) = wide_divrem(&wide_add(&neg, &pm1), &m.p);
    let (qpos, _) = wide_divrem(&pos, &m.p);
    let qbits = wide_bitlen(&wide_add(&offset, &qpos)).max(1);
    let offset_p = wide_mul_lo(&offset, &pw);
    assert!(qbits + 264 <= 64 * WIDE, "quotient too wide");

    // Witness: q = (d + K p) / p by multiplication with p^-1 mod 2^576 (exact when d is a
    // multiple of p; any other assignment is rejected by the rows below).
    let (mut vpos, mut vneg) = ([0u64; WIDE], [0u64; WIDE]);
    for (k, c) in d.0.iter().enumerate() {
        let v = coef_value(cs, c);
        let sign = v >> 127;
        let mag = ((v ^ sign) - sign) as u128;
        wide_add_shifted(&mut vpos, mag & !(sign as u128) & (u64::MAX as u128), k);
        wide_add_shifted(&mut vneg, mag & (sign as u128) & (u64::MAX as u128), k);
    }
    let numer = wide_add(&wide_sub(&vpos, &vneg), &offset_p);
    let q_bytes = wide_to_bytes(&wide_mul_lo(&numer, &m.pinv));
    let q = alloc_int(cs, &q_bytes, qbits);
    let qp = q.poly();

    // e = d + K p - q p, coefficient by coefficient.
    let offset_bytes = wide_to_bytes(&offset_p);
    let offset_len = wide_bitlen(&offset_p).div_ceil(8);
    let top = m.sparse.iter().map(|&(k, _)| k).max().unwrap();
    let len = d.0.len().max(offset_len).max(qp.0.len() + top);
    let mut e: Vec<Coef> = (0..len)
        .map(|k| d.0.get(k).cloned().unwrap_or_else(Coef::zero))
        .collect();
    for (k, slot) in e.iter_mut().enumerate().take(offset_len) {
        let b = offset_bytes[k] as i128;
        slot.lc = slot.lc.plus_const(f_int(b));
        slot.lo += b;
        slot.hi += b;
    }
    for (i, qc) in qp.0.iter().enumerate() {
        for &(k, c) in &m.sparse {
            let c = -(c as i128);
            let slot = &mut e[i + k];
            slot.lc = slot.lc.plus(&qc.lc.scaled(f_int(c)));
            slot.lo += (qc.lo * c).min(qc.hi * c);
            slot.hi += (qc.lo * c).max(qc.hi * c);
        }
    }

    let mut at = 0;
    let mut carry = Coef::zero();
    let mut carry_value = 0i128;
    while at < len {
        // (group length, carry interval and bit count); `None` for the closing group.
        let mut choice: Option<(usize, Option<(i128, u32)>)> = None;
        for g in (1..=(len - at).min(8)).rev() {
            let (mut lo, mut hi) = (carry.lo, carry.hi);
            for i in 0..g {
                lo += e[at + i].lo << (8 * i);
                hi += e[at + i].hi << (8 * i);
            }
            if at + g == len {
                if lo > -PG && hi < PG {
                    choice = Some((g, None));
                    break;
                }
                continue;
            }
            let weight = 1i128 << (8 * g);
            let clo = lo.div_euclid(weight) + (lo.rem_euclid(weight) != 0) as i128;
            // An empty interval means no assignment can satisfy the identity; the carry is
            // then pinned to one value and its row cannot hold.
            let chi = hi.div_euclid(weight).max(clo);
            let nbits = 128 - ((chi - clo) as u128).leading_zeros();
            let admitted_hi = clo + (1i128 << nbits) - 1;
            if lo - weight * admitted_hi > -PG && hi - weight * clo < PG {
                choice = Some((g, Some((clo, nbits))));
                break;
            }
        }
        let (g, out) = choice.expect("no carry group fits the field");

        let mut parts: Vec<(F, &Lc)> = vec![(F::ONE, &carry.lc)];
        let mut value = carry_value;
        for i in 0..g {
            parts.push((F::TWO.pow(8 * i as u64), &e[at + i].lc));
            value = value.wrapping_add(coef_value(cs, &e[at + i]).wrapping_shl(8 * i as u32));
        }
        let group = Lc::combine(&parts);
        at += g;
        let Some((clo, nbits)) = out else {
            cs.enforce_zero(group);
            break;
        };
        let next = group.scaled(F::TWO.pow(8 * g as u64).inv());
        carry_value = value >> (8 * g);
        if nbits == 0 {
            cs.enforce_zero(next.plus_const(f_int(-clo)));
        } else {
            let shifted = (carry_value.wrapping_sub(clo)) as u128;
            let mut top = next.plus_const(f_int(-clo));
            for k in 0..nbits - 1 {
                let bit = cs.alloc(F::from_u64_reduced(((shifted >> k) & 1) as u64));
                cs.enforce_boolean(&bit.into());
                top = top.minus(&Lc::term(bit, F::from_u64_reduced(1 << k)));
            }
            cs.enforce_boolean(&top.scaled(F::from_u64_reduced(1 << (nbits - 1)).inv()));
        }
        carry = Coef {
            lc: next,
            lo: clo,
            hi: clo + (1i128 << nbits) - 1,
        };
    }
    q
}

// ============================================================================
// Comparisons with public constants
// ============================================================================

/// `1` iff every bit is one, as a linear form: two rows (none for one bit, one for two).
fn all_ones(cs: &mut ConstraintSystem, bits: &[Lc]) -> Lc {
    match bits {
        [one] => one.clone(),
        [a, b] => cs.mul(a, b).into(),
        _ => {
            let parts: Vec<(F, &Lc)> = bits.iter().map(|b| (F::NEG_ONE, b)).collect();
            let missing = Lc::combine(&parts).plus_const(F::from_u64_reduced(bits.len() as u64));
            let inv = cs.alloc(cs.eval(&missing).inv_or_zero());
            let nonzero = cs.mul(&missing, &inv.into());
            let flag = Lc::constant(F::ONE).minus(&nonzero.into());
            cs.enforce_mul(missing, flag.clone(), Lc::zero());
            flag
        }
    }
}

/// `sum bits_i 2^i <= bound` for Boolean `bits` and a public `bound` (little-endian bytes).
///
/// Scanning from the top, `run` is one while every bit seen under a one of `bound` was one.
/// Under a zero of `bound` the bit must then be zero. A block of ones of `bound` costs at
/// most three rows and a block of zeros one row.
fn enforce_le_const(cs: &mut ConstraintSystem, bits_le: &[Lc], bound_le: &[u8]) {
    let n = bits_le.len();
    let bound_bit = |i: usize| (bound_le.get(i / 8).copied().unwrap_or(0) >> (i % 8)) & 1 == 1;
    assert!((n..8 * bound_le.len()).all(|i| !bound_bit(i)));
    let Some(lowest_zero) = (0..n).find(|&i| !bound_bit(i)) else {
        return;
    };
    let mut run: Option<Lc> = None;
    let mut hi = n;
    while hi > lowest_zero {
        let ones = bound_bit(hi - 1);
        let mut lo = hi - 1;
        while lo > lowest_zero && bound_bit(lo - 1) == ones {
            lo -= 1;
        }
        let block = &bits_le[lo..hi];
        if ones {
            let all = all_ones(cs, block);
            run = Some(match run {
                None => all,
                Some(r) => cs.mul(&r, &all).into(),
            });
        } else {
            let parts: Vec<(F, &Lc)> = block.iter().map(|b| (F::ONE, b)).collect();
            let sum = Lc::combine(&parts);
            match &run {
                None => cs.enforce_zero(sum),
                Some(r) => cs.enforce_mul(r.clone(), sum, Lc::zero()),
            }
        }
        hi = lo;
    }
}

/// At least one of the Boolean `bits` is one: one row.
fn enforce_nonzero(cs: &mut ConstraintSystem, bits: &[Lc]) {
    let parts: Vec<(F, &Lc)> = bits.iter().map(|b| (F::ONE, b)).collect();
    let sum = Lc::combine(&parts);
    let inv = cs.alloc(cs.eval(&sum).inv_or_zero());
    cs.enforce_mul(sum, inv.into(), Lc::constant(F::ONE));
}

// ============================================================================
// Public-table lookup
// ============================================================================

/// Products of every subset of `bits`, indexed by the subset mask: `2^k - k - 1` rows.
fn monomials(cs: &mut ConstraintSystem, bits: &[Lc]) -> Vec<Lc> {
    let mut out: Vec<Lc> = Vec::with_capacity(1 << bits.len());
    out.push(Lc::constant(F::ONE));
    for mask in 1usize..1 << bits.len() {
        let top = usize::BITS as usize - 1 - mask.leading_zeros() as usize;
        let rest = mask ^ (1 << top);
        let lc = if rest == 0 {
            bits[top].clone()
        } else {
            cs.mul(&out[rest], &bits[top]).into()
        };
        out.push(lc);
    }
    out
}

/// `outputs` values of the public table row selected by the Boolean `index_bits`
/// (little-endian). The low [`LOW_INDEX_BITS`] bits are resolved through their subset
/// products, where every table column is a linear form; the high bits pick among those
/// forms with one row per form but the first. Each output is a single variable, or the
/// linear form itself when there are no high bits.
fn lookup(
    cs: &mut ConstraintSystem,
    index_bits: &[Lc],
    outputs: usize,
    entry: &dyn Fn(usize, usize) -> u64,
) -> Vec<Lc> {
    let low = index_bits.len().min(LOW_INDEX_BITS);
    let high = index_bits.len() - low;
    let low_monos = monomials(cs, &index_bits[..low]);
    let high_monos = monomials(cs, &index_bits[low..]);
    // One-hot selectors of the high index, as linear forms of its subset products.
    let selectors: Vec<Lc> = (0..1usize << high)
        .map(|h| {
            let parts: Vec<(F, &Lc)> = (0..1usize << high)
                .filter(|s| s & h == h)
                .map(|s| {
                    let sign = if (s ^ h).count_ones() % 2 == 0 {
                        F::ONE
                    } else {
                        F::NEG_ONE
                    };
                    (sign, &high_monos[s])
                })
                .collect();
            Lc::combine(&parts)
        })
        .collect();

    let mut out = Vec::with_capacity(outputs);
    let mut column = vec![F::ZERO; 1 << low];
    for o in 0..outputs {
        let forms: Vec<Lc> = (0..1usize << high)
            .map(|h| {
                for (l, slot) in column.iter_mut().enumerate() {
                    *slot = F::from_u64_reduced(entry((h << low) | l, o));
                }
                // Subset-sum inversion: column[l] = sum over S subset of l of coefficient[S].
                for i in 0..low {
                    for mask in 0..1usize << low {
                        if mask >> i & 1 == 1 {
                            let below = column[mask ^ (1 << i)];
                            column[mask] -= below;
                        }
                    }
                }
                let parts: Vec<(F, &Lc)> = column.iter().copied().zip(&low_monos).collect();
                Lc::combine(&parts)
            })
            .collect();
        if high == 0 {
            out.push(forms.into_iter().next().unwrap());
            continue;
        }
        // out = form_0 + sum over h >= 1 of selector_h (form_h - form_0); the last product
        // is the row that defines the output variable.
        let mut value = F::ZERO;
        for (sel, form) in selectors.iter().zip(&forms) {
            value += cs.eval(sel).const_mul(cs.eval(form));
        }
        let var: Lc = cs.alloc(value).into();
        let mut rest = var.minus(&forms[0]);
        let last = forms.len() - 1;
        for h in 1..last {
            rest = rest.minus(&cs.mul(&selectors[h], &forms[h].minus(&forms[0])).into());
        }
        cs.enforce_mul(selectors[last].clone(), forms[last].minus(&forms[0]), rest);
        out.push(var);
    }
    out
}

// ============================================================================
// Curves and window tables
// ============================================================================

/// Affine point in Montgomery-form coordinates.
type Pt = (U256, U256);

struct WindowTable {
    lo: usize,
    width: usize,
    signed: bool,
    /// Canonical little-endian `(x, y)` per table index.
    points: Vec<[[u8; 32]; 2]>,
}

impl WindowTable {
    /// Output `o` of a table row: the 32 bytes of `x`, then `y` in 48-bit chunks (signed
    /// windows) or in bytes (the unsigned window, whose outputs cost no rows).
    fn entry(&self, index: usize, o: usize) -> u64 {
        let [x, y] = &self.points[index];
        if o < 32 {
            return x[o] as u64;
        }
        if !self.signed {
            return y[o - 32] as u64;
        }
        let from = Y_CHUNK_LIMBS * (o - 32);
        let mut v = 0u64;
        for (k, &b) in y[from..(from + Y_CHUNK_LIMBS).min(32)].iter().enumerate() {
            v |= (b as u64) << (8 * k);
        }
        v
    }
}

const TABLE_OUTPUTS: usize = 32 + 32usize.div_ceil(Y_CHUNK_LIMBS);

/// `y^2 = x^3 + a2 x^2 + a4 x + a6` with the window tables of its base point.
struct Curve {
    f: Modulus,
    a2: u64,
    a4: u64,
    windows: Vec<WindowTable>,
}

impl Curve {
    fn double(&self, p: &Pt) -> Pt {
        let f = &self.f;
        let xx = f.mmul(&p.0, &p.0);
        let num = f.madd(
            &f.madd(
                &f.mmul(&f.small(3), &xx),
                &f.mmul(&f.small(2 * self.a2), &p.0),
            ),
            &f.small(self.a4),
        );
        let lam = f.mmul(&num, &f.inv(&f.madd(&p.1, &p.1)));
        self.chord(p, p, &lam)
    }

    fn chord(&self, p: &Pt, q: &Pt, lam: &U256) -> Pt {
        let f = &self.f;
        let x3 = f.msub(
            &f.msub(&f.msub(&f.mmul(lam, lam), &f.small(self.a2)), &p.0),
            &q.0,
        );
        let y3 = f.msub(&f.mmul(lam, &f.msub(&p.0, &x3)), &p.1);
        (x3, y3)
    }

    /// Group law on public points.
    fn add(&self, p: &Option<Pt>, q: &Option<Pt>) -> Option<Pt> {
        let f = &self.f;
        let (Some(p), Some(q)) = (p, q) else {
            return p.or(*q);
        };
        if p.0 == q.0 {
            if p.1 == q.1 && p.1 != [0; 4] {
                return Some(self.double(p));
            }
            return None;
        }
        let lam = f.mmul(&f.msub(&q.1, &p.1), &f.inv(&f.msub(&q.0, &p.0)));
        Some(self.chord(p, q, &lam))
    }

    fn scalar_mul(&self, k: &U256, p: &Pt) -> Option<Pt> {
        let mut acc = None;
        for i in (0..256).rev() {
            acc = self.add(&acc, &acc);
            if (k[i / 64] >> (i % 64)) & 1 == 1 {
                acc = self.add(&acc, &Some(*p));
            }
        }
        acc
    }

    /// `base_i + q` for every `i`, with one field inversion. No sum may be exceptional.
    fn batch_add(&self, base: &[Pt], q: &Pt) -> Vec<Pt> {
        let f = &self.f;
        let dx: Vec<U256> = base.iter().map(|p| f.msub(&q.0, &p.0)).collect();
        let mut prefix = Vec::with_capacity(dx.len());
        let mut acc = f.one;
        for d in &dx {
            assert!(*d != [0; 4], "exceptional table addition");
            prefix.push(acc);
            acc = f.mmul(&acc, d);
        }
        let mut inv = f.inv(&acc);
        let mut out = vec![([0u64; 4], [0u64; 4]); base.len()];
        for i in (0..base.len()).rev() {
            let dinv = f.mmul(&inv, &prefix[i]);
            inv = f.mmul(&inv, &dx[i]);
            let lam = f.mmul(&f.msub(&q.1, &base[i].1), &dinv);
            out[i] = self.chord(&base[i], q, &lam);
        }
        out
    }

    fn build(f: Modulus, a2: u64, a4: u64, base: (U256, U256), order: U256) -> Self {
        let mut curve = Self {
            f,
            a2,
            a4,
            windows: Vec::new(),
        };
        let f = &curve.f;
        let g: Pt = (f.mont(&base.0), f.mont(&base.1));
        // H = [1/2] G, and its doublings.
        let mut half = order;
        for i in 0..4 {
            half[i] = (order[i] >> 1) | if i < 3 { order[i + 1] << 63 } else { 0 };
        }
        let (half, _) = u256_add(&half, &[1, 0, 0, 0]);
        let h = curve.scalar_mul(&half, &g).expect("base point order");
        assert_eq!(curve.add(&Some(h), &Some(h)), Some(g));

        // The signed windows reach up to `last_lo`. Their partial sums are odd integers
        // of absolute value below 2^last_lo, which must not wrap modulo the group order.
        let last_lo = (u256_bitlen(&order) - 1) / SIGNED_WINDOW * SIGNED_WINDOW;
        assert!(last_lo < SCALAR_BITS && u256_bitlen(&order) > last_lo);
        let mut pow2 = Vec::with_capacity(last_lo + 2);
        pow2.push(h);
        for i in 0..=last_lo {
            let next = curve.double(&pow2[i]);
            pow2.push(next);
        }

        let canonical = |p: &Pt| [u256_to_bytes(&f.canon(&p.0)), u256_to_bytes(&f.canon(&p.1))];
        let mut windows = Vec::new();
        for lo in (0..last_lo).step_by(SIGNED_WINDOW) {
            // Index r holds [(2r + 1) 2^lo] H.
            let mut pts = vec![pow2[lo]];
            for k in 0..SIGNED_WINDOW - 1 {
                let more = curve.batch_add(&pts, &pow2[lo + k + 1]);
                pts.extend(more);
            }
            windows.push(WindowTable {
                lo,
                width: SIGNED_WINDOW,
                signed: true,
                points: pts.iter().map(canonical).collect(),
            });
        }
        // Index v holds [2 v 2^last_lo + 2^last_lo - 1] H.
        let neg_h = (h.0, f.msub(&[0; 4], &h.1));
        let mut pt = curve.add(&Some(pow2[last_lo]), &Some(neg_h));
        let mut pts = Vec::new();
        for _ in 0..1usize << (SCALAR_BITS - last_lo) {
            pts.push(canonical(&pt.expect("table point at infinity")));
            pt = curve.add(&pt, &Some(pow2[last_lo + 1]));
        }
        windows.push(WindowTable {
            lo: last_lo,
            width: SCALAR_BITS - last_lo,
            signed: false,
            points: pts,
        });
        curve.windows = windows;
        curve
    }

    fn secp256k1() -> Self {
        use crate::secp256k1_ct::{SECP_GX, SECP_GY, SECP_N};
        Self::build(Modulus::secp256k1_base(), 0, 0, (SECP_GX, SECP_GY), SECP_N)
    }

    /// Curve25519 in Montgomery form `v^2 = u^3 + 486662 u^2 + u`, base point `u = 9`.
    fn curve25519() -> Self {
        Self::build(
            Modulus::curve25519_base(),
            ED_MONT_A,
            1,
            ([9, 0, 0, 0], ED_BASE_V),
            ED_L,
        )
    }
}

fn with_secp256k1<R>(run: impl FnOnce(&Curve) -> R) -> R {
    #[cfg(any(feature = "std", test))]
    {
        static CURVE: std::sync::OnceLock<Curve> = std::sync::OnceLock::new();
        run(CURVE.get_or_init(Curve::secp256k1))
    }
    #[cfg(not(any(feature = "std", test)))]
    {
        run(&Curve::secp256k1())
    }
}

fn with_curve25519<R>(run: impl FnOnce(&Curve) -> R) -> R {
    #[cfg(any(feature = "std", test))]
    {
        static CURVE: std::sync::OnceLock<Curve> = std::sync::OnceLock::new();
        run(CURVE.get_or_init(Curve::curve25519))
    }
    #[cfg(not(any(feature = "std", test)))]
    {
        run(&Curve::curve25519())
    }
}

// ============================================================================
// Point addition and the fixed-base ladder
// ============================================================================

/// Accumulator: `x` in limbs, `y` as an unreduced integer.
struct Acc {
    x: Poly,
    y: Poly,
    x_element: Option<Element>,
}

/// The table point a scalar window selects, as `(x limbs, y)`.
fn window_point(cs: &mut ConstraintSystem, table: &WindowTable, bits: &[Lc]) -> (Poly, Poly) {
    assert_eq!(bits.len(), table.width);
    let limbs = |out: &[Lc]| -> (Poly, Poly) {
        let x = Poly(
            out[..32]
                .iter()
                .map(|lc| Coef {
                    lc: lc.clone(),
                    lo: 0,
                    hi: 255,
                })
                .collect(),
        );
        let mut y = vec![Coef::zero(); 32];
        for (c, lc) in out[32..].iter().enumerate() {
            let width = 8 * (32 - Y_CHUNK_LIMBS * c).min(Y_CHUNK_LIMBS);
            let max = (1i128 << width) - 1;
            y[Y_CHUNK_LIMBS * c] = Coef {
                lc: lc.clone(),
                lo: -max,
                hi: max,
            };
        }
        (x, Poly(y))
    };
    if !table.signed {
        assert!(table.width <= LOW_INDEX_BITS);
        let out = lookup(cs, bits, 64, &|i, o| table.entry(i, o));
        let bytes = |lcs: &[Lc]| {
            Poly(
                lcs.iter()
                    .map(|lc| Coef {
                        lc: lc.clone(),
                        lo: 0,
                        hi: 255,
                    })
                    .collect(),
            )
        };
        return (bytes(&out[..32]), bytes(&out[32..]));
    }
    // Window value u = 2^(w-1) s + r selects (2u + 1 - 2^w): index r with sign + when the
    // top bit s is set, index (complement of r) with sign - otherwise.
    let s = &bits[table.width - 1];
    let flip = Lc::constant(F::ONE).minus(s);
    let index: Vec<Lc> = bits[..table.width - 1]
        .iter()
        .map(|b| {
            let both = cs.mul(b, &flip);
            b.plus(&flip).minus(&Lc::from(both).scaled(F::TWO))
        })
        .collect();
    let mut out = lookup(cs, &index, TABLE_OUTPUTS, &|i, o| table.entry(i, o));
    let sign = s.scaled(F::TWO).plus_const(F::NEG_ONE);
    for y in out[32..].iter_mut() {
        *y = cs.mul(&sign, y).into();
    }
    limbs(&out)
}

/// `acc + (xt, yt)` in affine coordinates.
///
/// Rows: `lambda (xt - x1) = yt - y1` and `lambda^2 = a2 + x1 + xt + x3`, both modulo `p`,
/// with `lambda` and `x3` fresh. The new `y` is the integer `lambda (xt - x3) - yt`.
///
/// These two equations fix the sum when `x1 != xt`. With `complete`, the further equation
/// `2 lambda y1 + x3 xt - x1 (x3 + 2 x1 + xt) - 2 a2 x1 - a4 = 0` is enforced. It follows
/// from the first two and the curve equation when `x1 != xt`, and for `(xt, yt) = (x1, y1)`
/// it reads `2 lambda y1 = 3 x1^2 + 2 a2 x1 + a4`, the tangent slope. For
/// `(xt, yt) = (x1, -y1)` the first equation reads `0 = 2 yt`, which no point of odd order
/// satisfies. So a `complete` step is exact for every pair of points of odd order whose sum
/// is not the identity, and unsatisfiable when it is.
fn add_step(
    cs: &mut ConstraintSystem,
    curve: &Curve,
    acc: &Acc,
    xt: &Poly,
    yt: &Poly,
    complete: bool,
) -> Acc {
    let f = &curve.f;
    let x1 = f.poly_value(cs, &acc.x);
    let y1 = f.poly_value(cs, &acc.y);
    let x2 = f.poly_value(cs, xt);
    let y2 = f.poly_value(cs, yt);
    let dx = f.msub(&x2, &x1);
    let mut lam = f.mmul(&f.msub(&y2, &y1), &f.inv(&dx));
    if complete {
        let num = f.madd(
            &f.madd(
                &f.mmul(&f.small(3), &f.mmul(&x1, &x1)),
                &f.mmul(&f.small(2 * curve.a2), &x1),
            ),
            &f.small(curve.a4),
        );
        let tangent = f.mmul(&num, &f.inv(&f.madd(&y1, &y1)));
        lam = u256_select(u256_zero_mask(&dx), &tangent, &lam);
    }
    let x3 = f.msub(
        &f.msub(&f.msub(&f.mmul(&lam, &lam), &f.small(curve.a2)), &x1),
        &x2,
    );
    let lam = alloc_int(cs, &u256_to_bytes(&f.canon(&lam)), f.bits);
    let x3 = alloc_int(cs, &u256_to_bytes(&f.canon(&x3)), f.bits);
    let (lam_p, x3_p) = (lam.poly(), x3.poly());
    let a2 = Poly::constant_bytes(&curve.a2.to_le_bytes()[..3]);

    let chord = mul_poly(cs, &lam_p, &xt.sub(&acc.x));
    enforce_zero_mod(cs, f, &chord.sub(yt).add(&acc.y));
    let square = mul_poly(cs, &lam_p, &lam_p);
    enforce_zero_mod(cs, f, &square.sub(&acc.x).sub(xt).sub(&x3_p).sub(&a2));

    if complete {
        let y1_p = if acc.y.is_limb_form() {
            acc.y.clone()
        } else {
            f.reduce(cs, &Lazy(acc.y.clone())).poly()
        };
        let t1 = mul_poly(cs, &lam_p, &y1_p);
        let t2 = mul_poly(cs, &x3_p, xt);
        let t3 = mul_poly(cs, &acc.x, &x3_p.add(&acc.x.scale(2)).add(xt));
        let linear = acc
            .x
            .mul_const(&(2 * curve.a2).to_le_bytes()[..3])
            .add(&Poly::constant_bytes(&curve.a4.to_le_bytes()[..1]));
        enforce_zero_mod(cs, f, &t1.scale(2).add(&t2).sub(&t3).sub(&linear));
    }

    let back = mul_poly(cs, &lam_p, &xt.sub(&x3_p));
    Acc {
        x: x3_p,
        y: back.sub(yt),
        x_element: Some(x3),
    }
}

/// `[k] G` for the Boolean little-endian scalar bits: the final `x` (a reduced witness) and
/// the unreduced `y`. Unsatisfiable when `k` is a multiple of the group order.
fn fixed_base_mul(cs: &mut ConstraintSystem, curve: &Curve, scalar_bits_le: &[Lc]) -> Acc {
    assert_eq!(scalar_bits_le.len(), SCALAR_BITS, "scalar is 256 bits");
    let mut acc: Option<Acc> = None;
    for table in &curve.windows {
        let bits = &scalar_bits_le[table.lo..table.lo + table.width];
        let (xt, yt) = window_point(cs, table, bits);
        acc = Some(match acc {
            None => Acc {
                x: xt,
                y: yt,
                x_element: None,
            },
            Some(prev) if table.signed => add_step(cs, curve, &prev, &xt, &yt, false),
            // The unsigned window's point has `y` in limbs, so it takes the accumulator
            // role and the tangent equation needs no reduction of the running `y`.
            Some(prev) => {
                let last = Acc {
                    x: xt,
                    y: yt,
                    x_element: None,
                };
                add_step(cs, curve, &last, &prev.x, &prev.y, true)
            }
        });
    }
    acc.expect("at least one window")
}

/// An affine point with unreduced coordinates.
#[derive(Clone)]
pub struct AffinePoint {
    pub x: Lazy,
    pub y: Lazy,
}

/// `p + q` on secp256k1 for two points of the curve with `p != -q` (which is
/// unsatisfiable); `p = q` is handled. Both coordinates of the result are fresh elements.
pub fn secp256k1_point_add(
    cs: &mut ConstraintSystem,
    p: &AffinePoint,
    q: &AffinePoint,
) -> AffinePoint {
    with_secp256k1(|curve| {
        let f = &curve.f;
        let reduce = |cs: &mut ConstraintSystem, a: &Lazy| {
            if a.0.is_limb_form() {
                a.0.clone()
            } else {
                f.reduce(cs, a).poly()
            }
        };
        let acc = Acc {
            x: reduce(cs, &p.x),
            y: reduce(cs, &p.y),
            x_element: None,
        };
        let (qx, qy) = (reduce(cs, &q.x), reduce(cs, &q.y));
        let sum = add_step(cs, curve, &acc, &qx, &qy, true);
        AffinePoint {
            x: Lazy(sum.x),
            y: f.reduce(cs, &Lazy(sum.y)).lazy(),
        }
    })
}

// ============================================================================
// secp256k1
// ============================================================================

/// A field element in its canonical representation.
#[derive(Clone)]
pub struct CanonicalCoordinate {
    /// 32 little-endian bytes.
    pub bytes_le: Vec<Lc>,
    /// 256 little-endian bits (bit `8i + k` is bit `k` of byte `i`).
    pub bits_le: Vec<Lc>,
}

impl CanonicalCoordinate {
    fn from_element(mut e: Element) -> Self {
        e.bits_le.resize(256, Lc::zero());
        Self {
            bytes_le: e.bytes_le,
            bits_le: e.bits_le,
        }
    }

    /// The eight bits of byte `i`, least significant first.
    pub fn byte_bits(&self, i: usize) -> [Lc; 8] {
        core::array::from_fn(|k| self.bits_le[8 * i + k].clone())
    }
}

/// `[k] G` on secp256k1 with canonical affine coordinates.
#[derive(Clone)]
pub struct Secp256k1PublicKey {
    pub x: CanonicalCoordinate,
    pub y: CanonicalCoordinate,
}

impl Secp256k1PublicKey {
    /// Parity of `y`.
    pub fn y_is_odd(&self) -> Lc {
        self.y.bits_le[0].clone()
    }

    /// SEC1 compressed encoding: `02 | parity(y)`, then `x` big-endian (33 bytes).
    pub fn compressed_bytes(&self) -> Vec<Lc> {
        let mut out = vec![self.y_is_odd().plus_const(F::TWO)];
        out.extend(self.x.bytes_le.iter().rev().cloned());
        out
    }

    /// Bits of [`Self::compressed_bytes`], per byte and least significant first.
    pub fn compressed_bits(&self) -> Vec<[Lc; 8]> {
        let mut prefix: [Lc; 8] = core::array::from_fn(|_| Lc::zero());
        prefix[0] = self.y_is_odd();
        prefix[1] = Lc::constant(F::ONE);
        let mut out = vec![prefix];
        out.extend((0..32).rev().map(|i| self.x.byte_bits(i)));
        out
    }

    /// `x || y`, both big-endian (64 bytes).
    pub fn uncompressed_bytes(&self) -> Vec<Lc> {
        let mut out: Vec<Lc> = self.x.bytes_le.iter().rev().cloned().collect();
        out.extend(self.y.bytes_le.iter().rev().cloned());
        out
    }

    /// Bits of [`Self::uncompressed_bytes`], per byte and least significant first.
    pub fn uncompressed_bits(&self) -> Vec<[Lc; 8]> {
        let mut out: Vec<[Lc; 8]> = (0..32).rev().map(|i| self.x.byte_bits(i)).collect();
        out.extend((0..32).rev().map(|i| self.y.byte_bits(i)));
        out
    }

    /// BIP340 x-only encoding: `x` big-endian (32 bytes). It names the point of this `x`
    /// with even `y`; see [`Self::enforce_even_y`].
    pub fn x_only_bytes(&self) -> Vec<Lc> {
        self.x.bytes_le.iter().rev().cloned().collect()
    }

    /// Bits of [`Self::x_only_bytes`], per byte and least significant first.
    pub fn x_only_bits(&self) -> Vec<[Lc; 8]> {
        (0..32).rev().map(|i| self.x.byte_bits(i)).collect()
    }

    /// Require `y` even, so that the scalar itself is the BIP340 secret key of
    /// [`Self::x_only_bytes`].
    pub fn enforce_even_y(&self, cs: &mut ConstraintSystem) {
        cs.enforce_zero(self.y_is_odd());
    }
}

fn canonical_x(cs: &mut ConstraintSystem, f: &Modulus, acc: &Acc) -> CanonicalCoordinate {
    let x = acc.x_element.clone().expect("at least one addition");
    f.enforce_canonical(cs, &x);
    CanonicalCoordinate::from_element(x)
}

/// `[k] G` on secp256k1 for the 256 little-endian scalar bits, which the caller has
/// constrained Boolean. The result is `[k mod n] G`; the rows are unsatisfiable when
/// `k = 0 (mod n)`. Use [`secp256k1_enforce_scalar_range`] where `1 <= k < n` is part of
/// the statement.
pub fn secp256k1_fixed_base_mul(
    cs: &mut ConstraintSystem,
    scalar_bits_le: &[Lc],
) -> Secp256k1PublicKey {
    with_secp256k1(|curve| {
        let acc = fixed_base_mul(cs, curve, scalar_bits_le);
        let x = canonical_x(cs, &curve.f, &acc);
        let y = curve.f.reduce(cs, &Lazy(acc.y));
        curve.f.enforce_canonical(cs, &y);
        Secp256k1PublicKey {
            x,
            y: CanonicalCoordinate::from_element(y),
        }
    })
}

/// The canonical `x` of `[k] G` only (BIP340 public key bytes are its big-endian bytes),
/// without materialising `y`. Same contract as [`secp256k1_fixed_base_mul`].
pub fn secp256k1_fixed_base_mul_x_only(
    cs: &mut ConstraintSystem,
    scalar_bits_le: &[Lc],
) -> CanonicalCoordinate {
    with_secp256k1(|curve| {
        let acc = fixed_base_mul(cs, curve, scalar_bits_le);
        canonical_x(cs, &curve.f, &acc)
    })
}

fn enforce_scalar_range(cs: &mut ConstraintSystem, bits_le: &[Lc], order: &U256) {
    let (max, _) = u256_sub(order, &[1, 0, 0, 0]);
    enforce_le_const(cs, bits_le, &u256_to_bytes(&max));
    enforce_nonzero(cs, bits_le);
}

/// `1 <= k <= n - 1` for Boolean little-endian scalar bits.
pub fn secp256k1_enforce_scalar_range(cs: &mut ConstraintSystem, scalar_bits_le: &[Lc]) {
    assert_eq!(scalar_bits_le.len(), SCALAR_BITS);
    enforce_scalar_range(cs, scalar_bits_le, &crate::secp256k1_ct::SECP_N);
}

// ============================================================================
// Ed25519
// ============================================================================

/// An Ed25519 point `[k] B` in its RFC 8032 encoding.
#[derive(Clone)]
pub struct Ed25519PublicKey {
    /// Canonical Edwards `y` (bit 255 is the constant zero).
    pub y: CanonicalCoordinate,
    /// Parity of the canonical Edwards `x`.
    pub x_is_odd: Lc,
}

impl Ed25519PublicKey {
    /// The 32-byte encoding: `y` little-endian with the parity of `x` in the top bit.
    pub fn encoding_bytes(&self) -> Vec<Lc> {
        let mut out = self.y.bytes_le.clone();
        out[31] = out[31].plus(&self.x_is_odd.scaled(F::from_u64_reduced(128)));
        out
    }

    /// The 256 bits of the encoding, little-endian.
    pub fn encoding_bits(&self) -> Vec<Lc> {
        let mut out = self.y.bits_le.clone();
        out[255] = self.x_is_odd.clone();
        out
    }
}

/// `[k] B` on Ed25519 for the 256 little-endian scalar bits, which the caller has
/// constrained Boolean. The result is `[k mod l] B`; the rows are unsatisfiable when
/// `k = 0 (mod l)`, which no clamped scalar is.
///
/// The ladder runs on the Montgomery model `v^2 = u^3 + 486662 u^2 + u`; the result is
/// mapped by `y = (u - 1) / (u + 1)`, `x = sqrt(-486664) u / v`. A point of order `l` has
/// `u != -1` and `v != 0`, so both quotients are determined.
pub fn ed25519_fixed_base_mul(
    cs: &mut ConstraintSystem,
    scalar_bits_le: &[Lc],
) -> Ed25519PublicKey {
    with_curve25519(|curve| {
        let f = &curve.f;
        let acc = fixed_base_mul(cs, curve, scalar_bits_le);
        let u = acc.x;
        let v = f.reduce(cs, &Lazy(acc.y)).poly();
        let (un, vn) = (f.poly_value(cs, &u), f.poly_value(cs, &v));
        let yn = f.mmul(&f.msub(&un, &f.one), &f.inv(&f.madd(&un, &f.one)));
        let c = f.mont(&ED_SQRT_M486664);
        let xn = f.mmul(&f.mmul(&c, &un), &f.inv(&vn));
        let y = alloc_int(cs, &u256_to_bytes(&f.canon(&yn)), f.bits);
        let x = alloc_int(cs, &u256_to_bytes(&f.canon(&xn)), f.bits);

        let one = Poly::constant_bytes(&[1]);
        let yu = mul_poly(cs, &y.poly(), &u.add(&one));
        enforce_zero_mod(cs, f, &yu.sub(&u).add(&one));
        let xv = mul_poly(cs, &x.poly(), &v);
        enforce_zero_mod(
            cs,
            f,
            &xv.sub(&u.mul_const(&u256_to_bytes(&ED_SQRT_M486664))),
        );
        f.enforce_canonical(cs, &y);
        f.enforce_canonical(cs, &x);
        Ed25519PublicKey {
            x_is_odd: x.bits_le[0].clone(),
            y: CanonicalCoordinate::from_element(y),
        }
    })
}

/// RFC 8032 clamping of 256 little-endian bits: clear bits 0, 1, 2 and 255, set bit 254.
pub fn ed25519_clamp(bits_le: &[Lc]) -> Vec<Lc> {
    assert_eq!(bits_le.len(), SCALAR_BITS);
    let mut out = bits_le.to_vec();
    for i in [0, 1, 2, 255] {
        out[i] = Lc::zero();
    }
    out[254] = Lc::constant(F::ONE);
    out
}

/// `1 <= k <= l - 1` for Boolean little-endian scalar bits.
pub fn ed25519_enforce_scalar_range(cs: &mut ConstraintSystem, scalar_bits_le: &[Lc]) {
    assert_eq!(scalar_bits_le.len(), SCALAR_BITS);
    enforce_scalar_range(cs, scalar_bits_le, &ED_L);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ed25519_ct::public_key_from_clamped_scalar;
    use crate::secp256k1_ct::{Fp256, SECP_N, SECP_P, SecpPoint};
    use dregg_sig_agg::zk_hem::relation::Shape;
    use std::println;

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn bytes(&mut self) -> [u8; 32] {
            u256_to_bytes(&core::array::from_fn(|_| self.next()))
        }
    }

    fn bit_vars(cs: &mut ConstraintSystem, le: &[u8; 32]) -> Vec<Lc> {
        (0..256)
            .map(|i| {
                let bit: Lc = cs
                    .alloc(F::from_u64_reduced(((le[i / 8] >> (i % 8)) & 1) as u64))
                    .into();
                cs.enforce_boolean(&bit);
                bit
            })
            .collect()
    }

    fn eval_bytes(cs: &ConstraintSystem, lcs: &[Lc]) -> Vec<u8> {
        lcs.iter()
            .map(|lc| {
                let v = cs.eval(lc).to_canonical_u64();
                assert!(v < 256, "byte out of range");
                v as u8
            })
            .collect()
    }

    fn eval_bit_bytes(cs: &ConstraintSystem, bits: &[[Lc; 8]]) -> Vec<u8> {
        bits.iter()
            .map(|byte| {
                byte.iter().enumerate().fold(0u8, |acc, (k, lc)| {
                    let v = cs.eval(lc).to_canonical_u64();
                    assert!(v < 2, "bit out of range");
                    acc | ((v as u8) << k)
                })
            })
            .collect()
    }

    fn var_of(lc: &Lc) -> usize {
        assert_eq!(lc.terms().len(), 1);
        lc.terms()[0].0 as usize
    }

    /// Violated rows as `(range rows, other rows)`. A range row is `v (1 - v) = 0`: an
    /// empty right side and a second factor of more than one term. Product rows have a
    /// right side and the closing row of a reduction has the constant one as second factor.
    fn violated_rows(shape: &Shape, z: &[F]) -> (usize, usize) {
        assert_eq!(shape.num_sbox, 0);
        let (mut range, mut other) = (0, 0);
        for i in 0..shape.num_rows() {
            if shape.a.row_dot(i, z).const_mul(shape.b.row_dot(i, z)) != shape.c.row_dot(i, z) {
                if shape.c.row(i).count() == 0 && shape.b.row(i).count() > 1 {
                    range += 1;
                } else {
                    other += 1;
                }
            }
        }
        (range, other)
    }

    fn le(a: &U256) -> [u8; 32] {
        u256_to_bytes(a)
    }

    fn be(le: &[u8; 32]) -> [u8; 32] {
        let mut out = *le;
        out.reverse();
        out
    }

    /// Shift-and-add reference, independent of the Montgomery code under test.
    fn ref_mulmod(a: &U256, b: &U256, p: &U256) -> U256 {
        let reduce = |x: U256, carry: u64| {
            let (d, borrow) = u256_sub(&x, p);
            if carry == 1 || borrow == 0 { d } else { x }
        };
        let a = reduce(*a, 0);
        let mut acc = [0u64; 4];
        for i in (0..256).rev() {
            let (s, c) = u256_add(&acc, &acc);
            acc = reduce(s, c);
            if (b[i / 64] >> (i % 64)) & 1 == 1 {
                let (s, c) = u256_add(&acc, &a);
                acc = reduce(s, c);
            }
        }
        acc
    }

    #[test]
    fn field_mul_matches_references_for_four_moduli() {
        let mut rng = Rng(1);
        let moduli = [
            (Modulus::secp256k1_base(), SECP_P),
            (Modulus::curve25519_base(), ED_P),
            (Modulus::secp256k1_order(), SECP_N),
            (Modulus::ed25519_order(), ED_L),
        ];
        for (m, p) in &moduli {
            for round in 0..3 {
                let (mut a, mut b) = (rng.bytes(), rng.bytes());
                if round == 0 {
                    // Largest representable operands.
                    a = [0xff; 32];
                    b = [0xff; 32];
                }
                let mut cs = ConstraintSystem::new();
                let (ea, eb) = (m.alloc(&mut cs, &a), m.alloc(&mut cs, &b));
                let c = m.mul(&mut cs, &ea.lazy(), &eb.lazy());
                m.enforce_canonical(&mut cs, &c);
                // `alloc` keeps the low `bits` bits.
                let mask = |x: &[u8; 32]| {
                    let mut v = u256_from_bytes(x);
                    if m.bits() < 256 {
                        v[3] &= (1u64 << (m.bits() - 192)) - 1;
                    }
                    v
                };
                let want = ref_mulmod(&mask(&a), &mask(&b), p);
                assert_eq!(eval_bytes(&cs, &c.bytes_le), le(&want));
                assert_eq!(m.value(&cs, &c.lazy()), le(&want));
                if *p == SECP_P {
                    let native = Fp256(ref_mulmod(&mask(&a), &[1, 0, 0, 0], p))
                        * Fp256(ref_mulmod(&mask(&b), &[1, 0, 0, 0], p));
                    assert_eq!(native.normalize().0, want);
                }
                let (shape, z) = cs.finish();
                assert!(shape.is_satisfied(&z));
                for lc in [
                    &c.bytes_le[0],
                    &c.bytes_le[17],
                    &c.bits_le[9],
                    &ea.bytes_le[31],
                ] {
                    let mut bad = z.clone();
                    bad[var_of(lc)] += F::ONE;
                    assert!(!shape.is_satisfied(&bad));
                }
            }
        }
    }

    #[test]
    fn lazy_sums_and_differences_reduce_correctly() {
        let m = Modulus::secp256k1_base();
        let mut rng = Rng(2);
        let (a, b, c) = (rng.bytes(), rng.bytes(), rng.bytes());
        let mut cs = ConstraintSystem::new();
        let (ea, eb, ec) = (
            m.alloc(&mut cs, &a),
            m.alloc(&mut cs, &b),
            m.alloc(&mut cs, &c),
        );
        // (a - b + 3c + 5) * (b - a)
        let left = ea
            .lazy()
            .sub(&eb.lazy())
            .add(&ec.lazy().scale(3))
            .add(&Lazy::constant(&[5]));
        let right = eb.lazy().sub(&ea.lazy());
        let out = m.mul(&mut cs, &left, &right);
        m.enforce_canonical(&mut cs, &out);
        let (fa, fb, fc) = (
            Fp256(u256_from_bytes(&a)).normalize(),
            Fp256(u256_from_bytes(&b)).normalize(),
            Fp256(u256_from_bytes(&c)).normalize(),
        );
        let three_c = fc + fc + fc;
        let want = (fa - fb + three_c + Fp256([5, 0, 0, 0])) * (fb - fa);
        assert_eq!(eval_bytes(&cs, &out.bytes_le), le(&want.normalize().0));
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
    }

    #[test]
    fn non_canonical_limbs_and_out_of_range_quotients_are_rejected_by_range_rows_alone() {
        let m = Modulus::secp256k1_base();
        let mut rng = Rng(3);
        let (a, b) = (rng.bytes(), rng.bytes());
        let mut cs = ConstraintSystem::new();
        let (ea, eb) = (m.alloc(&mut cs, &a), m.alloc(&mut cs, &b));
        let product = mul_poly(&mut cs, &ea.poly(), &eb.poly());
        let value = m.value(&cs, &Lazy(product.clone()));
        let r = alloc_int(&mut cs, &value, m.bits());
        let q = enforce_zero_mod(&mut cs, &m, &r.poly().sub(&product));
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        assert_eq!(violated_rows(&shape, &z), (0, 0));

        // Move 256 from one limb into the next: the represented integer, and with it every
        // product row and the closing row, is unchanged. Only range rows can object: the two
        // limbs, and a carry whose integer value moved while its bits did not.
        for (element, most) in [(&r, 2), (&q, 3)] {
            let mut bad = z.clone();
            bad[var_of(&element.bytes_le[0])] += F::from_u64_reduced(256);
            bad[var_of(&element.bytes_le[1])] -= F::ONE;
            let (range, other) = violated_rows(&shape, &bad);
            assert!((2..=most).contains(&range), "{range} range rows");
            assert_eq!(other, 0);
        }
        // The reduction no longer needs a wide quotient: the high limbs are folded first.
        assert!(q.bits_le.len() < 48, "quotient of {} bits", q.bits_le.len());
        assert!(q.bytes_le.len() >= 2);
        // A quotient that is off by one breaks the identity itself.
        let mut bad = z.clone();
        let bit = var_of(&q.bits_le[0]);
        let delta = F::ONE - bad[bit] - bad[bit];
        bad[bit] += delta;
        bad[var_of(&q.bytes_le[0])] += delta;
        assert!(!shape.is_satisfied(&bad));
    }

    #[test]
    fn enforce_zero_accepts_exactly_the_multiples_of_p() {
        let m = Modulus::curve25519_base();
        let twice = u256_add(&ED_P, &ED_P).0;
        for (value, ok) in [
            ([0u64; 4], true),
            (ED_P, true),
            (twice, true),
            ([1, 0, 0, 0], false),
            (u256_sub(&ED_P, &[1, 0, 0, 0]).0, false),
            (u256_add(&ED_P, &[1, 0, 0, 0]).0, false),
            (u256_add(&twice, &[1 << 40, 0, 0, 0]).0, false),
        ] {
            // As a constant, and as a witness minus zero.
            let mut cs = ConstraintSystem::new();
            m.enforce_zero(&mut cs, &Lazy::constant(&le(&value)));
            let bits = bit_vars(&mut cs, &le(&value));
            m.enforce_equal(&mut cs, &Lazy::from_bits(&bits), &Lazy::constant(&[0]));
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok);
        }
    }

    #[test]
    #[should_panic(expected = "factor too wide")]
    fn operands_too_wide_for_the_field_are_refused_at_synthesis() {
        let m = Modulus::secp256k1_base();
        let mut cs = ConstraintSystem::new();
        let a = m.alloc(&mut cs, &[7; 32]);
        let wide = a.lazy().scale(1 << 20).scale(1 << 20);
        let _ = m.mul(&mut cs, &wide, &a.lazy());
    }

    #[test]
    fn canonical_check_separates_p_minus_one_from_p() {
        for (m, p) in [
            (Modulus::secp256k1_base(), SECP_P),
            (Modulus::curve25519_base(), ED_P),
        ] {
            let (pm1, _) = u256_sub(&p, &[1, 0, 0, 0]);
            let (pp1, _) = u256_add(&p, &[1, 0, 0, 0]);
            let top = if m.bits() == 256 {
                [u64::MAX; 4]
            } else {
                [u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]
            };
            for (value, ok) in [
                ([0u64; 4], true),
                ([5, 0, 0, 0], true),
                (pm1, true),
                (p, false),
                (pp1, false),
                (top, false),
            ] {
                let mut cs = ConstraintSystem::new();
                let e = m.alloc(&mut cs, &le(&value));
                assert_eq!(eval_bytes(&cs, &e.bytes_le), le(&value));
                m.enforce_canonical(&mut cs, &e);
                let (shape, z) = cs.finish();
                assert_eq!(shape.is_satisfied(&z), ok);
            }
        }
    }

    #[test]
    fn le_const_agrees_with_integer_comparison() {
        for bound in [
            0u8, 1, 2, 0b011_1000, 0b101_0101, 0b111_0111, 63, 64, 77, 126, 127,
        ] {
            for x in 0u8..128 {
                let mut cs = ConstraintSystem::new();
                let bits: Vec<Lc> = (0..7)
                    .map(|i| cs.alloc(F::from_u64_reduced(((x >> i) & 1) as u64)).into())
                    .collect();
                enforce_le_const(&mut cs, &bits, &[bound]);
                let (shape, z) = cs.finish();
                assert_eq!(shape.is_satisfied(&z), x <= bound, "x={x} bound={bound}");
            }
        }
    }

    #[test]
    fn scalar_range_gadgets_accept_exactly_one_to_order_minus_one() {
        let run = |secp: bool, k: U256| {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            if secp {
                secp256k1_enforce_scalar_range(&mut cs, &bits);
            } else {
                ed25519_enforce_scalar_range(&mut cs, &bits);
            }
            let (shape, z) = cs.finish();
            shape.is_satisfied(&z)
        };
        let mut rng = Rng(4);
        for (secp, order) in [(true, SECP_N), (false, ED_L)] {
            let minus = |d: u64| u256_sub(&order, &[d, 0, 0, 0]).0;
            let plus = |d: u64| u256_add(&order, &[d, 0, 0, 0]).0;
            assert!(!run(secp, [0; 4]));
            assert!(run(secp, [1, 0, 0, 0]));
            assert!(run(secp, minus(2)));
            assert!(run(secp, minus(1)));
            assert!(!run(secp, order));
            assert!(!run(secp, plus(1)));
            assert!(!run(secp, [u64::MAX; 4]));
            for _ in 0..20 {
                let k = u256_from_bytes(&rng.bytes());
                let (_, borrow) = u256_sub(&k, &order);
                assert_eq!(run(secp, k), borrow == 1);
                // Values within a few low bits of the order.
                let near = [
                    order[0] ^ (rng.next() & 0xffff),
                    order[1],
                    order[2],
                    order[3],
                ];
                let (_, borrow) = u256_sub(&near, &order);
                assert_eq!(run(secp, near), borrow == 1);
            }
        }
    }

    fn secp_scalars() -> Vec<U256> {
        let mut rng = Rng(5);
        let n = SECP_N;
        let mut out = vec![
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            u256_sub(&n, &[1, 0, 0, 0]).0,
            u256_sub(&n, &[2, 0, 0, 0]).0,
            // Zero windows almost everywhere.
            [0, 0, 0, 1 << 8],
            [0, 1 << 12, 0, 0],
            [0x0000_0fff_0000_0000, 0, 0, 0xf000_0000_0000_0000],
            // Above the order: the result is [k - n] G.
            [u64::MAX; 4],
            u256_add(&n, &[7, 0, 0, 0]).0,
            secp_doubling_scalar(),
        ];
        out.extend((0..4).map(|_| u256_from_bytes(&rng.bytes())));
        out
    }

    /// The scalar whose last addition has equal operands: `k_low = 2^256 - 1 - n` under the
    /// top window value 15.
    fn secp_doubling_scalar() -> U256 {
        let n = SECP_N;
        let low: U256 = core::array::from_fn(|i| !n[i]);
        u256_add(&low, &[0, 0, 0, 0xf000_0000_0000_0000]).0
    }

    #[test]
    fn doubling_scalars_really_double_the_last_table_point() {
        with_secp256k1(|curve| {
            let f = &curve.f;
            let [tx, ty] = curve.windows.last().unwrap().points[15];
            let t = (f.mont(&u256_from_bytes(&tx)), f.mont(&u256_from_bytes(&ty)));
            let twice = curve.double(&t);
            let native = SecpPoint::generator_mul_ct(&be(&le(&secp_doubling_scalar())))
                .to_affine()
                .unwrap();
            assert_eq!(f.canon(&twice.0), native.0.normalize().0);
            assert_eq!(f.canon(&twice.1), native.1.normalize().0);
        });
    }

    #[test]
    fn secp256k1_fixed_base_matches_native_encodings() {
        for k in secp_scalars() {
            let native = SecpPoint::generator_mul_ct(&be(&le(&k)));
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let pk = secp256k1_fixed_base_mul(&mut cs, &bits);
            let compressed = native.to_compressed_bytes().unwrap();
            let uncompressed = native.to_uncompressed_64().unwrap();
            assert_eq!(eval_bytes(&cs, &pk.compressed_bytes()), compressed);
            assert_eq!(eval_bit_bytes(&cs, &pk.compressed_bits()), compressed);
            assert_eq!(eval_bytes(&cs, &pk.uncompressed_bytes()), uncompressed);
            assert_eq!(eval_bit_bytes(&cs, &pk.uncompressed_bits()), uncompressed);
            assert_eq!(eval_bytes(&cs, &pk.x_only_bytes()), compressed[1..]);
            assert_eq!(eval_bit_bytes(&cs, &pk.x_only_bits()), compressed[1..]);
            let odd = cs.eval(&pk.y_is_odd()).to_canonical_u64();
            assert_eq!(odd as u8, compressed[0] & 1);
            pk.enforce_even_y(&mut cs);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), odd == 0, "k = {k:x?}");
        }
    }

    #[test]
    fn secp256k1_x_only_matches_native() {
        for k in [secp_scalars()[2], secp_scalars()[9], secp_scalars()[11]] {
            let native = SecpPoint::generator_mul_ct(&be(&le(&k)));
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let x = secp256k1_fixed_base_mul_x_only(&mut cs, &bits);
            let mut got = eval_bytes(&cs, &x.bytes_le);
            got.reverse();
            assert_eq!(got, native.to_compressed_bytes().unwrap()[1..]);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
        }
    }

    /// Every private variable of the relation is pinned: changing any single one breaks it.
    fn assert_single_changes_rejected(shape: &Shape, z: &[F], seed: u64, samples: usize) {
        let mut rng = Rng(seed);
        for _ in 0..samples {
            let i = 1 + (rng.next() as usize) % (shape.mask_var_base - 1);
            let mut bad = z.to_vec();
            bad[i] += F::from_u64_reduced(1 + rng.next() % 3);
            assert!(!shape.is_satisfied(&bad), "variable {i} is free");
        }
    }

    #[test]
    fn secp256k1_rejects_tampered_witnesses_and_multiples_of_the_order() {
        let k = secp_scalars()[12];
        let mut cs = ConstraintSystem::new();
        let bits = bit_vars(&mut cs, &le(&k));
        let pk = secp256k1_fixed_base_mul(&mut cs, &bits);
        let outputs = [
            var_of(&pk.x.bits_le[0]),
            var_of(&pk.x.bits_le[100]),
            var_of(&pk.y.bits_le[0]),
            var_of(&pk.y.bytes_le[31]),
            var_of(&pk.x.bytes_le[0]),
        ];
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        for i in outputs {
            let mut bad = z.clone();
            bad[i] += F::ONE;
            assert!(!shape.is_satisfied(&bad));
            // A flipped bit that stays Boolean.
            let mut bad = z.clone();
            bad[i] = F::ONE - bad[i];
            assert!(!shape.is_satisfied(&bad));
        }
        assert_single_changes_rejected(&shape, &z, 6, 600);

        for k in [[0u64; 4], SECP_N] {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let _ = secp256k1_fixed_base_mul(&mut cs, &bits);
            let (other, z) = cs.finish();
            assert_eq!(other, shape, "row structure depends on the witness");
            assert!(!other.is_satisfied(&z));
        }
    }

    #[test]
    fn secp256k1_point_add_matches_native_including_doubling() {
        let m = Modulus::secp256k1_base();
        let affine = |k: u64| {
            let (x, y) = SecpPoint::generator_mul_ct(&be(&le(&[k, 0, 0, 0])))
                .to_affine()
                .unwrap();
            (x.normalize().0, y.normalize().0)
        };
        let neg = |p: (U256, U256)| (p.0, (-Fp256(p.1)).normalize().0);
        for (a, b, sum) in [
            (affine(5), affine(11), Some(affine(16))),
            (affine(9), affine(9), Some(affine(18))),
            (affine(3), neg(affine(1)), Some(affine(2))),
            (affine(7), neg(affine(7)), None),
        ] {
            let mut cs = ConstraintSystem::new();
            let point = |cs: &mut ConstraintSystem, p: (U256, U256)| AffinePoint {
                x: m.alloc(cs, &le(&p.0)).lazy(),
                y: m.alloc(cs, &le(&p.1)).lazy(),
            };
            let (pa, pb) = (point(&mut cs, a), point(&mut cs, b));
            let out = secp256k1_point_add(&mut cs, &pa, &pb);
            let got = (m.value(&cs, &out.x), m.value(&cs, &out.y));
            let (shape, z) = cs.finish();
            match sum {
                Some(want) => {
                    assert_eq!(got, (le(&want.0), le(&want.1)));
                    assert!(shape.is_satisfied(&z));
                }
                None => assert!(!shape.is_satisfied(&z)),
            }
        }
    }

    fn ed_scalars() -> Vec<U256> {
        let mut rng = Rng(7);
        let mut out = vec![
            [1, 0, 0, 0],
            [8, 0, 0, 0],
            u256_sub(&ED_L, &[1, 0, 0, 0]).0,
            u256_add(&ED_L, &[1, 0, 0, 0]).0,
            // The last addition doubles: k_low = 2^252 - 1 under the top window value 0.
            [u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 4],
            [0, 0, 1 << 20, 1 << 62],
            [u64::MAX; 4],
        ];
        out.extend((0..3).map(|_| u256_from_bytes(&rng.bytes())));
        out
    }

    #[test]
    fn ed25519_fixed_base_matches_native_encoding() {
        for k in ed_scalars() {
            let want = public_key_from_clamped_scalar(&le(&k));
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let pk = ed25519_fixed_base_mul(&mut cs, &bits);
            assert_eq!(eval_bytes(&cs, &pk.encoding_bytes()), want);
            let enc_bits = pk.encoding_bits();
            let per_byte: Vec<[Lc; 8]> = (0..32)
                .map(|i| core::array::from_fn(|j| enc_bits[8 * i + j].clone()))
                .collect();
            assert_eq!(eval_bit_bytes(&cs, &per_byte), want);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z), "k = {k:x?}");
        }
    }

    #[test]
    fn ed25519_clamped_keys_match_native_and_tampering_is_rejected() {
        let mut rng = Rng(8);
        let mut shapes = Vec::new();
        for round in 0..3 {
            let raw = rng.bytes();
            let mut clamped = raw;
            clamped[0] &= 248;
            clamped[31] &= 127;
            clamped[31] |= 64;
            let want = public_key_from_clamped_scalar(&clamped);
            let mut cs = ConstraintSystem::new();
            let bits = ed25519_clamp(&bit_vars(&mut cs, &raw));
            let pk = ed25519_fixed_base_mul(&mut cs, &bits);
            assert_eq!(eval_bytes(&cs, &pk.encoding_bytes()), want);
            let outputs = [
                var_of(&pk.x_is_odd),
                var_of(&pk.y.bits_le[3]),
                var_of(&pk.y.bytes_le[31]),
            ];
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            if round == 0 {
                for i in outputs {
                    let mut bad = z.clone();
                    bad[i] = F::ONE - bad[i];
                    assert!(!shape.is_satisfied(&bad));
                }
                // Skip the scalar bits the clamp discards (variables 1..=256).
                let mut rng = Rng(9);
                for _ in 0..400 {
                    let i = 257 + (rng.next() as usize) % (shape.mask_var_base - 257);
                    let mut bad = z.clone();
                    bad[i] += F::ONE;
                    assert!(!shape.is_satisfied(&bad), "variable {i} is free");
                }
            }
            shapes.push(shape);
        }
        assert!(shapes.windows(2).all(|w| w[0] == w[1]));

        for k in [[0u64; 4], ED_L, u256_add(&ED_L, &ED_L).0] {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let _ = ed25519_fixed_base_mul(&mut cs, &bits);
            let (shape, z) = cs.finish();
            assert!(!shape.is_satisfied(&z));
        }
    }

    #[test]
    #[ignore = "measurement"]
    fn row_census() {
        let mut rng = Rng(10);
        let report = |name: &str, build: &dyn Fn(&mut ConstraintSystem)| {
            let mut cs = ConstraintSystem::new();
            let start = std::time::Instant::now();
            build(&mut cs);
            let synthesis = start.elapsed();
            let rows = cs.num_rows();
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            println!(
                "{name}: rows={rows} vars={} nnz={} synthesis={synthesis:?}",
                shape.num_vars,
                shape.a.nnz() + shape.b.nnz() + shape.c.nnz(),
            );
        };
        let (a, b) = (rng.bytes(), rng.bytes());
        let k = rng.bytes();
        let m = Modulus::secp256k1_base();
        let operands = |cs: &mut ConstraintSystem| {
            // Operand allocation, subtracted below.
            (m.alloc(cs, &a), m.alloc(cs, &b))
        };
        report("two operand allocations (overhead)", &|cs| {
            let _ = operands(cs);
        });
        report("non-native mul incl. operand allocations", &|cs| {
            let (ea, eb) = operands(cs);
            let _ = m.mul(cs, &ea.lazy(), &eb.lazy());
        });
        let affine = |s: u64| {
            let (x, y) = SecpPoint::generator_mul_ct(&be(&le(&[s, 0, 0, 0])))
                .to_affine()
                .unwrap();
            (le(&x.normalize().0), le(&y.normalize().0))
        };
        let (p, q) = (affine(5), affine(11));
        report("four coordinate allocations (overhead)", &|cs| {
            for v in [&p.0, &p.1, &q.0, &q.1] {
                let _ = m.alloc(cs, v);
            }
        });
        report(
            "complete point addition incl. coordinate allocations",
            &|cs| {
                let pa = AffinePoint {
                    x: m.alloc(cs, &p.0).lazy(),
                    y: m.alloc(cs, &p.1).lazy(),
                };
                let pb = AffinePoint {
                    x: m.alloc(cs, &q.0).lazy(),
                    y: m.alloc(cs, &q.1).lazy(),
                };
                let _ = secp256k1_point_add(cs, &pa, &pb);
            },
        );
        report("256 scalar bits (overhead)", &|cs| {
            let _ = bit_vars(cs, &k);
        });
        report(
            "secp256k1 fixed-base mul, x and y, incl. scalar bits",
            &|cs| {
                let bits = bit_vars(cs, &k);
                let _ = secp256k1_fixed_base_mul(cs, &bits);
            },
        );
        report(
            "secp256k1 fixed-base mul, x only, incl. scalar bits",
            &|cs| {
                let bits = bit_vars(cs, &k);
                let _ = secp256k1_fixed_base_mul_x_only(cs, &bits);
            },
        );
        report("ed25519 fixed-base mul incl. scalar bits", &|cs| {
            let bits = ed25519_clamp(&bit_vars(cs, &k));
            let _ = ed25519_fixed_base_mul(cs, &bits);
        });
        let start = std::time::Instant::now();
        let fresh = Curve::secp256k1();
        println!(
            "secp256k1 window tables: {} points, built in {:?}",
            fresh.windows.iter().map(|w| w.points.len()).sum::<usize>(),
            start.elapsed()
        );
        with_secp256k1(|curve| {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &k);
            let before = cs.num_rows();
            let table = &curve.windows[1];
            let _ = window_point(&mut cs, table, &bits[table.lo..table.lo + table.width]);
            println!(
                "one 12-bit signed window lookup: rows={}",
                cs.num_rows() - before
            );
        });
    }
}
