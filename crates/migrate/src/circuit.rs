//! Field elements of the five prime fields and GF(2) the general-quorum engine computes in.
use crate::{
    bls12_381::{BLS_P, BLS_P_INV, BLS_P_MINUS_2, BLS_P_R2},
    limbs,
    pallas::{PALLAS_P, PALLAS_P_INV, PALLAS_P_MINUS_2, PALLAS_P_R2},
    scalar,
    secp256k1_ct::{Fp256, SECP_P},
};
use dregg_sig_accel::goldilocks::{GOLDILOCKS_PRIME, gl_add, gl_mul, gl_sub};

pub(crate) type Value = [u64; 6];
pub(crate) const ZERO: Value = [0; 6];
pub(crate) const ONE: Value = [1, 0, 0, 0, 0, 0];

#[inline(always)]
pub(crate) const fn lift4(x: [u64; 4]) -> Value {
    [x[0], x[1], x[2], x[3], 0, 0]
}

#[inline(always)]
pub(crate) const fn trunc4(x: Value) -> [u64; 4] {
    [x[0], x[1], x[2], x[3]]
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Domain {
    Bit,
    Gold,
    Secp,
    Ed,
    PallasFp,
    BlsFp,
}
impl Domain {
    pub(crate) const ALL_FIELDS: [Self; 5] = [
        Self::Gold,
        Self::Secp,
        Self::Ed,
        Self::PallasFp,
        Self::BlsFp,
    ];

    pub(crate) fn inverse(self, a: Value) -> Value {
        match self {
            Self::PallasFp => lift4(limbs::mont_pow(
                trunc4(a),
                PALLAS_P_MINUS_2,
                PALLAS_P,
                PALLAS_P_INV,
                PALLAS_P_R2,
            )),
            Self::BlsFp => limbs::mont_pow(a, BLS_P_MINUS_2, BLS_P, BLS_P_INV, BLS_P_R2),
            _ => {
                let exp = limbs::sub_mod(self.modulus(), [2, 0, 0, 0, 0, 0], self.modulus());
                let mut out = ONE;
                for i in (0..self.width()).rev() {
                    out = self.mul(out, out);
                    if (exp[i / 64] >> (i % 64)) & 1 != 0 {
                        out = self.mul(out, a);
                    }
                }
                out
            }
        }
    }
    pub(crate) fn modulus(self) -> Value {
        match self {
            Self::Bit => [2, 0, 0, 0, 0, 0],
            Self::Gold => [GOLDILOCKS_PRIME, 0, 0, 0, 0, 0],
            Self::Secp => lift4(SECP_P),
            Self::Ed => lift4(scalar::ED_PRIME),
            Self::PallasFp => lift4(PALLAS_P),
            Self::BlsFp => BLS_P,
        }
    }
    pub(crate) fn width(self) -> usize {
        match self {
            Self::Bit => 1,
            Self::Gold => 64,
            Self::Secp => 256,
            Self::Ed => 255,
            Self::PallasFp => 255,
            Self::BlsFp => 381,
        }
    }
    #[inline(always)]
    pub(crate) fn limbs_len(self) -> usize {
        self.width().div_ceil(64)
    }
    #[inline(always)]
    pub(crate) fn byte_len(self) -> usize {
        self.width().div_ceil(8)
    }
    #[inline(always)]
    pub(crate) fn tape_draw_bits(self) -> usize {
        match self {
            Self::Bit => 1,
            Self::Gold => 64,
            Self::Secp | Self::Ed => 256,
            // Zero-rejection wide reductions:
            // - `PallasFp`: 512 bits (`lo + 2^254 * hi mod p`, `< 2^-253.8` bias, 0% rejection)
            // - `BlsFp`:    768 bits (`lo + 2^380 * hi mod p`, `< 2^-379` bias, 0% rejection)
            Self::PallasFp => 512,
            Self::BlsFp => 768,
        }
    }
    #[inline(always)]
    pub(crate) fn canonical(self, x: Value) -> bool {
        limbs::lt(x, self.modulus())
    }
    #[inline(always)]
    pub(crate) fn add(self, a: Value, b: Value) -> Value {
        match self {
            Self::Bit => [a[0] ^ b[0], 0, 0, 0, 0, 0],
            Self::Gold => [gl_add(a[0], b[0]), 0, 0, 0, 0, 0],
            Self::Secp => lift4((Fp256(trunc4(a)) + Fp256(trunc4(b))).0),
            Self::Ed => lift4(limbs::add_mod(trunc4(a), trunc4(b), scalar::ED_PRIME)),
            Self::PallasFp => lift4(limbs::add_mod(trunc4(a), trunc4(b), PALLAS_P)),
            Self::BlsFp => limbs::add_mod(a, b, BLS_P),
        }
    }
    #[inline(always)]
    pub(crate) fn sub(self, a: Value, b: Value) -> Value {
        match self {
            Self::Bit => self.add(a, b),
            Self::Gold => [gl_sub(a[0], b[0]), 0, 0, 0, 0, 0],
            Self::Secp => lift4((Fp256(trunc4(a)) - Fp256(trunc4(b))).0),
            Self::Ed => lift4(limbs::sub_mod(trunc4(a), trunc4(b), scalar::ED_PRIME)),
            Self::PallasFp => lift4(limbs::sub_mod(trunc4(a), trunc4(b), PALLAS_P)),
            Self::BlsFp => limbs::sub_mod(a, b, BLS_P),
        }
    }
    #[inline(always)]
    pub(crate) fn mul(self, a: Value, b: Value) -> Value {
        match self {
            Self::Bit => [a[0] & b[0], 0, 0, 0, 0, 0],
            Self::Gold => [gl_mul(a[0], b[0]), 0, 0, 0, 0, 0],
            Self::Secp => lift4((Fp256(trunc4(a)) * Fp256(trunc4(b))).0),
            Self::Ed => lift4(crate::ed25519_ct::multiply_limbs(trunc4(a), trunc4(b))),
            Self::PallasFp => {
                let m = limbs::mont_mul(trunc4(a), trunc4(b), PALLAS_P, PALLAS_P_INV);
                lift4(limbs::mont_mul(m, PALLAS_P_R2, PALLAS_P, PALLAS_P_INV))
            }
            Self::BlsFp => {
                let m = limbs::mont_mul(a, b, BLS_P, BLS_P_INV);
                limbs::mont_mul(m, BLS_P_R2, BLS_P, BLS_P_INV)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_prime_field_multiplies_and_inverts() {
        for d in Domain::ALL_FIELDS {
            let p = d.modulus();
            let minus_one = d.sub(ZERO, ONE);
            assert_eq!(d.add(minus_one, ONE), ZERO, "{d:?}");
            assert_eq!(d.mul(minus_one, minus_one), ONE, "{d:?}");
            assert!(d.canonical(minus_one) && !d.canonical(p), "{d:?}");
            // 2 * (p + 1) / 2 = 1, and Fermat inversion agrees with it.
            let two = d.add(ONE, ONE);
            let mut half = p;
            half[0] += 1;
            let mut carry = 0;
            for limb in half.iter_mut().rev() {
                let next = *limb & 1;
                *limb = (*limb >> 1) | (carry << 63);
                carry = next;
            }
            assert_eq!(d.mul(two, half), ONE, "{d:?}");
            assert_eq!(d.inverse(two), half, "{d:?}");
            let seven = [7, 0, 0, 0, 0, 0];
            assert_eq!(d.mul(d.inverse(seven), seven), ONE, "{d:?}");
            assert_eq!(
                d.mul([3, 0, 0, 0, 0, 0], seven),
                [21, 0, 0, 0, 0, 0],
                "{d:?}"
            );
        }
    }
}
