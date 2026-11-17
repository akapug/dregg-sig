//! Moduli and Montgomery constants of the Pallas base field (and, for the limb tests,
//! the scalar field modulus).

/// Pallas base field modulus `p = 2^254 + 0x224698fc094cf91b992d30ed00000001` (LE limbs).
pub(crate) const PALLAS_P: [u64; 4] = [
    0x992d_30ed_0000_0001,
    0x2246_98fc_094c_f91b,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];

pub(crate) const PALLAS_P_MINUS_2: [u64; 4] = [
    0x992d_30ec_ffff_ffff,
    0x2246_98fc_094c_f91b,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];

/// `-p[0]^{-1} mod 2^64` for CIOS Montgomery reduction over `F_p`.
pub(crate) const PALLAS_P_INV: u64 = 0x992d_30ec_ffff_ffff;

/// `R^2 mod p` for `R = 2^256`.
pub(crate) const PALLAS_P_R2: [u64; 4] = [
    0x8c78_ecb3_0000_000f,
    0xd7d3_0dbd_8b0d_e0e7,
    0x7797_a99b_c3c9_5d18,
    0x096d_41af_7b9c_b714,
];

#[cfg(test)]
/// Pallas scalar field modulus `q = 2^254 + 0x224698fc0994a8dd8c46eb2100000001` (LE limbs).
pub(crate) const PALLAS_Q: [u64; 4] = [
    0x8c46_eb21_0000_0001,
    0x2246_98fc_0994_a8dd,
    0x0000_0000_0000_0000,
    0x4000_0000_0000_0000,
];
