//! Modulus and Montgomery constants of the BLS12-381 base field (and, for the limb tests,
//! the subgroup order).

/// `BLS12-381` base field modulus `p` (`381` bits, little-endian `u64` limbs).
pub(crate) const BLS_P: [u64; 6] = [
    0xb9fe_ffff_ffff_aaab,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

pub(crate) const BLS_P_MINUS_2: [u64; 6] = [
    0xb9fe_ffff_ffff_aaa9,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

/// `-p[0]^{-1} mod 2^64` for 6-limb CIOS Montgomery reduction over `F_p`.
pub(crate) const BLS_P_INV: u64 = 0x89f3_fffc_fffc_fffd;

/// `R^2 mod p` for `R = 2^384`.
pub(crate) const BLS_P_R2: [u64; 6] = [
    0xf4df_1f34_1c34_1746,
    0x0a76_e6a6_09d1_04f1,
    0x8de5_476c_4c95_b6d5,
    0x67eb_88a9_939d_83c0,
    0x9a79_3e85_b519_952d,
    0x1198_8fe5_92ca_e3aa,
];

#[cfg(test)]
/// `BLS12-381` prime subgroup order `r` (`255` bits, little-endian `u64` limbs).
pub(crate) const BLS_R: [u64; 4] = [
    0xffff_ffff_0000_0001,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
];
