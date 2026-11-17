//! The Ed25519 base field prime, little-endian limbs.

pub(crate) const ED_PRIME: [u64; 4] = [
    0xffff_ffff_ffff_ffed,
    u64::MAX,
    u64::MAX,
    0x7fff_ffff_ffff_ffff,
];
