//! The engine interface the authenticated general-quorum engine (`threshold_mpc`)
//! implements, and the Boolean and prime-field gadgets written against it.
use crate::circuit::{Domain, Value, ZERO};
use crate::secret::{SecretVec, Wipe};
use crate::threshold_mpc::{
    AuthWord, BooleanTriple, DaBitWord, FieldShare, FieldTriple, ThresholdField,
};
use alloc::{vec, vec::Vec};
use dregg_sig_accel::ct::ct_zeroize_u64s;

const BIT_LANES: usize = 64;

pub(crate) type Word<B> = SecretVec<B>;

/// One 64-lane shared Boolean wire of some backend. XOR is the only local gate.
pub(crate) trait ShareBit:
    Copy + Default + Send + Sync + Wipe + core::ops::BitXor<Output = Self>
{
}

/// Primitive operations of an MPC engine; [`Gadgets`] is written against it alone.
///
/// Contract: no value derived from secret wires is
/// returned by `open`, `open_lanes` or `fopen_many`, and `agree` does not
/// succeed, unless every multiplication and conversion performed so far has
/// passed the backend's active-security check. Any failure poisons the engine.
pub(crate) trait Core {
    type Bit: ShareBit;
    /// Canonical `(position_in_quorum, quorum_size)`.
    fn quorum_position(&self) -> (usize, usize);
    /// Public 64-lane constant.
    fn constant(&self, x: u64) -> Self::Bit;
    /// Jointly input words: the shared value is the XOR of all parties' `own`.
    #[cfg(test)]
    fn share(&mut self, own: &[u64]) -> Result<Word<Self::Bit>, Error>;
    /// Jointly input words with pairwise PRSS / authenticated masking so no peer sees raw `own`.
    fn share_masked(&mut self, own: &[u64]) -> Result<Word<Self::Bit>, Error>;
    /// As `share`, with every party's contribution forced to be lane-uniform.
    fn share_uniform_lanes(&mut self, own: &[u64]) -> Result<Word<Self::Bit>, Error>;
    /// Jointly input 64-lane prime-field words: the shared value is the mod-`p_d` sum of all
    /// parties' canonical `own_words`, masked so no peer sees another party's raw share.
    fn fshare_many(&mut self, own_words: &[Value], d: Domain) -> Result<Vec<FieldWord>, Error>;
    /// Broadcast a byte slice from every party in canonical quorum order after settling pending checks.
    fn broadcast_bytes(&mut self, own: &[u8]) -> Result<Vec<Vec<u8>>, Error>;
    fn and_into(
        &mut self,
        pairs: &[(Self::Bit, Self::Bit)],
        out: &mut Word<Self::Bit>,
    ) -> Result<(), Error>;
    fn verify_all_pending(&mut self) -> Result<(), Error>;
    fn open(&mut self, bits: &[Self::Bit]) -> Result<Vec<u64>, Error>;
    /// Open only the lanes selected by `mask`; the other lanes stay hidden
    /// and are returned as zero.
    fn open_lanes(&mut self, bits: &[Self::Bit], mask: u64) -> Result<Vec<u64>, Error>;
    fn agree(&mut self, root: [u8; 32]) -> Result<(), Error>;
    fn poison(&mut self);

    fn fconstant(&self, value: Value, d: Domain) -> FieldWord;
    /// Scale lane `i` by the public `by[i]`.
    fn fscale_lanes(&self, a: &FieldWord, by: &[Value], d: Domain) -> FieldWord;
    fn fadd(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord;
    fn fsub(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord;
    fn fscale(&self, a: &FieldWord, b: Value, d: Domain) -> FieldWord;
    /// Fresh uniformly random shared field word.
    fn frandom(&mut self, d: Domain) -> Result<FieldWord, Error>;
    fn fmul_many(
        &mut self,
        pairs: &[(&FieldWord, &FieldWord)],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error>;
    fn fopen_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Vec<Value>>, Error>;
    fn bits_to_field_many(
        &mut self,
        words: &[Word<Self::Bit>],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error>;
    fn field_to_bits_many(
        &mut self,
        words: &[&FieldWord],
        d: Domain,
    ) -> Result<Vec<Word<Self::Bit>>, Error>;
    fn lift_bits_many(&mut self, bits: &[Self::Bit], d: Domain) -> Result<Vec<FieldWord>, Error>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidConfiguration,
    Transport,
    Authentication(usize),
    Disagreement(usize),
    MultiplicationCheck,
    InvalidTape,
    InvalidProof,
    MissingPreprocessing,
}

/// Authenticated envelopes also require confidential delivery. Implementations
/// must deliver each envelope only to its recipient; broadcasting is unsafe.
pub trait Transport: Send {
    /// General quorum delivery, ordered by the configured quorum with self omitted.
    /// Each envelope must remain confidential to its recipient.
    fn exchange_many(&mut self, _outgoing: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
        Err(Error::InvalidConfiguration)
    }

    /// Preprocessing for this stream, consumed in request order. Every quorum
    /// member must serve the same positions of the same ceremony output under
    /// its MAC key shares. Material is used once, including across aborts; a
    /// stream that runs dry fails closed. See `threshold_prep`.
    fn take_boolean_triples(&mut self, _count: usize) -> Result<Vec<BooleanTriple>, Error> {
        Err(Error::MissingPreprocessing)
    }
    fn take_auth_words(&mut self, _count: usize) -> Result<Vec<AuthWord>, Error> {
        Err(Error::MissingPreprocessing)
    }
    fn take_field_triples(
        &mut self,
        _field: ThresholdField,
        _count: usize,
    ) -> Result<Vec<FieldTriple>, Error> {
        Err(Error::MissingPreprocessing)
    }
    fn take_field_randoms(
        &mut self,
        _field: ThresholdField,
        _count: usize,
    ) -> Result<Vec<FieldShare>, Error> {
        Err(Error::MissingPreprocessing)
    }
    fn take_dabits(
        &mut self,
        _field: ThresholdField,
        _count: usize,
    ) -> Result<Vec<DaBitWord>, Error> {
        Err(Error::MissingPreprocessing)
    }
}

/// Wire envelope. Authentication binds the session, identities and sequence.
pub struct Envelope {
    pub sender: usize,
    pub recipient: usize,
    pub sequence: u64,
    pub payload: Vec<u64>,
    pub tag: [u8; 32],
}
impl Drop for Envelope {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.payload);
    }
}

/// Word-oriented view of the workspace SHAKE256 sponge: 64-bit words are
/// absorbed and squeezed in little-endian byte order.
/// Replicated additive field shares, with one entry per repetition lane.
pub(crate) type FieldWord = SecretVec<[Value; 2]>;

/// Per-word sums and the carry out of each word.
pub(crate) type SumsAndCarries<B> = (Vec<Word<B>>, Word<B>);

/// Backend-independent gadgets over any [`Core`] engine.
pub(crate) trait Gadgets: Core {
    fn and(&mut self, pairs: &[(Self::Bit, Self::Bit)]) -> Result<Word<Self::Bit>, Error> {
        let mut out = SecretVec::with_capacity(pairs.len());
        self.and_into(pairs, &mut out)?;
        Ok(out)
    }

    fn number(&self, x: Value, n: usize) -> Word<Self::Bit> {
        (0..n)
            .map(|i| {
                self.constant(if i < 384 && (x[i / 64] >> (i % 64)) & 1 != 0 {
                    u64::MAX
                } else {
                    0
                })
            })
            .collect()
    }

    fn xor(&self, a: &[Self::Bit], b: &[Self::Bit]) -> Word<Self::Bit> {
        a.iter().zip(b).map(|(&a, &b)| a ^ b).collect()
    }

    fn select_many(
        &mut self,
        conds: &[Self::Bit],
        a_words: &[Word<Self::Bit>],
        b_words: &[Word<Self::Bit>],
    ) -> Result<Vec<Word<Self::Bit>>, Error> {
        if a_words.is_empty() {
            return Ok(Vec::new());
        }
        let width = a_words[0].len();
        let mut pairs = SecretVec::with_capacity(a_words.len() * width);
        for ((&c, a), b) in conds.iter().zip(a_words).zip(b_words) {
            for (&ai, &bi) in a.iter().zip(b) {
                pairs.push((c, ai ^ bi));
            }
        }
        let prods = self.and(&pairs)?;
        let mut out = Vec::with_capacity(a_words.len());
        for (b, chunk) in b_words.iter().zip(prods.chunks_exact(width)) {
            out.push(chunk.iter().zip(b).map(|(&p, &bi)| p ^ bi).collect());
        }
        Ok(out)
    }

    /// Vectorized 1-AND-per-bit Boyar-Peralta adder across `K` words in parallel.
    fn add_many(
        &mut self,
        a_words: &[Word<Self::Bit>],
        b_words: &[Word<Self::Bit>],
        carry_mask: u64,
    ) -> Result<SumsAndCarries<Self::Bit>, Error> {
        if a_words.is_empty() {
            return Ok((Vec::new(), SecretVec::new()));
        }
        let k = a_words.len();
        let n = a_words[0].len();
        let mut sums: Vec<Word<Self::Bit>> = (0..k).map(|_| SecretVec::with_capacity(n)).collect();
        let mut carries: Word<Self::Bit> = vec![self.constant(carry_mask); k].into();
        let zero = self.constant(0);
        let mut pairs = SecretVec::with_capacity(k);
        pairs.resize(k, (zero, zero));
        let mut prods = SecretVec::with_capacity(k);
        for bit in 0..n {
            for (pair_slot, ((a, b), (&c, sum_w))) in pairs.iter_mut().zip(
                a_words
                    .iter()
                    .zip(b_words)
                    .zip(carries.iter().zip(&mut sums)),
            ) {
                let ai = a[bit];
                let bi = b[bit];
                sum_w.push(ai ^ bi ^ c);
                *pair_slot = (ai ^ c, bi ^ c);
            }
            self.and_into(&pairs, &mut prods)?;
            for (c, &p) in carries.iter_mut().zip(&prods) {
                *c = *c ^ p;
            }
        }
        Ok((sums, carries))
    }

    /// Vectorized addition of `a_words` with a public constant `k_val` (`1` `AND` per bit).
    fn add_public_many(
        &mut self,
        a_words: &[Word<Self::Bit>],
        k_val: Value,
        carry_mask: u64,
        width: usize,
    ) -> Result<SumsAndCarries<Self::Bit>, Error> {
        if a_words.is_empty() {
            return Ok((Vec::new(), SecretVec::new()));
        }
        let k = a_words.len();
        let k_bits = self.number(k_val, width);
        let mut sums: Vec<Word<Self::Bit>> =
            (0..k).map(|_| SecretVec::with_capacity(width)).collect();
        let mut carries: Word<Self::Bit> = vec![self.constant(carry_mask); k].into();
        let zero = self.constant(0);
        let mut pairs = SecretVec::with_capacity(k);
        pairs.resize(k, (zero, zero));
        let mut prods = SecretVec::with_capacity(k);
        for (bit, &kb) in k_bits.iter().enumerate() {
            for (pair_slot, (a, (&c, sum_w))) in pairs
                .iter_mut()
                .zip(a_words.iter().zip(carries.iter().zip(&mut sums)))
            {
                let ai = a[bit];
                sum_w.push(ai ^ kb ^ c);
                *pair_slot = (ai ^ c, kb ^ c);
            }
            self.and_into(&pairs, &mut prods)?;
            for (c, &p) in carries.iter_mut().zip(&prods) {
                *c = *c ^ p;
            }
        }
        Ok((sums, carries))
    }

    /// Check `v < d.modulus()` across `v_words` (`width == d.width()`).
    /// Since `p = 2^n - c`, `v < p <==> v + c < 2^n <==> carry_out_n(v + c) == 0`.
    fn less_than_modulus_many(
        &mut self,
        v_words: &[Word<Self::Bit>],
        d: Domain,
    ) -> Result<Word<Self::Bit>, Error> {
        if v_words.is_empty() {
            return Ok(SecretVec::new());
        }
        let (_, carries) = self.add_public_many(v_words, domain_c_const(d), 0, d.width())?;
        let ones = self.constant(u64::MAX);
        Ok(carries.into_iter().map(|ge| ge ^ ones).collect())
    }

    fn field_add_many(
        &mut self,
        a_words: &[Word<Self::Bit>],
        b_words: &[Word<Self::Bit>],
        d: Domain,
    ) -> Result<Vec<Word<Self::Bit>>, Error> {
        if a_words.is_empty() {
            return Ok(Vec::new());
        }
        if d == Domain::Bit {
            return Ok(a_words
                .iter()
                .zip(b_words)
                .map(|(a, b)| self.xor(a, b))
                .collect());
        }
        let n = d.width();
        let (sums, overflow) = self.add_many(a_words, b_words, 0)?;
        // `0 <= a + b < 2p = 2^(n+1) - 2c`, so `overflow` and `carry_c` are mutually exclusive.
        let (diffs, carry_c) = self.add_public_many(&sums, domain_c_const(d), 0, n)?;
        let ge: Word<Self::Bit> = overflow
            .into_iter()
            .zip(carry_c)
            .map(|(ov, cc)| ov ^ cc)
            .collect();
        self.select_many(&ge, &diffs, &sums)
    }

    fn fmul(&mut self, a: &FieldWord, b: &FieldWord, d: Domain) -> Result<FieldWord, Error> {
        Ok(self.fmul_many(&[(a, b)], d)?.pop().unwrap())
    }

    #[cfg(test)]
    fn bits_to_field(&mut self, v: &[Self::Bit], d: Domain) -> Result<FieldWord, Error> {
        Ok(self
            .bits_to_field_many(&[v.iter().copied().collect()], d)?
            .pop()
            .unwrap())
    }

    #[cfg(test)]
    fn field_to_bits(&mut self, v: &FieldWord, d: Domain) -> Result<Word<Self::Bit>, Error> {
        Ok(self.field_to_bits_many(&[v], d)?.pop().unwrap())
    }

    /// Lane-wise inverse of a shared field word whose lanes must all be nonzero.
    ///
    /// The only thing a zero operand discloses is that some lane is zero. Opening
    /// `a[i] * mask[i]` directly would show every party which lanes are zero, so
    /// the product of all lanes is tested first: six rotate-and-multiply rounds
    /// leave that one product in every lane, and it is opened under a fresh
    /// uniform mask. The opened word is all zero exactly when some lane of `a` is
    /// zero (up to all 64 mask lanes being zero), so it does not depend on which
    /// lane or on how many. Only after that test passes are the per-lane masked
    /// products opened, and then a zero can come from the mask alone.
    fn finverse(&mut self, a: &FieldWord, d: Domain) -> Result<FieldWord, Error> {
        if a.len() != BIT_LANES {
            self.poison();
            return Err(Error::InvalidConfiguration);
        }
        let mut all: FieldWord = a.iter().copied().collect();
        for shift in [1, 2, 4, 8, 16, 32] {
            let rotated: FieldWord = (0..BIT_LANES)
                .map(|lane| all[(lane + shift) % BIT_LANES])
                .collect();
            all = self.fmul(&all, &rotated, d)?;
        }
        let gate_mask = self.frandom(d)?;
        let gate = self.fmul(&all, &gate_mask, d)?;
        let gate = self.fopen_many(&[gate], d)?;
        let nonzero = gate[0]
            .iter()
            .fold(0u64, |acc, v| acc | v[0] | v[1] | v[2] | v[3] | v[4] | v[5]);
        if nonzero == 0 {
            self.poison();
            return Err(Error::InvalidProof);
        }
        // Every lane of `a` is nonzero here, so a zero below is a zero mask lane,
        // which is independent of `a`; that mask is discarded and redrawn.
        for _ in 0..3 {
            let mask = self.frandom(d)?;
            let product = self.fmul(a, &mask, d)?;
            let opened = self.fopen_many(&[product], d)?;
            if opened[0].contains(&ZERO) {
                continue;
            }
            let inverses: Vec<Value> = opened[0].iter().map(|u| d.inverse(*u)).collect();
            return Ok(self.fscale_lanes(&mask, &inverses, d));
        }
        self.poison();
        Err(Error::InvalidProof)
    }
}
impl<E: Core> Gadgets for E {}

fn domain_c_const(d: Domain) -> Value {
    match d {
        Domain::Ed => [19, 0, 0, 0, 0, 0],
        Domain::Secp => [0x1_0000_03d1, 0, 0, 0, 0, 0],
        Domain::Gold => [0xffff_ffff, 0, 0, 0, 0, 0],
        Domain::PallasFp => crate::limbs::sbb([0, 0, 0, 1u64 << 63, 0, 0], d.modulus()).0,
        Domain::BlsFp => crate::limbs::sbb([0, 0, 0, 0, 0, 1u64 << 61], d.modulus()).0,
        Domain::Bit => ZERO,
    }
}
