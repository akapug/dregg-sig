//! Authenticated arithmetic over Goldilocks for a quorum of custodians.
//!
//! SPDZ over additive shares (Damgard, Pastro, Smart, Zakarias, CRYPTO 2012; the MAC check
//! is the commit-then-open check of SPDZ-2, Damgard et al., ESORICS 2013). A shared value
//! `x` is held as additive shares of `x` and of `alpha_0 x`, `alpha_1 x` for two
//! Goldilocks keys that are themselves additively shared. An extension-field value carries the same
//! two base-field keys limb by limb, so multiplying a share by a public extension element
//! is local.
//!
//! * Opening a value sends the value shares and queues the MAC shares.
//! * [`Engine::check`] settles the queue: every party commits to its share of
//!   `sum_j r_j (m_j - alpha x_j)` for coefficients `r_j` derived from the transcript of
//!   everything sent so far, then opens it; the shares must sum to zero for both keys. A
//!   wrong opened value passes with probability at most `2 / p^2 < 2^-126`.
//! * The same check compares every party's hash of all messages sent and received, so a
//!   custodian that tells different custodians different things is caught there.
//! * A multiplication consumes one Beaver triple and opens two masked values.
//!
//! Nothing here decides *when* to check. The rule the callers follow is in the module
//! comment of [`super`]: a value masked by fresh preprocessing may be opened before the
//! check, anything else only after it.

#[cfg(any(test, feature = "test-dealer"))]
use alloc::vec;
use alloc::vec::Vec;

use dregg_sig_agg::field::{Goldilocks, GoldilocksExt4, GoldilocksOps as _};
use dregg_sig_agg::sponge::cshake256_32;
use dregg_sig_agg::zk_hem::SeedStream;

use super::net::{NetError, Transport};

type F = Goldilocks;
type E = GoldilocksExt4;

/// One party's share of an authenticated base-field value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sb {
    pub v: F,
    pub m: [F; 2],
}

/// One party's share of an authenticated extension-field value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sh {
    pub v: E,
    pub m: [E; 2],
}

impl Sb {
    pub const ZERO: Self = Self {
        v: F::ZERO,
        m: [F::ZERO; 2],
    };

    #[inline]
    pub fn scale(self, k: F) -> Self {
        Self {
            v: self.v * k,
            m: [self.m[0] * k, self.m[1] * k],
        }
    }

    /// The share times a public extension element.
    #[inline]
    pub fn scale_ext(self, k: E) -> Sh {
        Sh {
            v: k.mul_base(self.v),
            m: [k.mul_base(self.m[0]), k.mul_base(self.m[1])],
        }
    }

    #[inline]
    pub fn lift(self) -> Sh {
        Sh {
            v: E::from_base(self.v),
            m: [E::from_base(self.m[0]), E::from_base(self.m[1])],
        }
    }
}

impl core::ops::Add for Sb {
    type Output = Self;
    #[inline]
    fn add(self, r: Self) -> Self {
        Self {
            v: self.v + r.v,
            m: [self.m[0] + r.m[0], self.m[1] + r.m[1]],
        }
    }
}

impl core::ops::Sub for Sb {
    type Output = Self;
    #[inline]
    fn sub(self, r: Self) -> Self {
        Self {
            v: self.v - r.v,
            m: [self.m[0] - r.m[0], self.m[1] - r.m[1]],
        }
    }
}

impl core::ops::AddAssign for Sb {
    #[inline]
    fn add_assign(&mut self, r: Self) {
        *self = *self + r;
    }
}

impl Sh {
    pub const ZERO: Self = Self {
        v: E::ZERO,
        m: [E::ZERO; 2],
    };

    #[inline]
    pub fn scale(self, k: E) -> Self {
        Self {
            v: self.v * k,
            m: [self.m[0] * k, self.m[1] * k],
        }
    }

    /// Limb `j` of the value, as a base-field share.
    #[inline]
    pub fn limb(self, j: usize) -> Sb {
        Sb {
            v: self.v.to_limbs()[j],
            m: [self.m[0].to_limbs()[j], self.m[1].to_limbs()[j]],
        }
    }
}

impl core::ops::Add for Sh {
    type Output = Self;
    #[inline]
    fn add(self, r: Self) -> Self {
        Self {
            v: self.v + r.v,
            m: [self.m[0] + r.m[0], self.m[1] + r.m[1]],
        }
    }
}

impl core::ops::Sub for Sh {
    type Output = Self;
    #[inline]
    fn sub(self, r: Self) -> Self {
        Self {
            v: self.v - r.v,
            m: [self.m[0] - r.m[0], self.m[1] - r.m[1]],
        }
    }
}

impl core::ops::AddAssign for Sh {
    #[inline]
    fn add_assign(&mut self, r: Self) {
        *self = *self + r;
    }
}

/// One party's one-use material: its shares of the two MAC keys, of Beaver triples
/// `(a, b, a b)` and of uniform values, all over the base field. Every party consumes
/// its store in the same order.
pub struct Preprocessing {
    pub key: [F; 2],
    pub triples: Vec<[Sb; 3]>,
    pub randoms: Vec<Sb>,
}

impl Drop for Preprocessing {
    fn drop(&mut self) {
        dregg_sig_asm::volatile_fill(&mut self.key, F::ZERO);
        dregg_sig_asm::volatile_fill(&mut self.triples, [Sb::ZERO; 3]);
        dregg_sig_asm::volatile_fill(&mut self.randoms, Sb::ZERO);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MpcError {
    Net(NetError),
    /// A message has the wrong length or a non-canonical field element.
    Malformed {
        from: usize,
    },
    OutOfTriples,
    OutOfRandoms,
    /// The batch MAC check failed: some opened value was wrong.
    MacCheck,
    /// Two parties hold different transcripts of the broadcast messages.
    Equivocation,
    /// A party's opened check value does not match its commitment.
    BadCommitment {
        from: usize,
    },
}

impl From<NetError> for MpcError {
    fn from(e: NetError) -> Self {
        Self::Net(e)
    }
}

/// What one party sent and consumed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Payload bytes sent, summed over all peers.
    pub bytes_sent: u64,
    /// Broadcast rounds.
    pub rounds: u64,
    pub triples_used: u64,
    pub randoms_used: u64,
    pub mac_checks: u64,
}

const COIN_DOMAIN: &[u8] = b"QSAG.COLLAB.MAC.COINS/v1";
const COMMIT_DOMAIN: &[u8] = b"QSAG.COLLAB.MAC.COMMIT/v1";
const ECHO_DOMAIN: &[u8] = b"QSAG.COLLAB.ECHO/v1";
const LOCAL_DOMAIN: &[u8] = b"QSAG.COLLAB.LOCAL/v1";

/// One custodian's side of the authenticated computation.
pub struct Engine<T: Transport> {
    net: T,
    prep: Preprocessing,
    t_used: usize,
    r_used: usize,
    /// Opened values awaiting the MAC check, with this party's MAC shares.
    pending: Vec<(E, [E; 2])>,
    /// Hash chain over every broadcast round.
    echo: [u8; 32],
    local: SeedStream,
    pub stats: Stats,
}

fn put_base(out: &mut Vec<u8>, v: F) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn put_ext(out: &mut Vec<u8>, v: E) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn get_base(bytes: &[u8]) -> Option<Vec<F>> {
    if bytes.len() % 8 != 0 {
        return None;
    }
    bytes
        .chunks_exact(8)
        .map(|c| F::from_canonical_u64(u64::from_le_bytes(c.try_into().ok()?)))
        .collect()
}

fn get_ext(bytes: &[u8]) -> Option<Vec<E>> {
    if bytes.len() % 32 != 0 {
        return None;
    }
    bytes
        .chunks_exact(32)
        .map(|c| E::from_le_bytes_canonical(c.try_into().ok()?))
        .collect()
}

impl<T: Transport> Engine<T> {
    /// `local_seed` is this party's private randomness; it must be uniform and never
    /// reused across runs.
    pub fn new(net: T, prep: Preprocessing, session: &[u8; 32], local_seed: &[u8; 32]) -> Self {
        Self {
            net,
            prep,
            t_used: 0,
            r_used: 0,
            pending: Vec::new(),
            echo: cshake256_32(ECHO_DOMAIN, session),
            local: SeedStream::new(LOCAL_DOMAIN, local_seed),
            stats: Stats::default(),
        }
    }

    #[inline]
    pub fn me(&self) -> usize {
        self.net.me()
    }

    #[inline]
    pub fn parties(&self) -> usize {
        self.net.parties()
    }

    /// A uniform base-field element known to this party only.
    pub fn local_base(&mut self) -> F {
        self.local.next_base()
    }

    /// Triples and randoms not yet consumed.
    pub fn remaining(&self) -> (usize, usize) {
        (
            self.prep.triples.len() - self.t_used,
            self.prep.randoms.len() - self.r_used,
        )
    }

    /// Broadcast `payload` and collect one message from every party, in party order (the
    /// own message included).
    pub fn exchange(&mut self, payload: Vec<u8>) -> Result<Vec<Vec<u8>>, MpcError> {
        let (me, n) = (self.me(), self.parties());
        for p in (0..n).filter(|&p| p != me) {
            self.net.send(p, &payload)?;
        }
        self.stats.bytes_sent += (payload.len() * (n - 1)) as u64;
        self.stats.rounds += 1;
        let mut all = Vec::with_capacity(n);
        for p in 0..n {
            if p == me {
                all.push(Vec::new());
            } else {
                all.push(self.net.recv(p)?);
            }
        }
        all[me] = payload;
        let mut chain = self.echo.to_vec();
        for msg in &all {
            chain.extend_from_slice(&(msg.len() as u64).to_le_bytes());
            chain.extend_from_slice(&cshake256_32(ECHO_DOMAIN, msg));
        }
        self.echo = cshake256_32(ECHO_DOMAIN, &chain);
        Ok(all)
    }

    /// The share of a public constant.
    #[inline]
    pub fn public(&self, c: F) -> Sb {
        Sb {
            v: if self.me() == 0 { c } else { F::ZERO },
            m: [self.prep.key[0] * c, self.prep.key[1] * c],
        }
    }

    /// The share of a public extension-field constant.
    #[inline]
    pub fn public_ext(&self, c: E) -> Sh {
        Sh {
            v: if self.me() == 0 { c } else { E::ZERO },
            m: [c.mul_base(self.prep.key[0]), c.mul_base(self.prep.key[1])],
        }
    }

    /// The next preprocessed uniform value.
    pub fn random(&mut self) -> Result<Sb, MpcError> {
        let r = *self
            .prep
            .randoms
            .get(self.r_used)
            .ok_or(MpcError::OutOfRandoms)?;
        self.prep.randoms[self.r_used] = Sb::ZERO;
        self.r_used += 1;
        self.stats.randoms_used += 1;
        Ok(r)
    }

    /// A uniform extension-field value from four preprocessed base values.
    pub fn random_ext(&mut self) -> Result<Sh, MpcError> {
        let mut out = Sh::ZERO;
        for j in 0..4 {
            let mut unit = [F::ZERO; 4];
            unit[j] = F::ONE;
            out += self.random()?.scale_ext(E::from_limbs(unit));
        }
        Ok(out)
    }

    fn sum_opened<V: Copy + core::ops::Add<Output = V>>(
        all: Vec<Option<Vec<V>>>,
        len: usize,
    ) -> Result<Vec<V>, MpcError> {
        let mut total: Option<Vec<V>> = None;
        for (from, part) in all.into_iter().enumerate() {
            let part = part
                .filter(|p| p.len() == len)
                .ok_or(MpcError::Malformed { from })?;
            total = Some(match total {
                None => part,
                Some(mut acc) => {
                    for (a, &p) in acc.iter_mut().zip(&part) {
                        *a = *a + p;
                    }
                    acc
                }
            });
        }
        Ok(total.unwrap_or_default())
    }

    /// Open base-field values. Their MACs are queued for [`Self::check`].
    pub fn open(&mut self, shares: &[Sb]) -> Result<Vec<F>, MpcError> {
        let mut payload = Vec::with_capacity(8 * shares.len());
        for s in shares {
            put_base(&mut payload, s.v);
        }
        let all = self.exchange(payload)?;
        let opened = Self::sum_opened(all.iter().map(|m| get_base(m)).collect(), shares.len())?;
        self.pending
            .extend(opened.iter().zip(shares).map(|(&x, s)| {
                (
                    E::from_base(x),
                    [E::from_base(s.m[0]), E::from_base(s.m[1])],
                )
            }));
        Ok(opened)
    }

    /// Open extension-field values. Their MACs are queued for [`Self::check`].
    pub fn open_ext(&mut self, shares: &[Sh]) -> Result<Vec<E>, MpcError> {
        let mut payload = Vec::with_capacity(32 * shares.len());
        for s in shares {
            put_ext(&mut payload, s.v);
        }
        let all = self.exchange(payload)?;
        let opened = Self::sum_opened(all.iter().map(|m| get_ext(m)).collect(), shares.len())?;
        self.pending
            .extend(opened.iter().zip(shares).map(|(&x, s)| (x, s.m)));
        Ok(opened)
    }

    /// Settle every opening made since the last check, and compare transcripts.
    pub fn check(&mut self) -> Result<(), MpcError> {
        self.stats.mac_checks += 1;
        let echo = self.echo;
        let mut coins = SeedStream::new(COIN_DOMAIN, &echo);
        let mut sigma = [E::ZERO; 2];
        for (x, m) in self.pending.drain(..) {
            let r = coins.next_ext4();
            for k in 0..2 {
                sigma[k] += r * (m[k] - x.mul_base(self.prep.key[k]));
            }
        }
        let mut opening = Vec::with_capacity(128);
        put_ext(&mut opening, sigma[0]);
        put_ext(&mut opening, sigma[1]);
        opening.extend_from_slice(&echo);
        for _ in 0..4 {
            opening.extend_from_slice(&self.local.next_base().to_le_bytes());
        }
        let commitments = self.exchange(cshake256_32(COMMIT_DOMAIN, &opening).to_vec())?;
        let openings = self.exchange(opening)?;
        let mut total = [E::ZERO; 2];
        for (from, (commitment, opened)) in commitments.iter().zip(&openings).enumerate() {
            if opened.len() != 128 || commitment[..] != cshake256_32(COMMIT_DOMAIN, opened)[..] {
                return Err(MpcError::BadCommitment { from });
            }
            if opened[64..96] != echo[..] {
                return Err(MpcError::Equivocation);
            }
            let parts = get_ext(&opened[..64]).ok_or(MpcError::Malformed { from })?;
            total[0] += parts[0];
            total[1] += parts[1];
        }
        if total != [E::ZERO; 2] {
            return Err(MpcError::MacCheck);
        }
        Ok(())
    }

    /// Whether any opening awaits a check.
    pub fn has_pending(&self) -> bool {
        !self.pending.is_empty()
    }

    /// Products of base-field values: one triple and two masked openings each.
    pub fn mul(&mut self, xs: &[Sb], ys: &[Sb]) -> Result<Vec<Sb>, MpcError> {
        Ok(self.mul_open(xs, ys, &[])?.0)
    }

    /// The products `xs[i] ys[i]` and the values of `opens`, in one round: the masked
    /// openings of the products and the plain openings travel in the same exchange.
    #[allow(clippy::type_complexity)]
    pub fn mul_open(
        &mut self,
        xs: &[Sb],
        ys: &[Sb],
        opens: &[Sb],
    ) -> Result<(Vec<Sb>, Vec<F>), MpcError> {
        assert_eq!(xs.len(), ys.len());
        let n = xs.len();
        if self.prep.triples.len() - self.t_used < n {
            return Err(MpcError::OutOfTriples);
        }
        let triples = &self.prep.triples[self.t_used..self.t_used + n];
        let mut masked = Vec::with_capacity(2 * n + opens.len());
        for ((x, y), t) in xs.iter().zip(ys).zip(triples) {
            masked.push(*x - t[0]);
            masked.push(*y - t[1]);
        }
        masked.extend_from_slice(opens);
        let mut opened = self.open(&masked)?;
        let plain = opened.split_off(2 * n);
        let mut out = Vec::with_capacity(n);
        for (k, pair) in opened.chunks_exact(2).enumerate() {
            let (d, e) = (pair[0], pair[1]);
            let t = self.prep.triples[self.t_used + k];
            out.push(t[2] + t[1].scale(d) + t[0].scale(e) + self.public(d * e));
        }
        dregg_sig_asm::volatile_fill(
            &mut self.prep.triples[self.t_used..self.t_used + n],
            [Sb::ZERO; 3],
        );
        self.t_used += n;
        self.stats.triples_used += n as u64;
        Ok((out, plain))
    }

    /// Products of extension-field values: sixteen base products of limbs each.
    pub fn mul_ext(&mut self, xs: &[Sh], ys: &[Sh]) -> Result<Vec<Sh>, MpcError> {
        assert_eq!(xs.len(), ys.len());
        let unit = |j: usize| {
            let mut limbs = [F::ZERO; 4];
            limbs[j] = F::ONE;
            E::from_limbs(limbs)
        };
        let weights: [E; 16] = core::array::from_fn(|k| unit(k / 4) * unit(k % 4));
        let mut a = Vec::with_capacity(16 * xs.len());
        let mut b = Vec::with_capacity(16 * xs.len());
        for (x, y) in xs.iter().zip(ys) {
            for k in 0..16 {
                a.push(x.limb(k / 4));
                b.push(y.limb(k % 4));
            }
        }
        let products = self.mul(&a, &b)?;
        Ok(products
            .chunks_exact(16)
            .map(|group| {
                group
                    .iter()
                    .zip(&weights)
                    .fold(Sh::ZERO, |acc, (p, &w)| acc + p.scale_ext(w))
            })
            .collect())
    }

    /// Party `owner` contributes private base-field values; every party gets shares of
    /// them. `values` is `Some` for the owner and `None` for everyone else. One
    /// preprocessed random per value.
    ///
    /// The mask is opened to the owner without a MAC check, so another party can shift
    /// the owner's input by a value of its choice. That is an input substitution, not a
    /// leak: the shifted value is still masked by the uniform mask.
    pub fn input(
        &mut self,
        owner: usize,
        values: Option<&[F]>,
        count: usize,
    ) -> Result<Vec<Sb>, MpcError> {
        let (me, n) = (self.me(), self.parties());
        let masks: Vec<Sb> = (0..count)
            .map(|_| self.random())
            .collect::<Result<_, _>>()?;
        if me != owner {
            let mut payload = Vec::with_capacity(8 * count);
            for mask in &masks {
                put_base(&mut payload, mask.v);
            }
            self.net.send(owner, &payload)?;
            self.stats.bytes_sent += payload.len() as u64;
            let eps = get_base(&self.net.recv(owner)?)
                .filter(|e| e.len() == count)
                .ok_or(MpcError::Malformed { from: owner })?;
            return Ok(masks
                .iter()
                .zip(eps)
                .map(|(&mask, e)| mask + self.public(e))
                .collect());
        }
        let values = values
            .filter(|v| v.len() == count)
            .expect("the owner's values");
        let mut clear: Vec<F> = masks.iter().map(|mask| mask.v).collect();
        for p in (0..n).filter(|&p| p != me) {
            let part = get_base(&self.net.recv(p)?)
                .filter(|e| e.len() == count)
                .ok_or(MpcError::Malformed { from: p })?;
            for (c, s) in clear.iter_mut().zip(part) {
                *c += s;
            }
        }
        let eps: Vec<F> = values.iter().zip(&clear).map(|(&x, &r)| x - r).collect();
        dregg_sig_asm::volatile_fill(&mut clear, F::ZERO);
        let mut payload = Vec::with_capacity(8 * count);
        for &e in &eps {
            put_base(&mut payload, e);
        }
        for p in (0..n).filter(|&p| p != me) {
            self.net.send(p, &payload)?;
        }
        self.stats.bytes_sent += (payload.len() * (n - 1)) as u64;
        Ok(masks
            .iter()
            .zip(eps)
            .map(|(&mask, e)| mask + self.public(e))
            .collect())
    }
}

/// A single generator that knows both MAC keys and every share. It stands in for the
/// preprocessing ceremony in tests and benchmarks and must never be compiled into a
/// deployment: whoever runs it can forge any opening.
#[cfg(any(test, feature = "test-dealer"))]
pub struct Dealer {
    parties: usize,
    key: [F; 2],
    key_shares: Vec<[F; 2]>,
    stream: SeedStream,
}

#[cfg(any(test, feature = "test-dealer"))]
impl Dealer {
    pub fn new(parties: usize, seed: &[u8; 32]) -> Self {
        assert!(parties >= 2);
        let mut stream = SeedStream::new(b"QSAG.COLLAB.TEST.DEALER/v1", seed);
        let key_shares: Vec<[F; 2]> = (0..parties)
            .map(|_| [stream.next_base(), stream.next_base()])
            .collect();
        let key = key_shares
            .iter()
            .fold([F::ZERO; 2], |acc, s| [acc[0] + s[0], acc[1] + s[1]]);
        Self {
            parties,
            key,
            key_shares,
            stream,
        }
    }

    /// Authenticated shares of `value`, one per party.
    pub fn share(&mut self, value: F) -> Vec<Sb> {
        let mut rest = Sb {
            v: value,
            m: [self.key[0] * value, self.key[1] * value],
        };
        let mut out = vec![Sb::ZERO; self.parties];
        for slot in &mut out[1..] {
            *slot = Sb {
                v: self.stream.next_base(),
                m: [self.stream.next_base(), self.stream.next_base()],
            };
            rest = rest - *slot;
        }
        out[0] = rest;
        out
    }

    /// Every party's store with `triples` triples and `randoms` uniform values.
    pub fn preprocessing(&mut self, triples: usize, randoms: usize) -> Vec<Preprocessing> {
        let mut out: Vec<Preprocessing> = self
            .key_shares
            .iter()
            .map(|&key| Preprocessing {
                key,
                triples: Vec::with_capacity(triples),
                randoms: Vec::with_capacity(randoms),
            })
            .collect();
        for _ in 0..triples {
            let (a, b) = (self.stream.next_base(), self.stream.next_base());
            let (sa, sb, sc) = (self.share(a), self.share(b), self.share(a * b));
            for (p, prep) in out.iter_mut().enumerate() {
                prep.triples.push([sa[p], sb[p], sc[p]]);
            }
        }
        for _ in 0..randoms {
            let r = self.stream.next_base();
            let sr = self.share(r);
            for (p, prep) in out.iter_mut().enumerate() {
                prep.randoms.push(sr[p]);
            }
        }
        out
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::super::net::{ChannelLink, Framed, channel_mesh};
    use super::*;

    pub(in super::super) type TestEngine = Engine<Framed<ChannelLink>>;

    /// Run `party` for every custodian on its own thread over a channel mesh.
    pub(in super::super) fn run_parties<R: Send>(
        preps: Vec<Preprocessing>,
        party: impl Fn(TestEngine) -> R + Sync,
    ) -> Vec<R> {
        let session = [9u8; 32];
        let mesh = channel_mesh(session, preps.len());
        std::thread::scope(|scope| {
            let handles: Vec<_> = mesh
                .into_iter()
                .zip(preps)
                .enumerate()
                .map(|(p, (net, prep))| {
                    let party = &party;
                    scope.spawn(move || {
                        party(Engine::new(net, prep, &session, &[p as u8 + 100; 32]))
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    }

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    #[test]
    fn products_openings_and_inputs_are_correct_for_every_quorum_size() {
        for parties in [2usize, 3, 5] {
            let mut dealer = Dealer::new(parties, &[1; 32]);
            let (x, y) = (f(123_456_789), f(987_654_321_012));
            let (sx, sy) = (dealer.share(x), dealer.share(y));
            let preps = dealer.preprocessing(40, 12);
            let secret = f(77);
            let out = run_parties(preps, |mut e| {
                let me = e.me();
                let prod = e.mul(&[sx[me]], &[sy[me]]).unwrap()[0];
                let sum = prod + e.public(f(5)) - sx[me].scale(f(2));
                let rx = e.random_ext().unwrap();
                let ext = e
                    .mul_ext(&[sx[me].scale_ext(E::V), rx], &[sy[me].lift(), rx])
                    .unwrap();
                let input = e.input(1, (me == 1).then_some(&[secret][..]), 1).unwrap()[0];
                let opened = e.open(&[prod, sum, input]).unwrap();
                let opened_ext = e.open_ext(&[ext[0], ext[1], rx]).unwrap();
                e.check().unwrap();
                assert!(!e.has_pending());
                (opened, opened_ext, e.stats)
            });
            for (opened, opened_ext, stats) in &out {
                assert_eq!(opened, &[x * y, x * y + f(5) - x * f(2), secret]);
                assert_eq!(opened_ext[0], E::V.mul_base(x) * E::from_base(y));
                assert_eq!(opened_ext[1], opened_ext[2] * opened_ext[2]);
                assert_eq!(stats.triples_used, 33);
                assert_eq!(stats.randoms_used, 5);
            }
        }
    }

    /// A party that opens a wrong value, sends a wrong MAC-check share, or tells two
    /// parties different things is caught at the check by every honest party.
    #[test]
    fn the_check_catches_wrong_openings_and_equivocation() {
        #[derive(Clone, Copy, PartialEq, Debug)]
        enum Cheat {
            None,
            Value,
            Mac,
            Key,
        }
        for cheat in [Cheat::None, Cheat::Value, Cheat::Mac, Cheat::Key] {
            let mut dealer = Dealer::new(3, &[2; 32]);
            let sx = dealer.share(f(41));
            let preps = dealer.preprocessing(0, 0);
            let out = run_parties(preps, |mut e| {
                let me = e.me();
                let mut share = sx[me];
                if me == 2 {
                    match cheat {
                        Cheat::None => {}
                        Cheat::Value => share.v += F::ONE,
                        Cheat::Mac => share.m[1] += F::ONE,
                        Cheat::Key => e.prep.key[0] += F::ONE,
                    }
                }
                let opened = e.open(&[share]).unwrap();
                (opened[0], e.check())
            });
            for (p, (value, verdict)) in out.iter().enumerate() {
                match cheat {
                    Cheat::None => assert_eq!((*value, *verdict), (f(41), Ok(()))),
                    _ => {
                        assert_eq!(*verdict, Err(MpcError::MacCheck), "party {p} {cheat:?}");
                        assert_eq!(*value, if cheat == Cheat::Value { f(42) } else { f(41) });
                    }
                }
            }
        }

        // Equivocation: party 2 sends party 0 another value than party 1.
        let mut dealer = Dealer::new(3, &[3; 32]);
        let sx = dealer.share(f(9));
        let preps = dealer.preprocessing(0, 0);
        let out = run_parties(preps, |mut e| {
            let me = e.me();
            if me == 2 {
                let mut to0 = Vec::new();
                put_base(&mut to0, sx[me].v + F::ONE);
                let mut to1 = Vec::new();
                put_base(&mut to1, sx[me].v);
                e.net.send(0, &to0).unwrap();
                e.net.send(1, &to1).unwrap();
                let _ = (e.net.recv(0).unwrap(), e.net.recv(1).unwrap());
                // It then follows the check with either transcript; both are refused.
                e.echo = [0; 32];
                return e.check();
            }
            e.open(&[sx[me]]).unwrap();
            e.check()
        });
        assert!(out[..2].iter().all(|v| v.is_err()));
        assert!(
            out[..2].contains(&Err(MpcError::Equivocation))
                || out[..2].contains(&Err(MpcError::MacCheck))
        );
    }

    #[test]
    fn exhausted_preprocessing_fails_closed() {
        let mut dealer = Dealer::new(2, &[4; 32]);
        let sx = dealer.share(f(3));
        let preps = dealer.preprocessing(1, 0);
        let out = run_parties(preps, |mut e| {
            let me = e.me();
            let twice = e.mul(&[sx[me], sx[me]], &[sx[me], sx[me]]).map(|_| ());
            (twice, e.random().map(|_| ()), e.remaining())
        });
        for o in out {
            assert_eq!(
                o,
                (
                    Err(MpcError::OutOfTriples),
                    Err(MpcError::OutOfRandoms),
                    (1, 0)
                )
            );
        }
    }
}
