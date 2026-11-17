//! Message transport between custodians.
//!
//! A [`Transport`] gives one custodian an ordered, reliable byte-message link to every
//! other custodian. [`Framed`] builds one from raw [`Link`]s and puts every message in a
//! frame
//!
//! ```text
//! magic[4] || session[32] || from_be[2] || to_be[2] || seq_be[8] || len_be[4] || payload
//! ```
//!
//! and accepts a frame only if every header field is the expected one: this session, the
//! peer the link belongs to, the local party, and the next sequence number of that
//! directed link. Frames are neither encrypted nor authenticated. The protocol needs
//! private authenticated pairwise links for the Stage-0 trees to stay private from
//! outsiders and for abort to mean a custodian misbehaved; a thread channel is one, a
//! socket needs a secure channel beneath it.

use alloc::vec::Vec;

/// First bytes of every frame.
pub const FRAME_MAGIC: [u8; 4] = *b"QSCF";
/// Bytes before the payload.
pub const FRAME_HEADER_BYTES: usize = 4 + 32 + 2 + 2 + 8 + 4;
/// Largest payload of one frame.
pub const MAX_FRAME_PAYLOAD: usize = 1 << 30;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NetError {
    /// The link to `peer` is closed.
    Closed {
        peer: usize,
    },
    /// `peer` is the local party or not a party.
    UnknownPeer {
        peer: usize,
    },
    /// Not a frame for this link: bad magic, session, route, sequence number or length.
    BadFrame {
        peer: usize,
    },
    PayloadTooLarge,
}

/// One custodian's links to the others.
pub trait Transport {
    fn parties(&self) -> usize;
    fn me(&self) -> usize;
    fn send(&mut self, to: usize, payload: &[u8]) -> Result<(), NetError>;
    /// Blocks until the next message from `from` arrives.
    fn recv(&mut self, from: usize) -> Result<Vec<u8>, NetError>;
}

/// A raw bidirectional pipe to one peer that carries whole frames.
pub trait Link {
    fn send_frame(&mut self, frame: &[u8]) -> Result<(), ()>;
    /// The next frame: [`FRAME_HEADER_BYTES`] header bytes and the payload they declare.
    fn recv_frame(&mut self) -> Result<Vec<u8>, ()>;
}

pub fn encode_frame(session: &[u8; 32], from: u16, to: u16, seq: u64, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(FRAME_HEADER_BYTES + payload.len());
    out.extend_from_slice(&FRAME_MAGIC);
    out.extend_from_slice(session);
    out.extend_from_slice(&from.to_be_bytes());
    out.extend_from_slice(&to.to_be_bytes());
    out.extend_from_slice(&seq.to_be_bytes());
    out.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    out.extend_from_slice(payload);
    out
}

/// The payload of `frame` if its header is exactly the expected one.
pub fn decode_frame<'a>(
    frame: &'a [u8],
    session: &[u8; 32],
    from: u16,
    to: u16,
    seq: u64,
) -> Option<&'a [u8]> {
    let header = frame.get(..FRAME_HEADER_BYTES)?;
    let payload = &frame[FRAME_HEADER_BYTES..];
    let ok = header[..4] == FRAME_MAGIC
        && header[4..36] == session[..]
        && header[36..38] == from.to_be_bytes()
        && header[38..40] == to.to_be_bytes()
        && header[40..48] == seq.to_be_bytes()
        && header[48..52] == (payload.len() as u32).to_be_bytes()
        && payload.len() <= MAX_FRAME_PAYLOAD;
    ok.then_some(payload)
}

/// A [`Transport`] over one [`Link`] per peer.
pub struct Framed<L: Link> {
    session: [u8; 32],
    me: usize,
    /// `links[p]` for every `p != me`; the slot of `me` is `None`.
    links: Vec<Option<L>>,
    sent: Vec<u64>,
    received: Vec<u64>,
}

impl<L: Link> Framed<L> {
    /// `links[p]` must be `Some` exactly for `p != me`.
    pub fn new(session: [u8; 32], me: usize, links: Vec<Option<L>>) -> Option<Self> {
        let n = links.len();
        let shaped = n >= 2
            && n <= u16::MAX as usize
            && me < n
            && links
                .iter()
                .enumerate()
                .all(|(p, l)| l.is_some() == (p != me));
        shaped.then(|| Self {
            session,
            me,
            links,
            sent: alloc::vec![0; n],
            received: alloc::vec![0; n],
        })
    }
}

impl<L: Link> Transport for Framed<L> {
    fn parties(&self) -> usize {
        self.links.len()
    }

    fn me(&self) -> usize {
        self.me
    }

    fn send(&mut self, to: usize, payload: &[u8]) -> Result<(), NetError> {
        if payload.len() > MAX_FRAME_PAYLOAD {
            return Err(NetError::PayloadTooLarge);
        }
        let link = self
            .links
            .get_mut(to)
            .and_then(Option::as_mut)
            .ok_or(NetError::UnknownPeer { peer: to })?;
        let frame = encode_frame(
            &self.session,
            self.me as u16,
            to as u16,
            self.sent[to],
            payload,
        );
        self.sent[to] += 1;
        link.send_frame(&frame)
            .map_err(|()| NetError::Closed { peer: to })
    }

    fn recv(&mut self, from: usize) -> Result<Vec<u8>, NetError> {
        let link = self
            .links
            .get_mut(from)
            .and_then(Option::as_mut)
            .ok_or(NetError::UnknownPeer { peer: from })?;
        let frame = link
            .recv_frame()
            .map_err(|()| NetError::Closed { peer: from })?;
        let payload = decode_frame(
            &frame,
            &self.session,
            from as u16,
            self.me as u16,
            self.received[from],
        )
        .ok_or(NetError::BadFrame { peer: from })?;
        self.received[from] += 1;
        Ok(payload.to_vec())
    }
}

#[cfg(any(feature = "std", test))]
pub use with_std::*;

#[cfg(any(feature = "std", test))]
mod with_std {
    use super::*;
    use std::io::{Read, Write};
    use std::sync::mpsc::{Receiver, Sender, channel};

    /// A [`Link`] over a pair of thread channels.
    pub struct ChannelLink {
        tx: Sender<Vec<u8>>,
        rx: Receiver<Vec<u8>>,
    }

    impl Link for ChannelLink {
        fn send_frame(&mut self, frame: &[u8]) -> Result<(), ()> {
            self.tx.send(frame.to_vec()).map_err(|_| ())
        }

        fn recv_frame(&mut self) -> Result<Vec<u8>, ()> {
            self.rx.recv().map_err(|_| ())
        }
    }

    /// A [`Link`] over a byte stream such as a socket.
    pub struct StreamLink<S: Read + Write>(pub S);

    impl<S: Read + Write> Link for StreamLink<S> {
        fn send_frame(&mut self, frame: &[u8]) -> Result<(), ()> {
            self.0
                .write_all(frame)
                .and_then(|()| self.0.flush())
                .map_err(|_| ())
        }

        fn recv_frame(&mut self) -> Result<Vec<u8>, ()> {
            let mut frame = alloc::vec![0u8; FRAME_HEADER_BYTES];
            self.0.read_exact(&mut frame).map_err(|_| ())?;
            let len = u32::from_be_bytes([frame[48], frame[49], frame[50], frame[51]]) as usize;
            if len > MAX_FRAME_PAYLOAD {
                return Err(());
            }
            frame.resize(FRAME_HEADER_BYTES + len, 0);
            self.0
                .read_exact(&mut frame[FRAME_HEADER_BYTES..])
                .map_err(|_| ())?;
            Ok(frame)
        }
    }

    /// Transports of `parties` custodians joined pairwise by thread channels, in party order.
    pub fn channel_mesh(session: [u8; 32], parties: usize) -> Vec<Framed<ChannelLink>> {
        let mut links: Vec<Vec<Option<ChannelLink>>> = (0..parties)
            .map(|_| (0..parties).map(|_| None).collect())
            .collect();
        for a in 0..parties {
            for b in a + 1..parties {
                let (tx_ab, rx_ab) = channel();
                let (tx_ba, rx_ba) = channel();
                links[a][b] = Some(ChannelLink {
                    tx: tx_ab,
                    rx: rx_ba,
                });
                links[b][a] = Some(ChannelLink {
                    tx: tx_ba,
                    rx: rx_ab,
                });
            }
        }
        links
            .into_iter()
            .enumerate()
            .map(|(me, l)| Framed::new(session, me, l).expect("a full mesh"))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frames_are_accepted_only_with_the_expected_header() {
        let session = [7u8; 32];
        let frame = encode_frame(&session, 1, 2, 5, b"payload");
        assert_eq!(
            decode_frame(&frame, &session, 1, 2, 5),
            Some(&b"payload"[..])
        );
        assert_eq!(decode_frame(&frame, &[8u8; 32], 1, 2, 5), None);
        assert_eq!(decode_frame(&frame, &session, 0, 2, 5), None);
        assert_eq!(decode_frame(&frame, &session, 1, 0, 5), None);
        assert_eq!(decode_frame(&frame, &session, 1, 2, 4), None);
        assert_eq!(
            decode_frame(&frame[..frame.len() - 1], &session, 1, 2, 5),
            None
        );
        let mut longer = frame.clone();
        longer.push(0);
        assert_eq!(decode_frame(&longer, &session, 1, 2, 5), None);
        let mut magic = frame;
        magic[0] ^= 1;
        assert_eq!(decode_frame(&magic, &session, 1, 2, 5), None);
    }

    #[test]
    fn channel_mesh_delivers_in_order_and_reports_a_closed_peer() {
        let mut mesh = channel_mesh([1u8; 32], 3);
        let mut c = mesh.pop().unwrap();
        let mut b = mesh.pop().unwrap();
        let mut a = mesh.pop().unwrap();
        a.send(1, b"one").unwrap();
        a.send(1, b"two").unwrap();
        c.send(1, b"from c").unwrap();
        assert_eq!(b.recv(0).unwrap(), b"one");
        assert_eq!(b.recv(2).unwrap(), b"from c");
        assert_eq!(b.recv(0).unwrap(), b"two");
        assert_eq!(a.send(0, b"self"), Err(NetError::UnknownPeer { peer: 0 }));
        drop(c);
        assert_eq!(b.recv(2), Err(NetError::Closed { peer: 2 }));
    }

    /// Two custodians over a real socket pair; a frame replayed on the stream is refused.
    #[test]
    fn stream_links_carry_frames_over_sockets() {
        use std::os::unix::net::UnixStream;
        let session = [3u8; 32];
        let (sa, sb) = UnixStream::pair().unwrap();
        let mut a = Framed::new(session, 0, alloc::vec![None, Some(StreamLink(sa))]).unwrap();
        let mut raw = sb.try_clone().unwrap();
        let mut b = Framed::new(session, 1, alloc::vec![Some(StreamLink(sb)), None]).unwrap();
        let big = alloc::vec![0xabu8; 200_000];
        let sender = std::thread::spawn(move || {
            a.send(1, b"hello").unwrap();
            a.send(1, &big).unwrap();
            a.recv(1)
        });
        assert_eq!(b.recv(0).unwrap(), b"hello");
        assert_eq!(b.recv(0).unwrap().len(), 200_000);
        // A frame with a stale sequence number, written straight to the socket.
        use std::io::Write;
        raw.write_all(&encode_frame(&session, 1, 0, 7, b"replay"))
            .unwrap();
        assert_eq!(sender.join().unwrap(), Err(NetError::BadFrame { peer: 1 }));
    }
}
