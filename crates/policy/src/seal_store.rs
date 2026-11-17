//! One-use acceptance records for authenticated capability seals.
//!
//! A verifier must use the same store for every request in its acceptance domain.
//! Creating a fresh store for each request, or using independent stores on replicas,
//! permits replay. Consumption happens after authentication and before authorization
//! is returned; later application failure does not refund a consumed seal.

use alloc::vec::Vec;

use crate::macaroon::CapabilityError;
use crate::MAX_POLICY_CAPACITY;

/// Atomically reserve a previously unseen seal identifier before returning success.
/// Implementations must reject repeats, retain all accepted identifiers, and fail
/// closed on storage errors or exhaustion. Replicated verifiers need a shared,
/// linearizable implementation. Returning success without recording the identifier
/// violates this contract.
pub trait SealConsumptionStore {
    fn consume(&mut self, seal_id: [u8; 32]) -> Result<(), CapabilityError>;
}

/// Bounded process-local consumption. Dropping this store loses replay protection.
/// Use only when the verifier's entire acceptance lifetime is this process; durable
/// services should use persistent storage. There is deliberately no reset or eviction.
pub struct MemorySealConsumptionStore {
    consumed: Vec<[u8; 32]>,
    capacity: usize,
}

impl MemorySealConsumptionStore {
    /// A capacity outside `1..=MAX_POLICY_CAPACITY` fails closed on every consumption.
    pub const fn new(capacity: usize) -> Self {
        Self {
            consumed: Vec::new(),
            capacity,
        }
    }

    fn insertion_index(&self, seal_id: &[u8; 32]) -> Result<usize, CapabilityError> {
        let index = match self.consumed.binary_search(seal_id) {
            Ok(_) => return Err(CapabilityError::Replay),
            Err(index) => index,
        };
        if self.capacity > MAX_POLICY_CAPACITY || self.consumed.len() >= self.capacity {
            return Err(CapabilityError::ConsumptionFailed);
        }
        Ok(index)
    }
}

impl SealConsumptionStore for MemorySealConsumptionStore {
    fn consume(&mut self, seal_id: [u8; 32]) -> Result<(), CapabilityError> {
        let index = self.insertion_index(&seal_id)?;
        self.consumed
            .try_reserve(1)
            .map_err(|_| CapabilityError::ConsumptionFailed)?;
        self.consumed.insert(index, seal_id);
        Ok(())
    }
}

/// Crash-durable, exclusively locked consumption records in trusted local storage.
///
/// All processes in an acceptance domain must open the same provisioned path. A
/// competing open fails while this handle holds the lock; callers may retry after
/// the holder exits. `open_existing` never creates a missing ledger. The record and
/// its permanent `.lock` sidecar must not be deleted or restored from old backups.
///
/// This provides crash recovery and process exclusion, **not** authenticated storage
/// or rollback resistance against an administrator who can rewrite the directory.
/// Such deployments need a trusted external consumption service or monotonic storage.
/// Filesystem flush and lock guarantees are those of
/// [`dregg_sig_asm::durable::LockedRecord`]. No accepted entry is evicted on exhaustion.
#[cfg(feature = "std")]
pub struct FsSealConsumptionStore {
    record: dregg_sig_asm::durable::LockedRecord,
    memory: MemorySealConsumptionStore,
    failed: bool,
}

#[cfg(feature = "std")]
impl FsSealConsumptionStore {
    const MAGIC: &[u8; 8] = b"QSBURN01";
    const HEADER_BYTES: usize = 16;

    fn check_capacity(capacity: usize) -> std::io::Result<()> {
        if capacity == 0 || capacity > MAX_POLICY_CAPACITY {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "seal consumption capacity outside supported range",
            ));
        }
        Ok(())
    }

    /// Provision an empty acceptance domain. Never use this to recover a lost ledger.
    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
    ) -> std::io::Result<Self> {
        Self::check_capacity(capacity)?;
        let store = Self {
            record: dregg_sig_asm::durable::LockedRecord::create_new(path)?,
            memory: MemorySealConsumptionStore::new(capacity),
            failed: false,
        };
        store.record.replace(&store.encode())?;
        Ok(store)
    }

    /// Recover a provisioned domain, requiring its original capacity and format.
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
    ) -> std::io::Result<Self> {
        Self::check_capacity(capacity)?;
        let record = dregg_sig_asm::durable::LockedRecord::open_existing(path)?;
        let bytes = record.read_bounded(Self::HEADER_BYTES + 32 * capacity)?;
        let invalid = || {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "invalid or unsupported seal consumption record (expected QSBURN01 and configured capacity)",
            )
        };
        if bytes.len() < Self::HEADER_BYTES || &bytes[..8] != Self::MAGIC {
            return Err(invalid());
        }
        let stored_capacity = u32::from_be_bytes(bytes[8..12].try_into().map_err(|_| invalid())?);
        let count = u32::from_be_bytes(bytes[12..16].try_into().map_err(|_| invalid())?) as usize;
        if stored_capacity as usize != capacity
            || count > capacity
            || bytes.len() != Self::HEADER_BYTES + count * 32
        {
            return Err(invalid());
        }
        let mut memory = MemorySealConsumptionStore::new(capacity);
        memory
            .consumed
            .try_reserve_exact(count)
            .map_err(std::io::Error::other)?;
        let (ids, rest) = bytes[Self::HEADER_BYTES..].as_chunks::<32>();
        if !rest.is_empty() {
            return Err(invalid());
        }
        for &id in ids {
            if memory.consumed.last().is_some_and(|prev| prev >= &id) {
                return Err(invalid());
            }
            memory.consumed.push(id);
        }
        Ok(Self {
            record,
            memory,
            failed: false,
        })
    }

    fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(Self::HEADER_BYTES + self.memory.consumed.len() * 32);
        bytes.extend_from_slice(Self::MAGIC);
        bytes.extend_from_slice(&(self.memory.capacity as u32).to_be_bytes());
        bytes.extend_from_slice(&(self.memory.consumed.len() as u32).to_be_bytes());
        for id in &self.memory.consumed {
            bytes.extend_from_slice(id);
        }
        bytes
    }
}

#[cfg(feature = "std")]
impl SealConsumptionStore for FsSealConsumptionStore {
    fn consume(&mut self, seal_id: [u8; 32]) -> Result<(), CapabilityError> {
        if self.failed {
            return Err(CapabilityError::ConsumptionFailed);
        }
        self.memory.consume(seal_id)?;
        // An uncertain write may already be durable. Never permit another operation
        // through this handle until a fresh open has recovered the committed record.
        self.failed = true;
        self.record
            .replace(&self.encode())
            .map_err(|_| CapabilityError::ConsumptionFailed)?;
        self.failed = false;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn memory_rejects_replay_without_eviction() {
        let mut store = MemorySealConsumptionStore::new(2);
        assert_eq!(store.consume([2; 32]), Ok(()));
        assert_eq!(store.consume([1; 32]), Ok(()));
        assert_eq!(store.consume([2; 32]), Err(CapabilityError::Replay));
        assert_eq!(
            store.consume([3; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        assert_eq!(store.consume([1; 32]), Err(CapabilityError::Replay));
        assert_eq!(
            MemorySealConsumptionStore::new(0).consume([1; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        assert_eq!(
            MemorySealConsumptionStore::new(usize::MAX).consume([1; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
    }

    #[cfg(all(feature = "std", unix))]
    #[test]
    fn disk_rejects_replay_after_restart_and_competing_process() {
        const CHILD: &str = "QSAG_SEAL_STORE_CHILD_PATH";
        if let Some(path) = std::env::var_os(CHILD) {
            assert!(FsSealConsumptionStore::open_existing(path, 2).is_err());
            return;
        }
        let dir = temporary_directory("restart");
        let path = dir.join("consumed");
        let mut store = FsSealConsumptionStore::create_new(&path, 2).unwrap();
        store.consume([2; 32]).unwrap();
        let child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "seal_store::tests::disk_rejects_replay_after_restart_and_competing_process",
                "--nocapture",
            ])
            .env(CHILD, &path)
            .status()
            .unwrap();
        assert!(child.success());
        drop(store);
        let mut store = FsSealConsumptionStore::open_existing(&path, 2).unwrap();
        assert_eq!(store.consume([2; 32]), Err(CapabilityError::Replay));
        store.consume([1; 32]).unwrap();
        drop(store);
        let mut store = FsSealConsumptionStore::open_existing(&path, 2).unwrap();
        assert_eq!(
            store.consume([3; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        assert_eq!(store.consume([1; 32]), Err(CapabilityError::Replay));
        drop(store);
        assert!(FsSealConsumptionStore::open_existing(&path, 3).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(all(feature = "std", unix))]
    #[test]
    fn disk_write_failure_poison_and_invalid_format_fail_closed() {
        let dir = temporary_directory("failure");
        let path = dir.join("consumed");
        let mut store = FsSealConsumptionStore::create_new(&path, 2).unwrap();
        // A directory where atomic replacement needs its temporary file forces I/O failure.
        std::fs::create_dir(dir.join("consumed.tmp")).unwrap();
        assert_eq!(
            store.consume([1; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        std::fs::remove_dir(dir.join("consumed.tmp")).unwrap();
        assert_eq!(
            store.consume([2; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        drop(store);
        let mut store = FsSealConsumptionStore::open_existing(&path, 2).unwrap();
        store.consume([2; 32]).unwrap();
        let mut bad = store.encode();
        bad[..8].copy_from_slice(b"QSBURN00");
        store.record.replace(&bad).unwrap();
        drop(store);
        assert!(FsSealConsumptionStore::open_existing(&path, 2).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(all(feature = "std", unix))]
    fn temporary_directory(label: &str) -> std::path::PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(alloc::format!(
            "qsag-seal-store-{label}-{}-{nanos}",
            std::process::id()
        ));
        std::fs::create_dir(&path).unwrap();
        path
    }
}
