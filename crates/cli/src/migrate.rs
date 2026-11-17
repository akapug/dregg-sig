//! `dregg-sig migrate`: prove that the holder of a legacy credential authorises a
//! post-quantum address, verify such a proof, and record each migration once.
//!
//! The statements and proofs are those of [`dregg_sig_migrate::hem::relations`] (ownership
//! relations over the zk-Hem argument); the registry is
//! [`dregg_sig_migrate::hem::registry`]. Read `crates/migrate/SECURITY.md` for what a
//! statement proves and for the status of the proof system.
//!
//! # Files
//!
//! A claim file (`qsag-migration-claim-v2`) and a proof file (`qsag-migration-proof-v2`)
//! are JSON. Their `statement` member is the canonical statement encoding and is the only
//! authority; every other member (kind, legacy value, nullifier, epoch, domain, target
//! address) is a rendering of it and is rejected unless it equals what the statement
//! renders to. The proof itself is the `proof` member in base64 (RFC 4648, padded,
//! canonical). One file rather than a JSON header beside a binary sidecar, because a proof
//! is meaningless without its statement and a pair of files can be separated or mixed up;
//! base64 rather than hex, because the proof is about half a megabyte and hex doubles it
//! where base64 adds a third.
//!
//! # Statement kinds
//!
//! [`KINDS`] is the table of kinds the command line offers and [`kind_of`] maps a claim to
//! its entry with an exhaustive match, so a claim variant added to the library does not
//! compile here until it has an entry.

use dregg_sig_accel::keccak::cshake256_framed_32;
use dregg_sig_addr::QsagAddress;
use dregg_sig_agg::pcs::WhirSecurityRegime;
use dregg_sig_agg::zk_hem::protocol::{COL_DEGREE, Layout, ROW_DEGREE};
use dregg_sig_migrate::hem::registry::{
    BindingStatus, NullifierRegistry, Receipt, RegisteredBinding, RegistryError, pq_commitment,
};
use dregg_sig_migrate::hem::relations::{
    BIP32_HARDENED, BIP32_SEED_BYTES, ClaimKind, LegacyClaim, MAX_BIP32_DEPTH, OwnershipError,
    OwnershipProof, OwnershipStatement, OwnershipWitness, ownership_shape, prove_ownership,
    verify_ownership,
};

use crate::anchor::{AnchorConfig, AnchorRequirementError, FsExternalMountAnchor};
use crate::cli::{
    Args, CliError, MAX_KEY_FILE_BYTES, MAX_SIG_PROOF_BYTES, Secret32, ZeroizingBuf, os_random_32,
    private_dir, read_bounded_file, read_text, write_new,
};
use crate::codec::{Json, from_hex, from_hex_exact, to_hex};
use crate::vault::{Vault, set};

const MIGRATE_HELP: &str = "\
dregg-sig migrate <subcommand> [options]

Prove that the holder of a legacy credential authorises a post-quantum address, and record
each migration once. Proofs are zk-Hem ownership proofs; see crates/migrate/SECURITY.md.

  claim     derive the statement (legacy value, nullifier, target) from a legacy secret file
            (alias: commit)
  prove     prove a statement
  verify    verify a proof against the epoch, domain and target the verifier expects;
            --register records it in a registry in the same step
  registry  init | register | enroll | finalize | lookup: the durable one-way registry

statement kinds (--kind):
";

const CLAIM_FORMAT: &str = "qsag-migration-claim-v2";
const PROOF_FORMAT: &str = "qsag-migration-proof-v2";
const REGISTRY_FORMAT: &str = "qsag-migration-registry-v1";
const REGISTRY_SCHEME: &str = "migration-registry";
const DEFAULT_DOMAIN_LABEL: &[u8] = b"QSAG.CLI.MIGRATE.DEFAULT_DOMAIN.V1";
/// The regime every proof this command writes or accepts is made under.
const REGIME: WhirSecurityRegime = WhirSecurityRegime::BciksJohnsonQrom128;
const REGIME_NAME: &str = "BciksJohnsonQrom128";

// ============================================================================
// Statement kinds
// ============================================================================

/// What the secret file of a kind holds.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SecretForm {
    /// Exactly 32 bytes: raw, hex, or the `seed` of an unsealed JSON key file.
    Key32,
    /// A BIP-32 master seed of 16 to 64 bytes, as hex or as the `seed` of a JSON file.
    /// Raw bytes are not accepted: a 64-byte file would be ambiguous with 32 bytes of hex.
    HexSeed,
}

/// One statement kind of the command line. To offer a new [`LegacyClaim`] variant, add one
/// of these to [`KINDS`] and name it in [`kind_of`].
struct KindSpec {
    name: &'static str,
    aliases: &'static [&'static str],
    summary: &'static str,
    secret: SecretForm,
    /// Whether the kind takes `--path`.
    derivation_path: bool,
    claim: fn(Vec<u32>) -> ClaimKind,
    /// The witness for secret bytes of the length `secret` admits.
    witness: fn(&[u8]) -> Option<OwnershipWitness>,
    /// The public members a claim of this kind renders to.
    render: fn(&LegacyClaim) -> Vec<(&'static str, Json)>,
}

fn secp256k1_key(bytes: &[u8]) -> Option<OwnershipWitness> {
    Some(OwnershipWitness::Secp256k1Key(bytes.try_into().ok()?))
}

static BTC_HASH160: KindSpec = KindSpec {
    name: "btc-hash160",
    aliases: &["btc-p2wpkh", "btc-p2pkh"],
    summary: "Bitcoin P2WPKH / P2PKH: HASH160 of the compressed public key (hidden key)",
    secret: SecretForm::Key32,
    derivation_path: false,
    claim: |_| ClaimKind::BitcoinHash160,
    witness: secp256k1_key,
    render: |claim| match claim {
        LegacyClaim::BitcoinHash160(hash) => vec![("legacy_hash160", Json::hex(hash))],
        _ => Vec::new(),
    },
};

static ETH_EOA: KindSpec = KindSpec {
    name: "eth-eoa",
    aliases: &["ethereum"],
    summary: "Ethereum externally owned account address (hidden key)",
    secret: SecretForm::Key32,
    derivation_path: false,
    claim: |_| ClaimKind::EthereumAddress,
    witness: secp256k1_key,
    render: |claim| match claim {
        LegacyClaim::EthereumAddress(address) => vec![("legacy_address", Json::hex(address))],
        _ => Vec::new(),
    },
};

static ED25519_SEED: KindSpec = KindSpec {
    name: "ed25519",
    aliases: &["ed25519-seed"],
    summary: "Ed25519 public key, by knowledge of its RFC 8032 seed (revealed key)",
    secret: SecretForm::Key32,
    derivation_path: false,
    claim: |_| ClaimKind::Ed25519Seed,
    witness: |bytes| Some(OwnershipWitness::Ed25519Seed(bytes.try_into().ok()?)),
    render: |claim| match claim {
        LegacyClaim::Ed25519Seed { public_key } => {
            vec![("legacy_public_key", Json::hex(public_key))]
        }
        _ => Vec::new(),
    },
};

static BIP32_SECP256K1: KindSpec = KindSpec {
    name: "bip32-secp256k1",
    aliases: &["bip32"],
    summary: "secp256k1 public key at --path of a BIP-32 master seed (revealed key)",
    secret: SecretForm::HexSeed,
    derivation_path: true,
    claim: |path| ClaimKind::Bip32Secp256k1 { path },
    witness: |bytes| Some(OwnershipWitness::Bip32Seed(bytes.to_vec())),
    render: |claim| match claim {
        LegacyClaim::Bip32Secp256k1 {
            public_key,
            seed_len,
            path,
        } => vec![
            ("legacy_public_key", Json::hex(public_key)),
            ("derivation_path", Json::str(format_path(path))),
            ("seed_bytes", Json::num(seed_len)),
        ],
        _ => Vec::new(),
    },
};

const KINDS: &[&KindSpec] = &[&BTC_HASH160, &ETH_EOA, &ED25519_SEED, &BIP32_SECP256K1];

/// The table entry of a claim. Exhaustive on purpose.
fn kind_of(claim: &LegacyClaim) -> &'static KindSpec {
    match claim {
        LegacyClaim::BitcoinHash160(_) => &BTC_HASH160,
        LegacyClaim::EthereumAddress(_) => &ETH_EOA,
        LegacyClaim::Ed25519Seed { .. } => &ED25519_SEED,
        LegacyClaim::Bip32Secp256k1 { .. } => &BIP32_SECP256K1,
    }
}

fn kind_by_name(name: &str) -> Result<&'static KindSpec, CliError> {
    KINDS
        .iter()
        .copied()
        .find(|kind| kind.name == name || kind.aliases.contains(&name))
        .ok_or_else(|| {
            let names: Vec<_> = KINDS.iter().map(|kind| kind.name).collect();
            CliError::usage(format!(
                "unsupported --kind '{name}' (expected one of: {})",
                names.join(", ")
            ))
        })
}

fn kinds_help() -> String {
    let mut out = String::new();
    for kind in KINDS {
        out.push_str(&format!("  {:<16} {}\n", kind.name, kind.summary));
        if !kind.aliases.is_empty() {
            out.push_str(&format!(
                "  {:<16} aliases: {}\n",
                "",
                kind.aliases.join(", ")
            ));
        }
    }
    out
}

/// The `migration` entry of `dregg-sig info --json`.
pub fn info() -> Json {
    Json::object(vec![
        (
            "proof_system",
            Json::str(
                "zk-Hem ownership relations over the Hem WHIR commitment; composed zero-knowledge and knowledge-soundness bounds are not established (crates/migrate/SECURITY.md)",
            ),
        ),
        ("regime", Json::str(REGIME_NAME)),
        ("claim_format", Json::str(CLAIM_FORMAT)),
        ("proof_format", Json::str(PROOF_FORMAT)),
        ("registry_format", Json::str(REGISTRY_FORMAT)),
        (
            "statement_kinds",
            Json::Array(
                KINDS
                    .iter()
                    .map(|kind| {
                        Json::object(vec![
                            ("kind", Json::str(kind.name)),
                            (
                                "aliases",
                                Json::Array(kind.aliases.iter().map(|a| Json::str(*a)).collect()),
                            ),
                            ("statement", Json::str(kind.summary)),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

/// The migration line of `dregg-sig info`.
pub fn info_text() -> String {
    let names: Vec<_> = KINDS.iter().map(|kind| kind.name).collect();
    format!(
        "migration: zk-Hem ownership proofs ({REGIME_NAME}) for {}; one-way registry\n",
        names.join(", ")
    )
}

fn kind_names() -> String {
    let names: Vec<_> = KINDS.iter().map(|kind| kind.name).collect();
    names.join("|")
}

/// `m/44'/0'/0'/0/0`: `'`, `h` or `H` marks a hardened index.
fn parse_path(text: &str) -> Result<Vec<u32>, CliError> {
    let bad = || {
        CliError::usage(format!(
            "--path '{text}' is not a BIP-32 path such as m/44'/0'/0'/0/0"
        ))
    };
    let mut parts = text.split('/');
    if parts.next() != Some("m") {
        return Err(bad());
    }
    let mut path = Vec::new();
    for part in parts {
        let (digits, hardened) = match part.strip_suffix(['\'', 'h', 'H']) {
            Some(digits) => (digits, BIP32_HARDENED),
            None => (part, 0),
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(bad());
        }
        let index: u32 = digits.parse().map_err(|_| bad())?;
        if index >= BIP32_HARDENED {
            return Err(bad());
        }
        path.push(index | hardened);
    }
    if path.len() > MAX_BIP32_DEPTH {
        return Err(CliError::usage(format!(
            "--path has {} levels; at most {MAX_BIP32_DEPTH} are supported",
            path.len()
        )));
    }
    Ok(path)
}

fn format_path(path: &[u32]) -> String {
    let mut out = String::from("m");
    for &index in path {
        out.push('/');
        out.push_str(&(index & !BIP32_HARDENED).to_string());
        if index & BIP32_HARDENED != 0 {
            out.push('\'');
        }
    }
    out
}

// ============================================================================
// Legacy secrets
// ============================================================================

fn reject_sealed_legacy_key(json: &Json) -> Result<(), CliError> {
    if [
        "envelope",
        "salt",
        "envelope_tag",
        "envelope_salt",
        "envelope_nonce",
    ]
    .iter()
    .any(|key| json.get(key).is_some())
    {
        return Err(CliError::input(
            "sealed legacy keys are not supported by migrate; decrypt the key through an authenticated envelope reader before migration",
        ));
    }
    Ok(())
}

fn json_legacy_seed(json: &Json) -> Result<ZeroizingBuf, CliError> {
    reject_sealed_legacy_key(json)?;
    json.field_hex("seed")
}

/// Read the secret of a statement kind. The bytes stay in a wiping buffer.
///
/// `Key32`: 64 hex characters, a JSON object with a `seed` member, or a raw 32-byte file.
/// `HexSeed`: hex or such a JSON object, 16 to 64 bytes. A JSON object or a hex string is
/// never read as raw key bytes, whatever its length.
fn read_legacy_secret(path: &str, form: SecretForm) -> Result<ZeroizingBuf, CliError> {
    let raw = read_bounded_file(path, MAX_KEY_FILE_BYTES)?;
    let text = std::str::from_utf8(&raw.0).ok().map(str::trim);
    let hex = text
        .map(|text| text.strip_prefix("0x").unwrap_or(text))
        .filter(|hex| !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit()));
    // Hex text is hex whatever its length: 32 hex characters are a 16-byte value, never a
    // raw 32-byte key (32 uniform bytes are all hex digits with probability below 2^-110).
    let secret = match (text, hex) {
        (Some(text), _) if text.starts_with('{') => json_legacy_seed(&Json::parse(text)?)?,
        (_, Some(hex)) => from_hex(hex)?,
        _ if form == SecretForm::Key32 && raw.0.len() == 32 => raw,
        _ => {
            return Err(CliError::input(format!(
                "{path} must be hex or a JSON secret file{}",
                if form == SecretForm::Key32 {
                    ", or 32 raw bytes"
                } else {
                    ""
                }
            )));
        }
    };
    let accepted = match form {
        SecretForm::Key32 => secret.0.len() == 32,
        SecretForm::HexSeed => BIP32_SEED_BYTES.contains(&secret.0.len()),
    };
    if !accepted {
        return Err(CliError::input(match form {
            SecretForm::Key32 => format!("legacy secret must be 32 bytes (got {})", secret.0.len()),
            SecretForm::HexSeed => format!(
                "BIP-32 seed must be {} to {} bytes (got {})",
                BIP32_SEED_BYTES.start(),
                BIP32_SEED_BYTES.end(),
                secret.0.len()
            ),
        }));
    }
    Ok(secret)
}

// ============================================================================
// Statements
// ============================================================================

fn default_migration_domain() -> [u8; 32] {
    cshake256_framed_32(DEFAULT_DOMAIN_LABEL, &[b"qsag-mainnet-migration-v1"])
}

fn parse_domain(args: &Args) -> Result<[u8; 32], CliError> {
    match args.get("domain-hex") {
        Some(hex) => from_hex_exact::<32>(hex, "--domain-hex"),
        None => Ok(default_migration_domain()),
    }
}

fn required_epoch(args: &Args) -> Result<u64, CliError> {
    args.get_u64("epoch")?
        .ok_or_else(|| CliError::usage("missing required option --epoch"))
}

/// A target address and its canonical text.
fn parse_target(text: &str) -> Result<(QsagAddress, String), CliError> {
    let address = QsagAddress::decode(text)
        .map_err(|e| CliError::usage(format!("invalid --target address: {e:?}")))?;
    let canonical = address
        .encode()
        .map_err(|e| CliError::usage(format!("invalid --target address: {e:?}")))?;
    Ok((address, canonical))
}

/// The members a statement renders to, in file order. `target` is the canonical text of
/// the address `statement.pq_commitment` commits to.
fn statement_members(statement: &OwnershipStatement, target: &str) -> Vec<(&'static str, Json)> {
    let kind = kind_of(&statement.claim);
    let binding = statement.binding();
    let mut members = vec![("kind", Json::str(kind.name))];
    members.extend((kind.render)(&statement.claim));
    members.extend([
        (
            "key_exposure",
            Json::str(if statement.claim.key_is_revealed() {
                "revealed"
            } else {
                "hidden"
            }),
        ),
        ("target_pq_address", Json::str(target)),
        ("pq_commitment", Json::hex(&statement.pq_commitment)),
        ("epoch", Json::num(statement.epoch)),
        ("migration_domain", Json::hex(&statement.migration_domain)),
        ("nullifier", Json::hex(&statement.nullifier)),
        ("legacy_id", Json::hex(&binding.legacy_id)),
        ("statement", Json::hex(&statement.to_bytes())),
    ]);
    members
}

fn document(format: &str, mut members: Vec<(&'static str, Json)>) -> Json {
    members.insert(0, ("format", Json::str(format)));
    Json::object(members)
}

/// A statement read back from a claim or proof document.
struct LoadedStatement {
    statement: OwnershipStatement,
    target: QsagAddress,
    target_text: String,
}

/// Decode the statement of a claim or proof document and check that the document says
/// nothing else: the target address must be the one the statement commits to, every
/// rendered member must equal its rendering, and no other member may be present beyond
/// `extra`.
fn load_statement(json: &Json, format: &str, extra: &[&str]) -> Result<LoadedStatement, String> {
    let Json::Object(members) = json else {
        return Err("not a JSON object".into());
    };
    let field = |name: &str| {
        json.get(name)
            .and_then(Json::as_str)
            .ok_or_else(|| format!("missing or non-string member \"{name}\""))
    };
    if field("format")? != format {
        return Err(format!("not a {format} file"));
    }
    let bytes = from_hex(field("statement")?).map_err(|e| e.message)?;
    let statement = OwnershipStatement::from_bytes(&bytes.0)
        .ok_or("statement is not a canonical ownership statement")?;
    let target_text = field("target_pq_address")?.to_owned();
    let target = QsagAddress::decode(&target_text)
        .map_err(|e| format!("invalid target_pq_address: {e:?}"))?;
    if target.encode().ok().as_deref() != Some(target_text.as_str()) {
        return Err("target_pq_address is not in canonical form".into());
    }
    if pq_commitment(&target) != statement.pq_commitment {
        return Err("target_pq_address is not the address the statement commits to".into());
    }
    let rendered = statement_members(&statement, &target_text);
    for (name, value) in &rendered {
        if json.get(name) != Some(value) {
            return Err(format!("member \"{name}\" does not match the statement"));
        }
    }
    for (name, _) in members {
        let known = name == "format"
            || extra.contains(&name.as_str())
            || rendered.iter().any(|(rendered, _)| rendered == name);
        if !known {
            return Err(format!("unexpected member \"{name}\""));
        }
    }
    if members.len() != 1 + rendered.len() + extra.len() {
        return Err("missing or repeated member".into());
    }
    Ok(LoadedStatement {
        statement,
        target,
        target_text,
    })
}

const STATEMENT_OPTIONS: &[&str] = &[
    "kind",
    "legacy-secret",
    "path",
    "target",
    "epoch",
    "domain-hex",
    "out",
];

/// The statement and witness the options describe.
fn derive(args: &Args) -> Result<(LoadedStatement, OwnershipWitness, ZeroizingBuf), CliError> {
    let kind = kind_by_name(args.require("kind")?)?;
    let path = match (kind.derivation_path, args.get("path")) {
        (true, Some(path)) => parse_path(path)?,
        (true, None) => {
            return Err(CliError::usage(format!(
                "--kind {} requires --path (for example m/44'/0'/0'/0/0)",
                kind.name
            )));
        }
        (false, Some(_)) => {
            return Err(CliError::usage(format!(
                "--path does not apply to --kind {}",
                kind.name
            )));
        }
        (false, None) => Vec::new(),
    };
    let (target, target_text) = parse_target(args.require("target")?)?;
    let epoch = required_epoch(args)?;
    let domain = parse_domain(args)?;
    let secret = read_legacy_secret(args.require("legacy-secret")?, kind.secret)?;
    let witness = (kind.witness)(&secret.0)
        .ok_or_else(|| CliError::input("legacy secret has the wrong length for this kind"))?;
    let statement = OwnershipStatement::derive(
        &(kind.claim)(path),
        &witness,
        pq_commitment(&target),
        domain,
        epoch,
    )
    .ok_or_else(|| {
        CliError::input(format!(
            "legacy secret is not a valid {} secret (a secp256k1 key must be in 1..n; a BIP-32 path must derive)",
            kind.name
        ))
    })?;
    Ok((
        LoadedStatement {
            statement,
            target,
            target_text,
        },
        witness,
        secret,
    ))
}

fn summary(loaded: &LoadedStatement) -> String {
    format!(
        "{} -> {} at epoch {} (nullifier {})",
        kind_of(&loaded.statement.claim).name,
        loaded.target_text,
        loaded.statement.epoch,
        to_hex(&loaded.statement.nullifier)
    )
}

fn claim(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, STATEMENT_OPTIONS, &["json", "help"])?;
    if args.flag("help") {
        println!(
            "dregg-sig migrate claim --kind <{}> --legacy-secret <path> [--path <m/..>] --target <address> --epoch <n> [--domain-hex <64-hex>] [--out <path>] [--json]\n\n\
Derive the statement a proof will be about: the legacy value, the nullifier of the legacy key\n\
in the migration domain, and the commitment to the target address. Nothing secret is written.\n\n{}",
            kind_names(),
            kinds_help()
        );
        return Ok(());
    }
    args.no_positionals()?;
    let (loaded, _witness, _secret) = derive(&args)?;
    let doc = document(
        CLAIM_FORMAT,
        statement_members(&loaded.statement, &loaded.target_text),
    );
    if let Some(out) = args.get("out") {
        write_new(out, doc.to_pretty().as_bytes(), false)?;
    }
    if args.flag("json") {
        print!("{}", doc.to_pretty());
    } else {
        println!("claim {}", summary(&loaded));
    }
    Ok(())
}

// ============================================================================
// Proof files
// ============================================================================

const BASE64: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn base64_len(bytes: usize) -> usize {
    bytes.div_ceil(3) * 4
}

fn to_base64(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(base64_len(bytes.len()));
    for chunk in bytes.chunks(3) {
        let word = chunk
            .iter()
            .enumerate()
            .fold(0u32, |word, (i, &b)| word | u32::from(b) << (16 - 8 * i));
        for i in 0..4 {
            out.push(if i <= chunk.len() {
                BASE64[(word >> (18 - 6 * i)) as usize & 63] as char
            } else {
                '='
            });
        }
    }
    out
}

/// Strict RFC 4648 base64: the standard alphabet, mandatory padding, no whitespace, and
/// zero bits in the unused tail of the last group, so each byte string has one encoding.
fn from_base64(text: &str) -> Option<Vec<u8>> {
    let text = text.as_bytes();
    if !text.len().is_multiple_of(4) {
        return None;
    }
    let sextet = |c: u8| BASE64.iter().position(|&a| a == c).map(|v| v as u32);
    let groups = text.len() / 4;
    let mut out = Vec::with_capacity(groups * 3);
    for (index, group) in text.as_chunks::<4>().0.iter().enumerate() {
        let padding = group.iter().rev().take_while(|&&c| c == b'=').count();
        if padding > 2 || (padding != 0 && index + 1 != groups) {
            return None;
        }
        let mut word = 0u32;
        for &c in &group[..4 - padding] {
            word = word << 6 | sextet(c)?;
        }
        word <<= 6 * padding;
        if word & ((1 << (8 * padding)) - 1) != 0 {
            return None;
        }
        out.extend_from_slice(&word.to_be_bytes()[1..4 - padding]);
    }
    Some(out)
}

/// An upper bound on the encoding of an ownership proof for `statement`, from the cell
/// layout and the query schedule of its relation: every transcript element the argument
/// sends, every opened symbol, and one authentication path per query with no sharing.
/// `None` for a malformed statement.
fn max_proof_bytes(statement: &OwnershipStatement) -> Option<usize> {
    const EXT: usize = 32;
    const BASE: usize = 8;
    const DIGEST: usize = 32;
    // The masked assignment table and its four companions share the Stage-0 commitment.
    const STAGE0_TABLES: usize = 5;
    let shape = ownership_shape(statement)?;
    let layout = Layout::new(&shape, REGIME)?;
    let schedule = &layout.schedule;
    // Magic, claim kind, regime, commitment; the two masked sumchecks with their mask
    // sums, the three row values and the four companion claims.
    let mut bytes = 8 + 2 + (DIGEST + 1);
    bytes += EXT
        * (1 + shape.log_rows * (ROW_DEGREE + 1) + 3 + 1 + layout.var_bits * (COL_DEGREE + 1) + 4);
    // Opening: out-of-domain values, one bridge polynomial and proof-of-work nonce per
    // folded variable, the terminal coefficients, and the length prefixes.
    bytes += 2 * EXT + 8 + layout.log_cells * (5 * EXT + 8) + 8;
    bytes += 4 + ((1usize << schedule.early_stop_vars) + 2) * EXT + 4;
    for (index, stage) in schedule.stages.iter().enumerate() {
        let arity = 1usize << stage.step_vars;
        let depth = layout.log_cells + stage.blowup.next_power_of_two().trailing_zeros() as usize;
        let leaf = if index == 0 {
            16 + arity * STAGE0_TABLES * BASE
        } else {
            arity * EXT
        };
        bytes += (DIGEST + 1) + 2 * EXT + 8 + 3 * 4 + stage.num_queries * (leaf + depth * DIGEST);
    }
    Some(bytes)
}

fn map_ownership_error(err: OwnershipError) -> CliError {
    match err {
        OwnershipError::MalformedStatement | OwnershipError::WitnessMismatch => {
            CliError::input(format!("migration witness error: {err:?}"))
        }
        OwnershipError::Proof(e) => CliError::input(format!("migration proving failed: {e:?}")),
    }
}

fn prove(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, STATEMENT_OPTIONS, &["deterministic", "json", "help"])?;
    if args.flag("help") {
        println!(
            "dregg-sig migrate prove --kind <{}> --legacy-secret <path> [--path <m/..>] --target <address> --epoch <n> [--domain-hex <64-hex>] --out <path> [--deterministic] [--json]\n\n\
Prove ownership of a legacy credential and bind it to --target, --epoch and the migration\n\
domain. --deterministic derives the proof randomness from the secret and the statement.\n\n{}",
            kind_names(),
            kinds_help()
        );
        return Ok(());
    }
    args.no_positionals()?;
    let out_path = args.require("out")?;
    let (loaded, witness, secret) = derive(&args)?;
    let statement = &loaded.statement;
    let seed = Secret32::new(if args.flag("deterministic") {
        cshake256_framed_32(
            b"QSAG.CLI.MIGRATE.PROOF.SEED.V2",
            &[&secret.0, &statement.to_bytes(), &[REGIME as u8]],
        )
    } else {
        os_random_32()?
    });
    let proof =
        prove_ownership(statement, &witness, REGIME, &seed.0).map_err(map_ownership_error)?;
    let bytes = proof.to_bytes();
    // Never write a proof that `verify` would refuse.
    let cap = max_proof_bytes(statement).unwrap_or(0);
    let reread = OwnershipProof::from_bytes(&bytes, statement);
    if bytes.len() > cap || !reread.is_some_and(|proof| verify_ownership(statement, REGIME, &proof))
    {
        return Err(CliError::verify(
            "the generated migration proof does not verify; nothing was written",
        ));
    }
    let mut members = statement_members(statement, &loaded.target_text);
    members.extend([
        ("regime", Json::str(REGIME_NAME)),
        ("proof_bytes", Json::num(bytes.len())),
        ("proof", Json::str(to_base64(&bytes))),
    ]);
    write_new(
        out_path,
        document(PROOF_FORMAT, members).to_pretty().as_bytes(),
        false,
    )?;
    if args.flag("json") {
        let mut report = vec![("operation", Json::str("migrate-prove"))];
        report.extend(statement_members(statement, &loaded.target_text));
        report.extend([
            ("regime", Json::str(REGIME_NAME)),
            ("proof_bytes", Json::num(bytes.len())),
            ("proof_file", Json::str(out_path)),
        ]);
        print!("{}", Json::object(report).to_pretty());
    } else {
        println!(
            "proved {} ({} proof bytes) -> {out_path}",
            summary(&loaded),
            bytes.len()
        );
    }
    Ok(())
}

/// What the verifier requires of a proof, from its own options.
struct Expectation {
    epoch: u64,
    domain: [u8; 32],
    target: Option<QsagAddress>,
}

impl Expectation {
    fn from_args(args: &Args) -> Result<Self, CliError> {
        Ok(Self {
            epoch: required_epoch(args)?,
            domain: parse_domain(args)?,
            target: args
                .get("target")
                .map(|text| parse_target(text).map(|(address, _)| address))
                .transpose()?,
        })
    }
}

/// Parse a claim or proof file. A file that cannot be opened is an I/O error; anything
/// wrong with its content is returned as text for the caller to classify.
fn read_document(path: &str) -> Result<Result<Json, String>, CliError> {
    let raw = read_bounded_file(path, MAX_SIG_PROOF_BYTES)?;
    Ok(std::str::from_utf8(&raw.0)
        .map_err(|_| format!("{path} is not UTF-8"))
        .and_then(|text| Json::parse(text).map_err(|e| format!("{path}: {e}"))))
}

/// Read a proof file and verify it. Every failure is exit code 2.
fn load_verified(path: &str, expected: &Expectation) -> Result<LoadedStatement, CliError> {
    let json = read_document(path)?.map_err(CliError::verify)?;
    let loaded = load_statement(&json, PROOF_FORMAT, &["regime", "proof_bytes", "proof"])
        .map_err(|e| CliError::verify(format!("{path}: {e}")))?;
    let statement = &loaded.statement;
    if json.get("regime").and_then(Json::as_str) != Some(REGIME_NAME) {
        return Err(CliError::verify(format!(
            "{path}: proof is not under the {REGIME_NAME} regime"
        )));
    }
    if statement.migration_domain != expected.domain {
        return Err(CliError::verify(
            "proof is for another migration domain (--domain-hex)",
        ));
    }
    if statement.epoch != expected.epoch {
        return Err(CliError::verify(format!(
            "proof is for epoch {}, not --epoch {}",
            statement.epoch, expected.epoch
        )));
    }
    if expected
        .target
        .as_ref()
        .is_some_and(|target| *target != loaded.target)
    {
        return Err(CliError::verify(
            "proof binds another target address than --target",
        ));
    }
    let encoded = json
        .get("proof")
        .and_then(Json::as_str)
        .ok_or_else(|| CliError::verify("migration proof file has no proof"))?;
    let cap = max_proof_bytes(statement)
        .ok_or_else(|| CliError::verify("statement has no ownership relation"))?;
    if encoded.len() > base64_len(cap) {
        return Err(CliError::verify(format!(
            "proof is larger than any proof of this statement ({cap} bytes)"
        )));
    }
    let bytes =
        from_base64(encoded).ok_or_else(|| CliError::verify("proof is not canonical base64"))?;
    if json.get("proof_bytes").and_then(Json::as_u64) != u64::try_from(bytes.len()).ok() {
        return Err(CliError::verify("proof_bytes does not match the proof"));
    }
    let proof = OwnershipProof::from_bytes(&bytes, statement)
        .ok_or_else(|| CliError::verify("proof is not a canonical ownership proof"))?;
    if !verify_ownership(statement, REGIME, &proof) {
        return Err(CliError::verify("migration proof verification failed"));
    }
    Ok(loaded)
}

const VERIFY_OPTIONS: &[&str] = &["proof", "target", "epoch", "domain-hex"];
const VERIFY_HELP: &str = "\
  --epoch <n>            the epoch the verifier is in; the proof must be for it
  --domain-hex <64-hex>  the migration domain (default: the built-in QSAG domain)
  --target <address>     require this target address (default: accept the proof's own)
";

fn verify(raw: &[String]) -> Result<(), CliError> {
    let mut options = VERIFY_OPTIONS.to_vec();
    options.extend(REGISTRY_OPTIONS);
    let mut flags = REGISTRY_FLAGS.to_vec();
    flags.push("register");
    let args = Args::parse(raw, &options, &flags)?;
    if args.flag("help") {
        print!(
            "dregg-sig migrate verify --proof <path> --epoch <n> [--domain-hex <64-hex>] [--target <address>] [--register --registry-dir <dir> ..] [--json]\n\n\
Verify a migration proof: the proof itself, that its target address is the one the statement\n\
commits to, and that epoch, domain and (if given) target are the ones expected.\n\
Exit code 2: the proof is refused. With --register, exit code 4: the proof is valid and the\n\
registry refuses it (the nullifier or the legacy credential is already bound elsewhere).\n\n\
{VERIFY_HELP}  --register             record the verified binding as finalized in --registry-dir\n{REGISTRY_HELP}"
        );
        return Ok(());
    }
    args.no_positionals()?;
    if !args.flag("register") {
        if let Some(option) = REGISTRY_OPTIONS.iter().find(|o| args.get(o).is_some()) {
            return Err(CliError::usage(format!(
                "--{option} applies only with --register"
            )));
        }
        let loaded = load_verified(args.require("proof")?, &Expectation::from_args(&args)?)?;
        if args.flag("json") {
            let mut report = vec![("valid", Json::Bool(true))];
            report.extend(statement_members(&loaded.statement, &loaded.target_text));
            print!("{}", Json::object(report).to_pretty());
        } else {
            println!("valid ({})", summary(&loaded));
        }
        return Ok(());
    }
    submit(&args, Submission::Register)
}

// ============================================================================
// Registry
// ============================================================================

const ROOT_NAME: &str = "registry.json";
const ANCHOR_DOMAIN: &str = "migration_registry";
const ANCHOR_SEAL_FIELD: &str = "anchor_registry_seal";

const REGISTRY_OPTIONS: &[&str] = &[
    "registry-dir",
    "anchor-dir",
    "anchor-tpm-nv",
    "anchor-tpm-device",
    "anchor-tpm-auth-env",
    "min-checkpoint",
    "passphrase-env",
    "passphrase-file",
];

const REGISTRY_FLAGS: &[&str] = &[
    "allow-single-disk-anchor",
    "anchor-vmgenid",
    "anchor-vmgenid-strict",
    "json",
    "help",
];

const REGISTRY_HELP: &str = "\
  --registry-dir <dir>          the registry directory
  --anchor-dir <dir>            the registry's external monotone anchor (required if it was
                                created with one)
  --allow-single-disk-anchor    permit --anchor-dir on the registry's filesystem device
  --min-checkpoint <n>:<hex>    for a registry without an anchor: refuse a log that is behind
                                this checkpoint (the checkpoint an earlier command printed)
  --passphrase-env <VAR> / --passphrase-file <PATH>  unlock a sealed registry key
  --json                        print the result as JSON
";

fn registry_error(err: RegistryError) -> CliError {
    match err {
        RegistryError::Io(e) => CliError::io("migration registry", e),
        other => CliError::state(format!("migration registry: {other}")),
    }
}

fn root_path(dir: &str) -> Result<String, CliError> {
    std::path::Path::new(dir)
        .join(ROOT_NAME)
        .to_str()
        .map(str::to_owned)
        .ok_or_else(|| CliError::usage("--registry-dir is not UTF-8"))
}

fn registry_secret(seed: &Secret32, label: &[u8]) -> Secret32 {
    Secret32::new(cshake256_framed_32(
        b"QSAG.CLI.MIGRATE.REGISTRY.KDF.V1",
        &[&seed.0, label],
    ))
}

/// The log's MAC key. It depends on whether the registry was created with an anchor, so
/// a root file edited to drop the anchor requirement opens no log.
fn log_key(seed: &Secret32, anchored: bool) -> Secret32 {
    registry_secret(
        seed,
        if anchored {
            b"log mac, anchored"
        } else {
            b"log mac, unanchored"
        },
    )
}

fn registry_id(seed: &Secret32, nonce: &[u8]) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.CLI.MIGRATE.REGISTRY.ID.V1",
        &[&registry_secret(seed, b"identifier").0, nonce],
    )
}

fn anchor_config(args: &Args, dir: &str) -> Result<Option<AnchorConfig>, CliError> {
    AnchorConfig::for_vault(args, dir, "anchor-dir", "allow-single-disk-anchor")
}

fn parse_checkpoint(text: &str) -> Result<dregg_sig_core::LedgerCheckpoint, CliError> {
    let bad = || CliError::usage("--min-checkpoint must be <generation>:<64-hex tag>");
    let (generation, tag) = text.split_once(':').ok_or_else(bad)?;
    Ok(dregg_sig_core::LedgerCheckpoint {
        generation: generation.parse().map_err(|_| bad())?,
        tag: from_hex_exact::<32>(tag, "--min-checkpoint tag").map_err(|_| bad())?,
    })
}

fn checkpoint_members(checkpoint: dregg_sig_core::LedgerCheckpoint) -> Vec<(&'static str, Json)> {
    vec![(
        "checkpoint",
        Json::str(format!(
            "{}:{}",
            checkpoint.generation,
            to_hex(&checkpoint.tag)
        )),
    )]
}

const INIT_HELP: &str = "\
dregg-sig migrate registry init --registry-dir <dir> (--anchor-dir <dir> | --ephemeral-unanchored)

Create an empty migration registry in a fresh owner-only directory. The registry records each
verified migration once: a nullifier, and the legacy credential behind it, stay bound to one
post-quantum address.

  --anchor-dir <dir>            ratchet the log's length and tip in an external monotone
                                anchor, so that restoring an old copy of the registry is refused
  --allow-single-disk-anchor    permit --anchor-dir on the registry's filesystem device
  --ephemeral-unanchored        create a registry without rollback protection (required when
                                no anchor is given); --min-checkpoint is then the only defence
  --passphrase-env <VAR> / --passphrase-file <PATH>  seal the registry key
  --json                        print the registry identifier as JSON
";

fn init(raw: &[String]) -> Result<(), CliError> {
    let mut flags = REGISTRY_FLAGS.to_vec();
    flags.push("ephemeral-unanchored");
    let args = Args::parse(raw, REGISTRY_OPTIONS, &flags)?;
    if args.flag("help") {
        print!("{INIT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let dir = args.require("registry-dir")?;
    if args.get("min-checkpoint").is_some() {
        return Err(CliError::usage(
            "--min-checkpoint does not apply to registry init",
        ));
    }
    let anchor_cfg = anchor_config(&args, dir)?;
    crate::anchor::require_anchor_or_waiver(
        anchor_cfg.is_some(),
        args.flag("ephemeral-unanchored"),
        "anchor-dir",
    )?;
    let passphrase = crate::envelope::passphrase(&args)?;

    private_dir(dir, true)?;
    let occupied = std::fs::read_dir(dir)
        .map_err(|e| CliError::io(format_args!("reading {dir}"), e))?
        .next()
        .is_some();
    if occupied {
        return Err(CliError::state(format!(
            "{dir} is not empty; a migration registry is created only in a fresh directory"
        )));
    }
    let root = root_path(dir)?;
    if let Some(cfg) = &anchor_cfg {
        cfg.validate_isolation(&[&root], &[dir], true)?;
    }
    let mut vault = Vault::acquire(&root, true)?;
    let seed = Secret32::new(os_random_32()?);
    let nonce = os_random_32()?;
    let nonce = &nonce[..16];
    let id = registry_id(&seed, nonce);
    let key = log_key(&seed, anchor_cfg.is_some());

    let (registry, anchor_seal) = match &anchor_cfg {
        Some(cfg) => {
            let anchor = FsExternalMountAnchor::provision_fresh(
                cfg,
                &[&root],
                &[dir],
                ANCHOR_DOMAIN,
                id,
                registry_secret(&seed, b"anchor mac").0,
            )?;
            let seal = anchor.lock_identity_seal();
            (
                NullifierRegistry::create_anchored(dir, key.0, Box::new(anchor)),
                Some(seal),
            )
        }
        None => (NullifierRegistry::create(dir, key.0), None),
    };
    let registry = registry.map_err(registry_error)?;

    let mut file = Json::object(vec![
        ("format", Json::str(REGISTRY_FORMAT)),
        ("scheme", Json::str(REGISTRY_SCHEME)),
        ("enrollment_nonce", Json::hex(nonce)),
        ("registry_id", Json::hex(&id)),
    ]);
    if let Some(seal) = &anchor_seal {
        set(&mut file, "anchor_required", Json::Bool(true));
        set(&mut file, ANCHOR_SEAL_FIELD, Json::hex(seal));
    }
    set(&mut file, "seed", Json::hex(&seed.0));
    vault.set_key_material(&crate::envelope::open(&file, None)?);
    if let Some(pass) = &passphrase {
        crate::envelope::seal(&mut file, pass)?;
    }
    vault.bind(&mut file)?;
    vault.seal(&mut file)?;
    let encoded = ZeroizingBuf::new(file.to_pretty().into_bytes());
    // Written last: a directory without it was never a usable registry.
    write_new(&root, &encoded.0, true)?;

    if args.flag("json") {
        let mut report = vec![
            ("registry_id", Json::hex(&id)),
            ("anchored", Json::Bool(anchor_cfg.is_some())),
        ];
        report.extend(checkpoint_members(registry.checkpoint()));
        print!("{}", Json::object(report).to_pretty());
    } else {
        println!("created migration registry {} in {dir}", to_hex(&id));
    }
    Ok(())
}

/// Open the registry the options name, under its anchor if it has one.
fn open_registry(args: &Args) -> Result<NullifierRegistry, CliError> {
    let dir = args.require("registry-dir")?;
    let passphrase = crate::envelope::passphrase(args)?;
    let anchor_cfg = anchor_config(args, dir)?;
    let minimum = args
        .get("min-checkpoint")
        .map(parse_checkpoint)
        .transpose()?;
    private_dir(dir, false)?;
    let root = root_path(dir)?;
    let mut vault = Vault::acquire(&root, false)?;
    let text = read_text(&root)?;
    let on_disk = Json::parse(&text)?;
    if on_disk.field_str("format")? != REGISTRY_FORMAT
        || on_disk.field_str("scheme")? != REGISTRY_SCHEME
    {
        return Err(CliError::input(format!(
            "{root} is not a {REGISTRY_FORMAT} file"
        )));
    }
    let opened = crate::envelope::open(&on_disk, passphrase.as_deref().map(Vec::as_slice))?;
    vault.set_key_material(&opened);
    vault.authenticate(&on_disk)?;
    let anchored = crate::anchor::anchor_requirement(&on_disk, anchor_cfg.is_some()).map_err(
        |e| match e {
            AnchorRequirementError::Malformed => crate::vault::corrupt(),
            AnchorRequirementError::AnchorMissing => CliError::state(
                "migration registry was created with an external anchor; its anchor directory is required",
            ),
            AnchorRequirementError::NotEnrolled => {
                CliError::state("migration registry was not created with an external anchor")
            }
        },
    )?;
    let seed = opened.seed()?;
    let nonce = on_disk.field_hex("enrollment_nonce")?;
    let id = registry_id(&seed, &nonce);
    let recorded: [u8; 32] = from_hex_exact(on_disk.field_str("registry_id")?, "registry_id")?;
    if id != recorded {
        return Err(crate::vault::corrupt());
    }
    let key = log_key(&seed, anchored);
    match (anchor_cfg, minimum) {
        (Some(_), Some(_)) => Err(CliError::usage(
            "--min-checkpoint applies to a registry without an anchor; the anchor already holds the checkpoint",
        )),
        (Some(cfg), None) => {
            let anchor = FsExternalMountAnchor::open_existing(
                &cfg,
                &[&root],
                &[dir],
                ANCHOR_DOMAIN,
                id,
                registry_secret(&seed, b"anchor mac").0,
            )?;
            anchor.verify_expected_seal(&on_disk, ANCHOR_SEAL_FIELD)?;
            NullifierRegistry::open_anchored(dir, key.0, Box::new(anchor)).map_err(registry_error)
        }
        (None, Some(minimum)) => {
            NullifierRegistry::open_at_least(dir, key.0, minimum).map_err(registry_error)
        }
        (None, None) => NullifierRegistry::open(dir, key.0).map_err(registry_error),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Submission {
    Register,
    Enroll,
    Finalize,
}

impl Submission {
    fn name(self) -> &'static str {
        match self {
            Self::Register => "register",
            Self::Enroll => "enroll",
            Self::Finalize => "finalize",
        }
    }
}

fn status_name(status: BindingStatus) -> &'static str {
    match status {
        BindingStatus::Enrolled => "enrolled",
        BindingStatus::Finalized => "finalized",
    }
}

/// Verify the proof, then submit its binding. The registry is opened only after the proof
/// verified, and the binding submitted is the verified statement's own.
fn submit(args: &Args, submission: Submission) -> Result<(), CliError> {
    args.require("registry-dir")?;
    let loaded = load_verified(args.require("proof")?, &Expectation::from_args(args)?)?;
    let binding = loaded.statement.binding();
    let mut registry = open_registry(args)?;
    let receipt: Receipt = match submission {
        Submission::Register => registry.register(&binding),
        Submission::Enroll => registry.enroll(&binding),
        Submission::Finalize => registry.finalize(&binding),
    }
    .map_err(registry_error)?;
    if args.flag("json") {
        let mut report = vec![
            ("valid", Json::Bool(true)),
            ("operation", Json::str(submission.name())),
            ("status", Json::str(status_name(receipt.status))),
            ("appended", Json::Bool(receipt.appended)),
        ];
        report.extend(checkpoint_members(receipt.checkpoint));
        report.extend(statement_members(&loaded.statement, &loaded.target_text));
        print!("{}", Json::object(report).to_pretty());
    } else {
        println!(
            "valid ({}); {} ({}); checkpoint {}:{}",
            summary(&loaded),
            status_name(receipt.status),
            if receipt.appended {
                "recorded"
            } else {
                "already recorded"
            },
            receipt.checkpoint.generation,
            to_hex(&receipt.checkpoint.tag)
        );
    }
    Ok(())
}

fn registry_submit(raw: &[String], submission: Submission) -> Result<(), CliError> {
    let mut options = VERIFY_OPTIONS.to_vec();
    options.extend(REGISTRY_OPTIONS);
    let args = Args::parse(raw, &options, REGISTRY_FLAGS)?;
    if args.flag("help") {
        let what = match submission {
            Submission::Register => {
                "Verify a migration proof and record its binding as finalized, in one step."
            }
            Submission::Enroll => {
                "Verify a migration proof and reserve its binding; legacy authorisation stays on\nuntil `finalize`."
            }
            Submission::Finalize => {
                "Verify the proof of an enrolled binding again and mark it finalized."
            }
        };
        print!(
            "dregg-sig migrate registry {} --registry-dir <dir> --proof <path> --epoch <n> [--domain-hex <64-hex>] [--target <address>]\n\n\
{what}\nAn identical submission is accepted again without writing. Exit code 2: the proof is refused.\n\
Exit code 4: the registry refuses the binding or does not open.\n\n{VERIFY_HELP}{REGISTRY_HELP}",
            submission.name()
        );
        return Ok(());
    }
    args.no_positionals()?;
    submit(&args, submission)
}

fn binding_members(found: &RegisteredBinding) -> Vec<(&'static str, Json)> {
    let binding = &found.binding;
    vec![
        ("status", Json::str(status_name(found.status))),
        ("ordinal", Json::num(found.ordinal)),
        ("nullifier", Json::hex(&binding.nullifier)),
        ("legacy_id", Json::hex(&binding.legacy_id)),
        ("pq_commitment", Json::hex(&binding.pq_commitment)),
        ("epoch", Json::num(binding.epoch)),
        ("migration_domain", Json::hex(&binding.migration_domain)),
        (
            "key_exposure",
            Json::str(match binding.exposure {
                dregg_sig_migrate::hem::registry::KeyExposure::Hidden => "hidden",
                dregg_sig_migrate::hem::registry::KeyExposure::Revealed => "revealed",
            }),
        ),
    ]
}

fn lookup(raw: &[String]) -> Result<(), CliError> {
    let mut options = vec!["nullifier", "legacy-id", "statement"];
    options.extend(REGISTRY_OPTIONS);
    let args = Args::parse(raw, &options, REGISTRY_FLAGS)?;
    if args.flag("help") {
        print!(
            "dregg-sig migrate registry lookup --registry-dir <dir> (--nullifier <64-hex> | --legacy-id <64-hex> | --statement <claim or proof file>)\n\n\
Report what the registry holds for a nullifier or for a legacy credential. --statement takes\n\
both from a claim or proof file, without verifying any proof. Exit code 0 whether or not a\n\
binding is recorded; the output says `absent` when none is.\n\n{REGISTRY_HELP}"
        );
        return Ok(());
    }
    args.no_positionals()?;
    args.require("registry-dir")?;
    let selectors = [
        args.get("nullifier"),
        args.get("legacy-id"),
        args.get("statement"),
    ];
    if selectors.iter().flatten().count() != 1 {
        return Err(CliError::usage(
            "lookup takes exactly one of --nullifier, --legacy-id and --statement",
        ));
    }
    let (nullifier, legacy_id) = match selectors {
        [Some(hex), _, _] => (Some(from_hex_exact::<32>(hex, "--nullifier")?), None),
        [_, Some(hex), _] => (None, Some(from_hex_exact::<32>(hex, "--legacy-id")?)),
        [_, _, Some(path)] => {
            let json = read_document(path)?.map_err(CliError::input)?;
            let loaded = load_statement(&json, CLAIM_FORMAT, &[])
                .or_else(|_| {
                    load_statement(&json, PROOF_FORMAT, &["regime", "proof_bytes", "proof"])
                })
                .map_err(|e| CliError::input(format!("{path}: {e}")))?;
            let binding = loaded.statement.binding();
            (Some(binding.nullifier), Some(binding.legacy_id))
        }
        _ => (None, None),
    };
    let registry = open_registry(&args)?;
    let by_nullifier = nullifier
        .map(|n| registry.lookup(&n))
        .transpose()
        .map_err(registry_error)?
        .flatten();
    let by_legacy = legacy_id
        .map(|l| registry.lookup_legacy(&l))
        .transpose()
        .map_err(registry_error)?
        .flatten();
    let render = |found: &Option<RegisteredBinding>| match found {
        Some(found) => Json::object(binding_members(found)),
        None => Json::object(vec![("status", Json::str("absent"))]),
    };
    if args.flag("json") {
        let mut report = Vec::new();
        if nullifier.is_some() {
            report.push(("by_nullifier", render(&by_nullifier)));
        }
        if legacy_id.is_some() {
            report.push(("by_legacy_id", render(&by_legacy)));
        }
        report.extend(checkpoint_members(registry.checkpoint()));
        print!("{}", Json::object(report).to_pretty());
    } else {
        let line = |what: &str, found: &Option<RegisteredBinding>| match found {
            Some(found) => println!(
                "{what}: {} to {} at epoch {} (nullifier {}, record {})",
                status_name(found.status),
                to_hex(&found.binding.pq_commitment),
                found.binding.epoch,
                to_hex(&found.binding.nullifier),
                found.ordinal
            ),
            None => println!("{what}: absent"),
        };
        if nullifier.is_some() {
            line("nullifier", &by_nullifier);
        }
        if legacy_id.is_some() {
            line("legacy credential", &by_legacy);
        }
    }
    Ok(())
}

const REGISTRY_COMMAND_HELP: &str = "\
dregg-sig migrate registry <subcommand> [options]

The durable one-way migration registry:
  init      create an empty registry (--anchor-dir, or --ephemeral-unanchored)
  register  verify a proof and record its binding as finalized
  enroll    verify a proof and reserve its binding
  finalize  verify the proof of an enrolled binding and mark it finalized
  lookup    report the binding of a nullifier or a legacy credential
";

fn registry(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{REGISTRY_COMMAND_HELP}");
        return Err(CliError::usage(
            "migrate registry requires a subcommand (try --help)",
        ));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{REGISTRY_COMMAND_HELP}");
            Ok(())
        }
        "init" => init(rest),
        "register" => registry_submit(rest, Submission::Register),
        "enroll" => registry_submit(rest, Submission::Enroll),
        "finalize" => registry_submit(rest, Submission::Finalize),
        "lookup" => lookup(rest),
        other => Err(CliError::usage(format!(
            "unknown migrate registry subcommand '{other}' (expected init, register, enroll, finalize, or lookup)"
        ))),
    }
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((sub, rest)) = raw.split_first() else {
        print!("{MIGRATE_HELP}{}", kinds_help());
        return Err(CliError::usage(
            "migrate requires a subcommand (try --help)",
        ));
    };
    match sub.as_str() {
        "--help" | "-h" | "help" => {
            print!("{MIGRATE_HELP}{}", kinds_help());
            Ok(())
        }
        "claim" | "commit" => claim(rest),
        "prove" => prove(rest),
        "verify" => verify(rest),
        "registry" => registry(rest),
        other => Err(CliError::usage(format!(
            "unknown migrate subcommand '{other}' (expected claim, prove, verify, or registry)"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sig_addr::{KeyIdentityKind, WitnessSuiteTag};

    fn address(seed: u8) -> QsagAddress {
        QsagAddress::from_pubkey_cshake256(
            "qsp",
            WitnessSuiteTag::MlDsa65,
            KeyIdentityKind::SingleOrThreshold,
            &[seed; 32],
        )
        .unwrap()
    }

    fn target() -> QsagAddress {
        address(7)
    }

    /// One statement per table entry, from fixed secrets.
    fn statements() -> Vec<(&'static KindSpec, OwnershipStatement, OwnershipWitness)> {
        KINDS
            .iter()
            .map(|&kind| {
                let secret: Vec<u8> = match kind.secret {
                    SecretForm::Key32 => (1..=32).collect(),
                    SecretForm::HexSeed => (1..=16).collect(),
                };
                let path = if kind.derivation_path {
                    parse_path("m/44'/0'/0'/0/0").unwrap()
                } else {
                    Vec::new()
                };
                let witness = (kind.witness)(&secret).unwrap();
                let statement = OwnershipStatement::derive(
                    &(kind.claim)(path),
                    &witness,
                    pq_commitment(&target()),
                    [9; 32],
                    3,
                )
                .unwrap();
                (kind, statement, witness)
            })
            .collect()
    }

    #[test]
    fn every_table_entry_derives_a_claim_that_maps_back_to_it_and_renders() {
        let mut names = Vec::new();
        for (kind, statement, _) in statements() {
            assert!(
                std::ptr::eq(kind_of(&statement.claim), kind),
                "{}",
                kind.name
            );
            assert!(!(kind.render)(&statement.claim).is_empty(), "{}", kind.name);
            assert!(std::ptr::eq(kind_by_name(kind.name).unwrap(), kind));
            names.push(kind.name);
            for alias in kind.aliases {
                assert!(std::ptr::eq(kind_by_name(alias).unwrap(), kind));
                names.push(alias);
            }
            // A claim of another kind renders to nothing under this entry.
            for (other, foreign, _) in statements() {
                if !std::ptr::eq(other, kind) {
                    assert!((kind.render)(&foreign.claim).is_empty());
                }
            }
        }
        let count = names.len();
        names.sort_unstable();
        names.dedup();
        assert_eq!(
            names.len(),
            count,
            "kind names and aliases must be distinct"
        );
        assert!(kind_by_name("btc-taproot").is_err());
    }

    #[test]
    fn statement_documents_round_trip_and_reject_any_other_content() {
        let text = target().encode().unwrap();
        for (kind, statement, _) in statements() {
            let doc = document(CLAIM_FORMAT, statement_members(&statement, &text));
            let loaded = load_statement(&doc, CLAIM_FORMAT, &[]).unwrap();
            assert_eq!(loaded.statement, statement, "{}", kind.name);
            assert_eq!(loaded.target, target());
            assert!(load_statement(&doc, PROOF_FORMAT, &[]).is_err());
            let Json::Object(members) = &doc else {
                unreachable!()
            };
            // Every member is checked: changing, dropping or adding one is refused.
            for index in 1..members.len() {
                let mut changed = members.clone();
                changed[index].1 = Json::str("00");
                assert!(
                    load_statement(&Json::Object(changed), CLAIM_FORMAT, &[]).is_err(),
                    "{} member {}",
                    kind.name,
                    members[index].0
                );
                let mut dropped = members.clone();
                dropped.remove(index);
                assert!(load_statement(&Json::Object(dropped), CLAIM_FORMAT, &[]).is_err());
            }
            let mut added = members.clone();
            added.push(("note".into(), Json::str("x")));
            assert!(load_statement(&Json::Object(added), CLAIM_FORMAT, &[]).is_err());
        }
        // Another address than the committed one, in canonical form.
        let (_, statement, _) = statements().remove(0);
        let other = address(8).encode().unwrap();
        let doc = document(CLAIM_FORMAT, statement_members(&statement, &other));
        let err = load_statement(&doc, CLAIM_FORMAT, &[]).err().unwrap();
        assert!(err.contains("commits to"), "{err}");
    }

    #[test]
    fn base64_is_canonical_and_strict() {
        for (bytes, text) in [
            (&b""[..], ""),
            (b"f", "Zg=="),
            (b"fo", "Zm8="),
            (b"foo", "Zm9v"),
            (b"foob", "Zm9vYg=="),
            (b"fooba", "Zm9vYmE="),
            (b"foobar", "Zm9vYmFy"),
            (&[0xfb, 0xff, 0xfe], "+//+"),
        ] {
            assert_eq!(to_base64(bytes), text);
            assert_eq!(from_base64(text).as_deref(), Some(bytes));
            assert_eq!(base64_len(bytes.len()), text.len());
        }
        for bad in [
            "Zg", "Zg=", "Zg===", "Z===", "Zh==", "Zm9=", "Zm8=Zm8=", "Zm9v\n", " Zm9v", "Zm-v",
            "Zm_v", "=m9v", "Z=9v",
        ] {
            assert_eq!(from_base64(bad), None, "{bad:?}");
        }
        let all: Vec<u8> = (0..=255).collect();
        for len in 0..all.len() {
            assert_eq!(from_base64(&to_base64(&all[..len])).unwrap(), all[..len]);
        }
    }

    #[test]
    fn bip32_paths_parse_and_print() {
        let h = BIP32_HARDENED;
        for (text, path) in [
            ("m", vec![]),
            ("m/0", vec![0]),
            ("m/44'/0'/0'/0/0", vec![44 | h, h, h, 0, 0]),
            ("m/2147483647'/1", vec![0x7fff_ffff | h, 1]),
        ] {
            assert_eq!(parse_path(text).unwrap(), path);
            assert_eq!(format_path(&path), text);
        }
        assert_eq!(parse_path("m/44h/1H").unwrap(), vec![44 | h, 1 | h]);
        for bad in [
            "",
            "44'/0'",
            "m/",
            "m//0",
            "M/0",
            "m/2147483648",
            "m/-1",
            "m/+1",
            "m/0''",
            "m/x",
            "m/0/1/2/3/4/5/6/7/8/9/10",
        ] {
            assert!(parse_path(bad).is_err(), "{bad:?}");
        }
        assert_eq!(parse_path("m/0/1/2/3/4/5/6/7/8/9").unwrap().len(), 10);
    }

    #[test]
    fn registry_keys_are_separated_by_purpose_and_by_anchoring() {
        let seed = Secret32::new([3; 32]);
        let keys = [
            log_key(&seed, true).0,
            log_key(&seed, false).0,
            registry_secret(&seed, b"anchor mac").0,
            registry_secret(&seed, b"identifier").0,
            log_key(&Secret32::new([4; 32]), true).0,
        ];
        for (i, a) in keys.iter().enumerate() {
            for b in &keys[i + 1..] {
                assert_ne!(a, b);
            }
        }
        assert_ne!(registry_id(&seed, &[1; 16]), registry_id(&seed, &[2; 16]));
    }

    /// The bound must hold for every kind, and must be a bound on this statement's
    /// proof, not a blanket ceiling.
    #[test]
    fn proof_size_bound_covers_every_kind_and_stays_within_a_factor_of_two() {
        for (kind, statement, witness) in statements() {
            let cap = max_proof_bytes(&statement).unwrap();
            let proof = prove_ownership(&statement, &witness, REGIME, &[5; 32]).unwrap();
            let len = proof.to_bytes().len();
            println!("{}: proof {len} bytes, bound {cap} bytes", kind.name);
            assert!(len <= cap, "{}: {len} > {cap}", kind.name);
            assert!(cap < 2 * len, "{}: bound {cap} for {len}", kind.name);
        }
    }
}
