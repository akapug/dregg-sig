// SPDX-License-Identifier: Apache-2.0 OR MIT
#![no_main]

//! Coverage-guided hostile wire-decoder, canonical roundtrip, and adversarial verifier fuzzer
//! across the `zk-Hem`, recursive shard/WHIR merge, `Corduroy-Poseidon2`, and height-20
//! `Jorts-Poseidon2` wire codecs in `dregg-sig-agg`:
//!
//! 1. `zk_hem::protocol::ZkHemProof::from_bytes` + `protocol::verify`
//! 2. `zk_hem::protocol::PublicHemProof::from_bytes` + `protocol::verify_public`
//! 3. `zk_hem::recursive_whir::FixedPathWhirProof::from_bytes` (`QSAGFWP1`) + `verify_fixed_path`
//!    and `SuccinctChildWhirMerge::from_bytes` (`QSAGFWP1`) + `verify_succinct_children_whir_merge`
//! 4. `zk_hem::full_shard::RecursiveShardProof::from_bytes` (`QSAGRSP1`) + `verify_recursive_shard`
//! 5. `sig::ValidatorSignature::from_bytes_canonical` for `CorduroyPoseidon2` (`76,896` B) and
//!    `JortsPoseidon2H20` (`4,776` B) + `verify_individual_signature`.
//!
//! Every fixture is built in `LLVMFuzzerInitialize` (the `init:` block), before libFuzzer
//! arms its per-input watchdog.
//!
//! Not covered here: `FullShardMergeProof::from_bytes` (`QSAGFSM1`) and
//! `SuccinctFullShardAggregate::from_bytes_canonical` (`QSAGFSA1`). Both take a
//! `&FullShardMergeRelation`, whose only constructor synthesizes the in-circuit WHIR verifier
//! (about 2.7M rows per child) and compiles its hologram: minutes under coverage
//! instrumentation. The `HologramPublicProof` decoder and verifier both wrap, and the
//! key-only `QSAGSTA1` subtree carriers, are fuzzed in `fuzz_hologram_and_subtree_decode`.

use std::sync::OnceLock;

use dregg_sig_agg::field::{Goldilocks, GoldilocksExt4};
use dregg_sig_agg::pcs::WhirSecurityRegime;
use dregg_sig_agg::zk_hem::full_shard::{
    FullShardParams, RECURSIVE_SHARD_WIRE_MAGIC, RecursiveShardProof, RecursiveShardStatement,
    verify_recursive_shard,
};
use dregg_sig_agg::zk_hem::protocol::{self, PublicHemProof, ZkHemProof};
use dregg_sig_agg::zk_hem::recursive_whir::{
    ChildWhirMergeRelation, ChildWhirStatement, FixedPathWhirParams, FixedPathWhirProof,
    SuccinctChildWhirMerge, verify_fixed_path, verify_succinct_children_whir_merge,
};
use dregg_sig_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape, sponge12};
use dregg_sig_agg::{
    AggSigProfile, SignerBitmap, ValidatorPublicKey, ValidatorSignature,
    verify_individual_signature,
};
use libfuzzer_sys::fuzz_target;

struct FuzzFixtures {
    generic_shape: Shape,
    fp_params: FixedPathWhirParams,
    fp_stmt: ChildWhirStatement,
    child_whir_rel: ChildWhirMergeRelation,
    fs_params: FullShardParams,
    fs_shard_stmt: RecursiveShardStatement,
    corduroy_pk: ValidatorPublicKey,
    jorts20_pk: ValidatorPublicKey,
}

/// Opening size of the recursive-WHIR fixtures. The merge relation embeds a WHIR verifier
/// for this size: about 40 MB at 6 variables, about 420 MB at 12.
const FIXED_PATH_NUM_VARS: usize = 6;

fn fixtures() -> &'static FuzzFixtures {
    static FX: OnceLock<FuzzFixtures> = OnceLock::new();
    FX.get_or_init(|| {
        let f = Goldilocks::from_u64_reduced;

        // 1. Minimal generic zk-Hem / PublicHem `Shape` (1 public input, 1 sponge12, 1 boolean).
        let mut cs = ConstraintSystem::new();
        let pub_in: Lc = cs.public_input(f(7)).into();
        let sec_var: Lc = cs.alloc(f(1)).into();
        cs.enforce_boolean(&sec_var);
        let st = sponge12(&mut cs, &[pub_in, sec_var]);
        let _ = cs.mul(&st[0], &st[1]);
        let (generic_shape, _) = cs.finish();

        // 2. `FixedPathWhirParams` + 1-child `ChildWhirMergeRelation`.
        let fp_regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;
        let fp_params =
            FixedPathWhirParams::new(fp_regime, FIXED_PATH_NUM_VARS).expect("FixedPathWhirParams");
        let fp_stmt = ChildWhirStatement {
            shard_header: [0xAB; 32],
            commitment: [f(3); 4],
            point: vec![GoldilocksExt4::ZERO; FIXED_PATH_NUM_VARS],
            value: GoldilocksExt4::ZERO,
        };
        let child_whir_rel =
            ChildWhirMergeRelation::with_children(fp_params.clone(), 1).expect("ChildWhirMerge");

        // 3. `FullShardParams` (`slots = 2`) for `RecursiveShardProof`.
        let fs_params = FullShardParams::new(fp_regime, 2).expect("FullShardParams");
        let jorts_pk0 = ValidatorPublicKey {
            profile: AggSigProfile::JortsPoseidon2,
            pk_seed: [f(0x101); 4],
            pk_root: [f(0x202); 4],
        };
        let jorts_pk1 = ValidatorPublicKey {
            profile: AggSigProfile::JortsPoseidon2,
            pk_seed: [f(0x303); 4],
            pk_root: [f(0x404); 4],
        };
        let fs_shard_stmt = RecursiveShardStatement {
            keys: vec![jorts_pk0, jorts_pk1],
            bitmap: SignerBitmap::from_active_indices(2, &[0]).expect("bitmap"),
            message: [0x5A; 32],
        };

        // 4. Dummy keys for `CorduroyPoseidon2` and height-20 `JortsPoseidon2H20`.
        let corduroy_pk = ValidatorPublicKey {
            profile: AggSigProfile::CorduroyPoseidon2,
            pk_seed: [f(0x77); 4],
            pk_root: [f(0x88); 4],
        };
        let jorts20_pk = ValidatorPublicKey {
            profile: AggSigProfile::JortsPoseidon2H20,
            pk_seed: [f(0x99); 4],
            pk_root: [f(0xAA); 4],
        };

        FuzzFixtures {
            generic_shape,
            fp_params,
            fp_stmt,
            child_whir_rel,
            fs_params,
            fs_shard_stmt,
            corduroy_pk,
            jorts20_pk,
        }
    })
}

fn with_magic(magic: &[u8; 8], data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + data.len());
    out.extend_from_slice(magic);
    out.extend_from_slice(data);
    out
}

fuzz_target!(init: {
    fixtures();
}, |data: &[u8]| {
    let fx = fixtures();
    let f = Goldilocks::from_u64_reduced;
    let zk_regime = if data.first().copied().unwrap_or(0) & 1 == 0 {
        WhirSecurityRegime::BciksJohnsonQrom128
    } else {
        WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128
    };
    let rec_regime = WhirSecurityRegime::Poseidon2Cdhz25ZeroPowQrom128;

    // 1. Generic `ZkHemProof` & `PublicHemProof` decoders + canonical roundtrip + verifiers
    if let Some(proof) = ZkHemProof::from_bytes(data, &fx.generic_shape, zk_regime) {
        assert_eq!(proof.to_bytes(), data);
        let _ = protocol::verify(
            &fx.generic_shape,
            &[f(7)],
            b"fuzz-generic",
            zk_regime,
            &proof,
        );
    }
    if let Some(proof) = PublicHemProof::from_bytes(data, &fx.generic_shape, zk_regime) {
        assert_eq!(proof.to_bytes(), data);
        let _ = protocol::verify_public(
            &fx.generic_shape,
            &[f(7)],
            b"fuzz-public",
            zk_regime,
            &proof,
        );
    }

    // 2. `FixedPathWhirProof` & `SuccinctChildWhirMerge` (`QSAGFWP1`) decoders + verifiers
    for candidate in [data.to_vec(), with_magic(b"QSAGFWP1", data)] {
        if let Some(proof) = FixedPathWhirProof::from_bytes(&candidate, &fx.fp_params) {
            assert_eq!(proof.to_bytes(), candidate);
            let _ = verify_fixed_path(&fx.fp_params, &fx.fp_stmt, &proof);
        }
        if let Some(merge) =
            SuccinctChildWhirMerge::from_bytes(&candidate, &fx.child_whir_rel, rec_regime)
        {
            assert_eq!(merge.to_bytes(), candidate);
            let _ = verify_succinct_children_whir_merge(
                &fx.child_whir_rel,
                std::slice::from_ref(&fx.fp_stmt),
                rec_regime,
                &merge,
            );
        }
    }

    // 3. `RecursiveShardProof` (`QSAGRSP1`) decoder + `verify_recursive_shard`
    for candidate in [data.to_vec(), with_magic(RECURSIVE_SHARD_WIRE_MAGIC, data)] {
        if let Some(proof) = RecursiveShardProof::from_bytes(&fx.fs_params, &candidate) {
            assert_eq!(proof.to_bytes(), candidate);
            let _ = verify_recursive_shard(&fx.fs_params, &fx.fs_shard_stmt, &proof);
        }
    }

    // 4. `CorduroyPoseidon2` (`76,896` B) & height-20 `JortsPoseidon2H20` (`4,776` B) codecs + verifiers
    if let Ok(sig) =
        ValidatorSignature::from_bytes_canonical(AggSigProfile::CorduroyPoseidon2, data)
    {
        assert_eq!(sig.to_bytes(), data);
        let _ = verify_individual_signature(&fx.corduroy_pk, b"fuzz-corduroy", &sig);
    }
    if let Ok(sig) =
        ValidatorSignature::from_bytes_canonical(AggSigProfile::JortsPoseidon2H20, data)
    {
        assert_eq!(sig.to_bytes(), data);
        let _ = verify_individual_signature(&fx.jorts20_pk, b"fuzz-jorts20", &sig);
    }
});
