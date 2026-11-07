#!/usr/bin/env python3
"""Record observed wrapper failures separately from unproved source obligations."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    profiles = {}
    for profile in ("core_new", "core_new_scoped", "core_new_prefixed_baseline", "core_new_closed",
                    "core_update_closed", "core_finalize_closed", "buffer_update", "buffer_finalize"):
        directory = HERE / "Artifacts" / profile
        inventory_path = directory / "inventory.json"
        inventory = json.loads(inventory_path.read_text())
        log_path = directory / ("charon.log" if inventory["charon_exit_code"] else "aeneas.log")
        if not log_path.exists():
            log_path = directory / "charon.log"
        log = re.sub(r"\x1b\[[0-9;]*m", "", log_path.read_text())
        if "GATs cannot work" in log:
            failure = "Charon rejects hybrid-array ArraySize generic associated types with the Aeneas preset's lift-associated-types pass."
        elif "only supports impl patterns" in log:
            failure = "Charon rejects an impl pattern that is not the first path element."
        elif inventory.get("counts", {}).get("ordered_decls") == 0:
            failure = "The trait-method resolver selected a declaration but produced zero ordered extraction roots; rejected before Aeneas."
        elif "PrePasses.update_array_default.matches_default_array" in log:
            failure = "Aeneas update_array_default scans ArraySize implementation metadata whose excluded trait declaration is absent, and raises CFailure at PrePasses.ml181-182."
        else:
            raise AssertionError((profile, log[-2000:]))
        files = {str(p.relative_to(REFERENCE)): digest(p) for p in directory.iterdir() if p.is_file()}
        profiles[profile] = {
            "accepted_reference": False, "charon_exit_code": inventory["charon_exit_code"],
            "aeneas_exit_code": inventory.get("aeneas_exit_code"),
            "counts": inventory.get("counts"), "observed_failure": failure,
            "files_sha256": files,
        }
    selected = json.loads((HERE / "InitialSelected/review.json").read_text())
    original = json.loads((HERE / "Artifacts/core_new_closed/sha_wrapper.llbc").read_text())["translated"]
    closure = {
        "original_llbc_sha256": selected["original_llbc_sha256"],
        "selected_llbc_sha256": selected["selected_llbc_sha256"],
        "all_original_ordered_roots_retained": original["ordered_decls"],
        "actual_function_bodies": {
            "0": {"operation": "Sha256VarCore::new", "signature": "Usize -> core::result::Result<Sha256VarCore, InvalidOutputSize>",
                  "regular_calls": [17], "global_reads": [1, 2], "user_types": [0, 1, 2]},
            "15": {"operation": "H256_224 constant initializer", "regular_calls": [], "global_reads": [], "user_types": []},
            "16": {"operation": "H256_256 constant initializer", "regular_calls": [], "global_reads": [], "user_types": []},
            "17": {"operation": "rustc-generated Sha256VarCore drop_glue", "regular_calls": [161], "global_reads": [], "user_types": [0]},
            "161": {"operation": "actual Sha256VarCore::drop under this configuration", "regular_calls": [], "global_reads": [], "user_types": [0]},
        },
        "types": {
            "0": "Sha256VarCore: state [u32;8], block_len u64",
            "1": "core::result::Result<T,E>, official Aeneas standard model",
            "2": "digest::InvalidOutputSize, zero-field Rust struct represented as Unit",
        },
        "globals": {"1": {"name": "H256_224", "type": "[u32;8]", "initializer": 15},
                    "2": {"name": "H256_256", "type": "[u32;8]", "initializer": 16}},
        "builtin_types": ["usize", "u32", "u64", "fixed arrays", "unit", "mutable borrow threaded by Aeneas"],
        "computational_trait_dispatch": [],
        "all_selected_bodies_signatures_constants_function_pointers_scanned": True,
        "removed_metadata_impls": [6, 9, 80], "already_excluded_trait": 8,
        "removed_impl_methods": [], "removed_impl_constants": [],
        "all_naming_and_src_provenance_unchanged": True,
        "remaining_non_emitted_references": selected["excluded_non_emitted_references_to_removed_metadata"],
        "these_non_emitted_declarations_are_not_part_of_reference_claim": True,
        "configuration": "sha2 default/alloc/oid; zeroize disabled; soft SHA256 compact backend; empty Drop behavior is configuration-specific and proves no erasure guarantee.",
    }
    closure_path = HERE / "typed-dependency-closure.json"
    closure_path.write_text(json.dumps(closure, indent=2) + "\n")
    files = [ROOT / ".deps/libsignal-vendor" / name for name in (
        "sha2-0.11.0/src/lib.rs", "sha2-0.11.0/src/block_api.rs", "sha2-0.11.0/src/sha256/soft.rs",
        "digest-0.11.3/src/buffer_macros/fixed.rs", "digest-0.11.3/src/block_api/ct_variable.rs",
        "block-buffer-0.12.1/src/lib.rs", "hybrid-array-0.4.13/src/lib.rs", "hybrid-array-0.4.13/src/traits.rs")]
    files += [REFERENCE / "ShaWordsWork/README.md", HERE / "extract.py", Path(__file__), closure_path,
              HERE / "proof-report.json", HERE / "InitialSelected/review.json"]
    report = {
        "accepted_reference": False, "full_sha256_digest_wrapper_refined": False,
        "profiles": profiles, "source_and_report_sha256": {str(p.relative_to(ROOT)): digest(p) for p in files},
        "proved_bounded_progress": "Actual core initialization including errors, plus actual constructor/compress_u32 composition for arbitrary16 shared words and every numeric output bit; eight standard-only kernel endpoints.",
        "observed_tool_blockers": [
            "Charon GAT lifting rejects direct actual Sha256::update/finalize_into wrapper graphs.",
            "Excluding ArraySize gets actual core update/finalize through Charon, but Aeneas prepass rejects their metadata. The initializer-only three-deletion selection is not asserted valid for these larger graphs.",
            "Existing ShaWordsWork independently records actual to_u32s -> array::from_fn -> try_from_fn_erased mutable-borrow-copy rejection; its conversion-closure proofs also have an unresolved existing Formatter type dependency.",
        ],
        "source_obligations_not_new_extraction_failures": [
            {"path": "sha2-0.11.0/src/block_api.rs:38", "operation": "update_blocks", "obligation": "Checked block_len arithmetic, hybrid Array::cast_slice_to_core, then compress256 dispatch and byte-to-word loading."},
            {"path": "hybrid-array-0.4.13/src/lib.rs:521", "operation": "cast_slice_to_core", "obligation": "Actual repr-transparent raw-pointer cast plus slice::from_raw_parts; no custom representation model adopted."},
            {"path": "block-buffer-0.12.1/src/lib.rs:160", "operation": "digest_blocks", "obligation": "Actual MaybeUninit buffer, get_pos invariants, copy_nonoverlapping, ResetGuard/Drop behavior on errors, split_blocks and leftover update."},
            {"path": "block-buffer-0.12.1/src/lib.rs:366", "operation": "digest_pad/len64_padding_be", "obligation": "Actual delimiter/zero writes, checked suffix bounds, MaybeUninit exposure, one/two compression calls and reset on errors."},
            {"path": "sha2-0.11.0/src/block_api.rs:64", "operation": "finalize_variable_core", "obligation": "Actual checked bit-length arithmetic, buffer padding callback and mutable chunks_exact_mut/Zip digest serialization."},
            {"path": "digest-0.11.3/src/block_api/ct_variable.rs:103", "operation": "CtOutWrapper::finalize_fixed_core", "obligation": "Actual default hybrid-array output construction, variable finalization, truncation slice and output copy."},
            {"path": "digest-0.11.3/src/buffer_macros/fixed.rs:202", "operation": "Sha256 Update and FixedOutput macro implementations", "obligation": "Compose the actual complete buffer/core wrappers, including success/error state and supported length domain."},
        ],
        "recommended_next_route": [
            "Retain the proved constructor and compact-word compression endpoints as reusable leaves.",
            "Resolve ArraySize/GAT metadata and model support for the exact selected wrapper graph through independently reviewed translator/model work, without replacing computational Rust bodies.",
            "Close actual byte loading and transparent array/slice conversions; keep the existing Formatter decision explicit.",
            "Translate and prove actual buffer update/padding operations with precise state, length/overflow, and error/reset domains; then compose actual finalize/output-copy wrappers.",
        ],
        "opaque_crypto_contracts_assumed": [], "source_substitutions": [],
        "standard_models_changed": False, "accepted_toolchain_changed": False,
    }
    (HERE / "wrapper-boundary-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Recorded eight expected-failure profiles and explicit wrapper obligations; no wrapper equivalence claim.")


if __name__ == "__main__":
    main()
