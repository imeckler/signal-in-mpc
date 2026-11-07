#!/usr/bin/env python3
"""Check generated references and Lean proofs, optionally using read-only caches."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile

from extract import (HERE, ROOT, PINS, PROFILES, check_sources, digest, inventory,
                     check_full_mir, check_discarded_metadata, check_body_dependencies)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path,
                        help="Existing matching mathlib/Lake package cache; read without modifying it")
    args = parser.parse_args()
    check_sources()
    backend = (HERE / PINS["aeneas"]["directory"] / "backends/lean").resolve()
    model_files = ["Aeneas/Std/Slice.lean", "Aeneas/Std/Scalar/Core.lean",
                   "Aeneas/Std/Scalar/Casts.lean", "Aeneas/Std/Scalar/CloneCopy.lean",
                   "Aeneas/Std/Scalar/Ops/Sub.lean", "Aeneas/Std/Scalar/Bitwise.lean",
                   "Aeneas/Std/Primitives.lean", "Aeneas/Std/SliceIter.lean",
                   "Aeneas/Std/Core/Iter.lean", "Aeneas/Std/WP.lean",
                   "Aeneas/Std/Core/Cmp.lean", "Aeneas/Std/Array/Array.lean",
                   "Aeneas/Std/Scalar/EqOrd.lean", "Aeneas/Std/Scalar/Ops/Rem.lean",
                   "Aeneas/Std/Scalar/Rotate.lean", "Aeneas/Std/Scalar/WrappingOps/Add.lean",
                   "Aeneas/Std/Array/Core.lean", "Aeneas/Std/SliceDef.lean",
                   "Aeneas/Data/List/List.lean", "Aeneas/Std/Scalar/Ops/Add.lean"]
    archive = ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz"
    if digest(archive) != PINS["aeneas"]["macos_aarch64_archive_sha256"]:
        raise ValueError("pinned Aeneas archive hash differs")
    with tarfile.open(archive) as bundle:
        for name in model_files:
            if bundle.extractfile("backends/lean/" + name).read() != (backend / name).read_bytes():
                raise ValueError(f"Aeneas standard model differs from pinned release: {name}")
    packages = args.packages_dir or HERE / ".lake/packages"
    if not (packages / "mathlib").is_dir():
        packages = args.packages_dir or backend / ".lake/packages"
    manifest = json.loads((backend / "lake-manifest.json").read_text())
    paths = []
    for package in manifest["packages"]:
        directory = packages / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory,
                                           text=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"wrong cached {package['name']} revision: {revision}")
        build = directory / ".lake/build/lib/lean"
        # Tool-only packages such as Cli need not have library artifacts. Lean
        # itself rejects a missing imported module during the checks below.
        if build.is_dir():
            paths.append(str(build.resolve()))
    expected_toolchain = PINS["aeneas"]["lean_toolchain"]
    for path in (ROOT / "lean-toolchain", HERE / "lean-toolchain", backend / "lean-toolchain"):
        if path.read_text().strip() != expected_toolchain:
            raise ValueError(f"Lean toolchain mismatch: {path}")

    for profile in ("key_accessors", "clamp", "sha256_round", "service_id_encode",
                    "message_type", "pkcs7_pad_selected", "aes_sub_bytes", "pkcs7_unpad_selected", "aes_layout", "sha256_compact_reviewed",
                    "aes_mix_columns_0", "aes_shift_rows", "aes_mix_phases", "aes_inverse_write"):
        check_full_mir(PROFILES[profile])
        recorded = json.loads((HERE / "Extraction" / f"{profile}.json").read_text())
        current = inventory(HERE / "Extraction" / f"libsignal_{profile}.llbc")
        if "trusted_declaration_selection" in PROFILES[profile]:
            from AesInverseLayoutWork.select_write import select
            original = HERE / recorded["source_llbc_file"]
            expected, changes = select(json.loads(original.read_text()))
            actual = json.loads((HERE / "Extraction" / f"libsignal_{profile}.llbc").read_text())
            review_path = HERE / recorded["selection_review_file"]
            review = json.loads(review_path.read_text())
            change_file = HERE / review["reversible_changes_file"]
            if (actual != expected or json.loads(change_file.read_text()) != changes or
                    digest(change_file) != review["reversible_changes_sha256"] or
                    digest(original) != recorded["source_llbc_sha256"] or
                    digest(review_path) != recorded["selection_review_sha256"] or
                    digest(HERE / recorded["selection_script_file"]) != recorded["selection_script_sha256"] or
                    digest(HERE / recorded["source_inventory_file"]) != recorded["source_inventory_sha256"] or
                    digest(HERE / recorded["independent_review_file"]) != recorded["independent_review_sha256"]):
                raise ValueError("closed declaration selection differs from reviewed provenance")
        if "trusted_preprocessing" in PROFILES[profile]:
            from MetadataWork.trim_step_metadata import normalize_data
            original = HERE / "Extraction/libsignal_sha256_compact.llbc"
            expected, edits = normalize_data(json.loads(original.read_text()))
            actual = json.loads((HERE / "Extraction" / f"libsignal_{profile}.llbc").read_text())
            reviewed = HERE / recorded["trusted_preprocessing_review"]
            review = json.loads(reviewed.read_text())
            if (actual != expected or review["changes"] != edits or
                    digest(original) != recorded["source_llbc_sha256"] or
                    digest(reviewed) != recorded["trusted_preprocessing_review_sha256"] or
                    digest(HERE / PROFILES[profile]["trusted_preprocessing"]) !=
                        recorded["trusted_preprocessing_source_sha256"]):
                raise ValueError("reviewed SHA metadata preprocessing differs")
        modeled = PROFILES[profile].get("modeled_std_functions", [])
        discarded = PROFILES[profile].get("discarded_metadata_types", [])
        if (current["has_errors"] or
                sorted(ty["name"] for ty in current["external_or_union_types"]) !=
                    sorted(discarded + PROFILES[profile].get("modeled_std_types", [])) or
                sorted(fn["name"] for fn in current["external_functions"]) != sorted(modeled) or
                current["counts"]["fun_decls"] != PROFILES[profile]["expected_functions"] or
                current["explicit_exclusions"] != [x.removeprefix("--exclude=")
                    for x in PROFILES[profile]["extra"] if x.startswith("--exclude=")] or
                not current["counts"]["ordered_decls"]):
            raise ValueError(f"incomplete reference: {profile}")
        if current["llbc_sha256"] != recorded["llbc_sha256"]:
            raise ValueError(f"LLBC provenance mismatch: {profile}")
        for name, expected in recorded["generated_files"].items():
            if digest(HERE / name) != expected:
                raise ValueError(f"generated reference changed: {name}; regenerate it with extract.py")
        check_body_dependencies(PROFILES[profile], HERE / "Extraction" / f"libsignal_{profile}.llbc")
        if discarded or PROFILES[profile].get("expected_generated_definitions"):
            generated = HERE / "LibSignalReference/Generated" / PROFILES[profile]["subdir"]
            check_discarded_metadata(PROFILES[profile], generated)

    baf = json.loads((HERE / "Extraction/baf-rfc5869-port.json").read_text())
    if digest(HERE / baf["local_file"]) != baf["local_sha256"]:
        raise ValueError("BAF RFC5869 port differs from its reviewed provenance manifest")

    for path in [*list((HERE / "LibSignalReference").rglob("*.lean")),
                 *list((ROOT / "TlsMpc/Signal").glob("*.lean"))]:
        if re.search(r"\b(sorry|admit|axiom)\b", path.read_text()):
            raise ValueError(f"unimplemented proof or custom axiom in {path}")
    subprocess.run(["lake", "build", "TlsMpc.Signal.KeyMaterial", "TlsMpc.Signal.Clamp",
                    "TlsMpc.Signal.Symmetric", "TlsMpc.Signal.ServiceId", "TlsMpc.Signal.Tag",
                    "TlsMpc.Signal.Cbc", "TlsMpc.Signal.Unpad", "TlsMpc.Signal.AesLayout", "TlsMpc.Signal.ShaCompact",
                    "TlsMpc.Signal.AesMix", "TlsMpc.Signal.AesShift", "TlsMpc.Signal.AesMixPhases",
                    "TlsMpc.Signal.AesInverseWrite"],
                   cwd=ROOT, check=True)
    output = HERE / ".lake/build/lib/lean"
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(output), str(ROOT / ".lake/build/lib/lean"),
                                       str(backend / ".lake/build/lib/lean"), *paths])
    modules = [
        "LibSignalReference/Generated/KeyAccessors/Types",
        "LibSignalReference/Generated/KeyAccessors/Funs",
        "LibSignalReference/Generated/Clamp/Types",
        "LibSignalReference/Generated/Clamp/Funs",
        "LibSignalReference/Generated/Sha256Round/Types",
        "LibSignalReference/Generated/Sha256Round/Funs",
        "LibSignalReference/Generated/ServiceIdEncode/Types",
        "LibSignalReference/Generated/ServiceIdEncode/Funs",
        "LibSignalReference/Generated/MessageType/Types",
        "LibSignalReference/Generated/MessageType/Funs",
        "LibSignalReference/Generated/Padding/Types",
        "LibSignalReference/Generated/Padding/Funs",
        "LibSignalReference/Generated/AesSubBytes/Types",
        "LibSignalReference/Generated/AesSubBytes/Funs",
        "LibSignalReference/Generated/Unpadding/Types",
        "LibSignalReference/Generated/Unpadding/Funs",
        "LibSignalReference/Generated/AesLayout/Types",
        "LibSignalReference/Generated/AesLayout/Funs",
        "LibSignalReference/Generated/Sha256Compact/Types",
        "LibSignalReference/Generated/Sha256Compact/Funs",
        "LibSignalReference/Generated/AesMix/Types",
        "LibSignalReference/Generated/AesMix/Funs",
        "LibSignalReference/Generated/AesShift/Types",
        "LibSignalReference/Generated/AesShift/Funs",
        "LibSignalReference/Generated/AesMixPhases/Types",
        "LibSignalReference/Generated/AesMixPhases/Funs",
        "LibSignalReference/Generated/AesInverseWrite/Types",
        "LibSignalReference/Generated/AesInverseWrite/Funs",
        "LibSignalReference/External/BafRFC5869",
        "LibSignalReference/Proofs/KeyAccessors",
        "LibSignalReference/Proofs/Clamp",
        "LibSignalReference/Proofs/Sha256Round",
        "LibSignalReference/Proofs/BafHkdf",
        "LibSignalReference/Proofs/ServiceId",
        "LibSignalReference/Proofs/Tag",
        "LibSignalReference/Proofs/Padding",
        "LibSignalReference/Proofs/AesNetwork",
        "LibSignalReference/Proofs/AesSubBytes",
        "LibSignalReference/Proofs/UnpadReference",
        "LibSignalReference/Proofs/Unpad",
        "LibSignalReference/Proofs/AesLayoutReference",
        "LibSignalReference/Proofs/AesLayoutPermutation",
        "LibSignalReference/Proofs/AesLayout",
        "LibSignalReference/Proofs/ShaCompactReference",
        "LibSignalReference/Proofs/ShaCompactCompression",
        "LibSignalReference/Proofs/ShaCompact",
        "LibSignalReference/Proofs/ShaCompactEquivalence",
        "LibSignalReference/Proofs/AesLinearReference",
        "LibSignalReference/Proofs/AesLinearLayout",
        "LibSignalReference/Proofs/AesLinearBits",
        "LibSignalReference/Proofs/AesLinearFormula",
        "LibSignalReference/Proofs/AesLinearProofs",
        "LibSignalReference/Proofs/AesLinear",
        "LibSignalReference/Proofs/AesShiftReference",
        "LibSignalReference/Proofs/AesShiftBits",
        "LibSignalReference/Proofs/AesShift",
        "LibSignalReference/Proofs/AesMixPhaseBits",
        "LibSignalReference/Proofs/AesMixPhaseReference",
        "LibSignalReference/Proofs/AesMixPhaseLayout",
        "LibSignalReference/Proofs/AesMixPhases",
        "LibSignalReference/Proofs/AesInverseWrite",
        "LibSignalReference",
    ]
    for module in modules:
        target = output / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), module + ".lean"],
                       cwd=HERE, env=env, check=True)
    result = subprocess.run(["lean", "Checks.lean"], cwd=HERE, env=env, check=True,
                            capture_output=True, text=True)
    print(result.stdout, end="")
    # A successful import alone does not exclude axioms in imported references.
    permitted = {"propext", "Classical.choice", "Quot.sound"}
    axioms = re.findall(r"depends on axioms: \[([^]]*)\]", result.stdout)
    expected_audits = len(re.findall(r"^#print axioms ", (HERE / "Checks.lean").read_text(), re.M))
    if len(axioms) != expected_audits:
        raise ValueError("the theorem axiom audit did not produce all expected results")
    for entries in axioms:
        unexpected = {x.strip() for x in entries.split(",") if x.strip()} - permitted
        if unexpected:
            raise ValueError(f"unexpected proof assumptions: {sorted(unexpected)}")
    report = {"checked_at_utc": datetime.now(timezone.utc).isoformat(),
              "checked_source": "pinned libsignal and locked dalek/SHA2 dependencies",
              "key_reference_profile": "Extraction/key_accessors.json",
              "clamp_reference_profile": "Extraction/clamp.json",
              "sha256_round_reference_profile": "Extraction/sha256_round.json",
              "service_id_reference_profile": "Extraction/service_id_encode.json",
              "service_id_kind_reference_profile": "Extraction/service_id_encode.json",
              "message_type_reference_profile": "Extraction/message_type.json",
              "padding_reference_profile": "Extraction/pkcs7_pad_selected.json",
              "aes_sub_bytes_reference_profile": "Extraction/aes_sub_bytes.json",
              "sha_compact_reference_profile": "Extraction/sha256_compact_reviewed.json",
              "sha_compact_trusted_metadata_review": "Extraction/sha256-compact-metadata/review.json",
              "aes_layout_reference_profile": "Extraction/aes_layout.json",
              "aes_mix_columns_0_reference_profile": "Extraction/aes_mix_columns_0.json",
              "aes_shift_rows_reference_profile": "Extraction/aes_shift_rows.json",
              "aes_mix_phases_reference_profile": "Extraction/aes_mix_phases.json",
              "aes_inverse_write_reference_profile": "Extraction/aes_inverse_write.json",
              "aes_inverse_write_trusted_selection": "Extraction/aes-inverse-write-selection/review.json",
              "unpadding_reference_profile": "Extraction/pkcs7_unpad_selected.json",
              "unpadding_metadata_and_model_review": "Extraction/unpad-review.json",
              "full_mir_unpadding_provenance": "Extraction/unpad-sysroot-provenance.json",
              "discarded_panic_format_metadata": "core::fmt::Arguments and PKCS7 core::fmt::{impl}::from_str; no computational reference stubs",
              "sha256_round_std_models": PROFILES["sha256_round"]["modeled_std_functions"],
              "baf_hkdf_spec_equality_is_not_rust_reference_refinement": True,
              "accepted_custom_axioms": [], "allowed_foundational_axioms": sorted(permitted),
              "checked_axiom_reports": len(axioms),
              "checked_theorems": re.findall(r"'([^']+)' depends on axioms:", result.stdout),
              "root_lean_crypto_refinement_is_not_rustcrypto_refinement": True,
              "root_sha_compression_rustcrypto_equivalence_established": True,
              "root_sha_digest_buffering_hmac_refinement_established": False,
              "cbc_lowering_checked": True,
              "cbc_rustcrypto_composition_refinement_established": False,
              "standard_model_sources_sha256": {name: digest(backend / name) for name in model_files},
              "proof_sources_sha256": {str(p.relative_to(HERE)): digest(p)
                                       for p in sorted((HERE / "LibSignalReference").rglob("*.lean"))},
              "root_signal_sources_sha256": {str(p.relative_to(ROOT)): digest(p)
                                             for p in sorted((ROOT / "TlsMpc/Signal").glob("*.lean"))}}
    (HERE / "Extraction/proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Checked actual Rust accessors, clamping, identifiers/tags, PKCS7 padding/unpadding, restored AES S-box, all forward AES linear phases, SHA compression including the root implementation, and numeric bridges.")
    print("Full Signal protocol and RustCrypto derivation refinement are not established by these checks.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Signal proof check failed: {error}", file=sys.stderr)
        raise SystemExit(1)
