#!/usr/bin/env python3
"""Check actual inverse-layout writer selection, Lean proof, and numeric wiring."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
sys.path.insert(0, str(ROOT))
from extract import PINS, check_sources, digest, inventory
from AesInverseLayoutWork.select_write import select
from backend_adapter import aig

MODULES = ["LibSignalReference/Generated/AesInverseWrite/Types",
           "LibSignalReference/Generated/AesInverseWrite/Funs",
           "LibSignalReference/Proofs/AesInverseWrite"]
MODEL_FILES = ["Aeneas/Std/Slice.lean", "Aeneas/Std/Scalar/Core.lean",
               "Aeneas/Std/Scalar/Bitwise.lean", "Aeneas/Std/Scalar/Casts.lean",
               "Aeneas/Std/Primitives.lean"]
ROOT_FILES = ["TlsMpc/ByteCircuit.lean", "TlsMpc/AigExport.lean",
              "TlsMpc/BvConstruct.lean", "TlsMpc/Signal/AesLayoutNetwork.lean", "TlsMpc/Signal/AesInverseWrite.lean",
              "backend_adapter/aig.py"]
REFERENCE_DEPENDENCIES = ["LibSignalReference/Proofs/AesLayoutReference.lean",
                        "LibSignalReference/Generated/AesLayout/Funs.lean",
                        "LibSignalReference/Generated/AesLayout/Types.lean"]


def audit_selection():
    original = HERE / "Artifacts/InvBitsliceScoped/aes_inverse_layout.llbc"
    selected = REFERENCE / "Extraction/libsignal_aes_inverse_write.llbc"
    report_path = REFERENCE / "Extraction/aes-inverse-write-selection/review.json"
    recorded = json.loads(report_path.read_text())
    expected, changes = select(json.loads(original.read_text()))
    actual = json.loads(selected.read_text())
    if actual != expected:
        raise ValueError("Selected writer differs from closed original declaration")
    change_path = REFERENCE / recorded["reversible_changes_file"]
    if digest(change_path) != recorded["reversible_changes_sha256"] or json.loads(change_path.read_text()) != changes:
        raise ValueError("Recorded exact selection changes differ")
    independent_path = REFERENCE / recorded["independent_review_file"]
    independent = json.loads(independent_path.read_text())
    current = inventory(selected)
    if (current["has_errors"] or current["body_kinds"] != {"Structured": 1} or
            current["external_functions"] or current["external_or_union_types"] or
            current["counts"] != {"type_decls": 0, "fun_decls": 1, "global_decls": 0,
                                  "trait_decls": 0, "trait_impls": 0, "ordered_decls": 1} or
            current["explicit_exclusions"] != ["hybrid_array::traits::ArraySize"] or
            current["explicit_opaque_patterns"] or recorded["source_patches"] or
            recorded["aeneas_exit_code"]):
        raise ValueError("Selected writer has unexpected graph dependencies")
    for key, path in (("original_llbc_sha256", original), ("selected_llbc_sha256", selected)):
        if digest(path) != recorded[key]:
            raise ValueError("LLBC hash differs from the selected replay; select() pins the independently reviewed semantic graph")
    if not independent["closed_builtin_only_declaration"] or independent["exact_reversible_declaration_changes"] != len(changes):
        raise ValueError("Missing independent closed-selection review")
    if digest(HERE / "select_write.py") != recorded["selection_script_sha256"]:
        raise ValueError("Selection script differs from recorded run")
    generated = REFERENCE / "LibSignalReference/Generated/AesInverseWrite"
    if sorted(p.name for p in generated.glob("*.lean")) != ["Funs.lean", "Types.lean"]:
        raise ValueError("Unexpected generated file or external template")
    if re.findall(r"^def ([^\s]+)", (generated / "Funs.lean").read_text(), re.M) != [
            "soft.fixslice.inv_bitslice.write_reordered"]:
        raise ValueError("Unexpected generated function inventory")
    if re.search(r"^\s*(?:opaque|structure|inductive|def)\b", (generated / "Types.lean").read_text(), re.M):
        raise ValueError("Expected no generated types")
    for name, expected_hash in recorded["generated_files"].items():
        if digest(REFERENCE / name) != expected_hash:
            raise ValueError(f"Generated reference changed: {name}")
    return {"review_file": str(report_path.relative_to(REFERENCE)),
            "review_sha256": digest(report_path),
            "independent_review_file": str(independent_path.relative_to(REFERENCE)),
            "independent_review_sha256": digest(independent_path),
            "original_llbc_sha256": digest(original), "selected_llbc_sha256": digest(selected),
            "retained_actual_function_declaration_identical": True,
            "retained_signature_and_body_closed_builtin_only": True,
            "reversible_declaration_changes": len(changes),
            "generated_files": recorded["generated_files"],
            "selection_correctness_mechanized": False,
            "additional_trusted_declaration_selection": True,
            "selection_script_sha256": digest(HERE / "select_write.py")}


def check_image(image):
    aig.validate(image)
    if image["input_bits"] != 160 or image["input_widths"] != [64] + [8] * 12 or len(image["outputs"]) != 96:
        raise ValueError("Unexpected writer ABI")
    stats = aig.statistics(image)
    if stats["executed_and_gates"] or stats["executed_xor_gates"]:
        raise ValueError("Expected pure bit selection")
    column_offsets = [0, 16, 32, 48, None, None, None, None, 8, 24, 40, 56]
    expected = []
    for byte, offset in enumerate(column_offsets):
        for network_bit in range(8):
            source = (64 + byte * 8 + network_bit) if offset is None else (56 - offset + network_bit)
            expected.append(1 << source)
    for optimize in (False, True):
        result = aig.execute(image, [1 << bit for bit in range(160)], 0, (1 << 160) - 1, optimize=optimize)
        if result != expected or any(aig.execute(image, [0] * 160, 0, 1, optimize=optimize)):
            raise ValueError("Native artifact disagrees with independent actual byte-write order")
    return {"nodes": len(image["nodes"]), **stats, "outputs": 96,
            "zero_and_all_160_basis_vectors_checked": True,
            "raw_and_optimized_adapter_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, required=True)
    args = parser.parse_args()
    check_sources()
    reference = audit_selection()
    backend = (REFERENCE / PINS["aeneas"]["directory"] / "backends/lean").resolve()
    archive = ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz"
    if digest(archive) != PINS["aeneas"]["macos_aarch64_archive_sha256"]:
        raise ValueError("Aeneas archive differs")
    with tarfile.open(archive) as bundle:
        for name in MODEL_FILES:
            if bundle.extractfile("backends/lean/" + name).read() != (backend / name).read_bytes():
                raise ValueError(f"Aeneas standard model changed: {name}")
    for path in (ROOT / "lean-toolchain", REFERENCE / "lean-toolchain", backend / "lean-toolchain"):
        if path.read_text().strip() != PINS["aeneas"]["lean_toolchain"]:
            raise ValueError(f"Lean toolchain differs: {path}")
    canonical_report = json.loads((REFERENCE / "Extraction/proof-check.json").read_text())
    dependency_hashes = {name: canonical_report["proof_sources_sha256"][name] for name in REFERENCE_DEPENDENCIES}
    if canonical_report["accepted_custom_axioms"]:
        raise ValueError("Canonical dependency audit uses custom assumptions")
    for name, expected_hash in dependency_hashes.items():
        if digest(REFERENCE / name) != expected_hash:
            raise ValueError(f"Canonical layout dependency changed: {name}")
    proof_paths = [REFERENCE / (module + ".lean") for module in MODULES]
    for path in proof_paths:
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", path.read_text()):
            raise ValueError(f"Incomplete or externally checked proof: {path}")
    package_paths = []
    for package in json.loads((backend / "lake-manifest.json").read_text())["packages"]:
        directory = args.packages_dir / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Cached package revision differs: {directory}")
        path = directory / ".lake/build/lib/lean"
        if path.is_dir():
            package_paths.append(path)
    root_hashes = {name: digest(ROOT / name) for name in ROOT_FILES}
    subprocess.run(["lake", "build", "TlsMpc.Signal.AesInverseWrite"], cwd=ROOT, check=True)
    output = REFERENCE / ".lake/build/lib/lean"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in
        [output, ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean", *package_paths])
    for module in MODULES:
        target = output / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), module + ".lean"], cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "AesInverseLayoutWork/Checks.lean"], cwd=REFERENCE, env=env,
                            check=True, text=True, capture_output=True)
    print(result.stdout, end="")
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    expected_count = len(re.findall(r"^#print axioms ", (HERE / "Checks.lean").read_text(), re.M))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if len(reports) != expected_count:
        raise ValueError("Missing theorem assumption reports")
    for name, names in reports:
        if {x.strip() for x in names.split(",") if x.strip()} - allowed:
            raise ValueError(f"Unexpected proof assumptions in {name}: {names}")
    exported = subprocess.check_output(["lean", "--run", "AesInverseLayoutWork/Export.lean"],
                                       cwd=REFERENCE, env=env, text=True)
    image = json.loads(exported)
    artifact_checks = check_image(image)
    artifact_path = HERE / "Artifacts/aes-inverse-write-reordered.json"
    artifact_path.write_text(json.dumps(image, separators=(",", ":")) + "\n")
    if root_hashes != {name: digest(ROOT / name) for name in ROOT_FILES} or any(
            digest(REFERENCE / name) != expected_hash for name, expected_hash in dependency_hashes.items()):
        raise ValueError("Shared source changed during the audit")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(), "accepted_reference": True, "canonical_reference_integrated": True,
        "canonical_reference_integrated": False,
        "reference": reference,
        "actual_locked_source": "aes 0.9.1 src/soft/fixslice64.rs:1317-1326; libsignal 0.106.1 Cargo.lock",
        "numeric_circuit_bridge_domain": "Every secret u64 column and every secret 12-byte initial slice; result is the exact successful 12-byte write-back",
        "actual_caller_shapes": "Both inv_bitslice calls use length12: block[0..12] and block[4..16]",
        "computational_standard_models": ["Slice.update", "UScalar.cast", "UScalar checked right shift", "Result and lift"],
        "explicit_exclusions": ["hybrid_array::traits::ArraySize: unused by the selected closed writer"],
        "source_patches": [], "custom_cryptographic_models": [], "custom_axioms": [],
        "allowed_foundational_axioms": sorted(allowed), "checked_theorems": expected_count,
        "proof_sources_sha256": {str(path.relative_to(REFERENCE)): digest(path) for path in proof_paths},
        "canonical_dependency_sources_sha256": dependency_hashes,
        "canonical_dependency_audit_utc": canonical_report["checked_at_utc"],
        "root_semantics_sha256": root_hashes,
        "standard_model_sources_sha256": {name: digest(backend / name) for name in MODEL_FILES},
        "unverified_export_source_sha256": digest(HERE / "Export.lean"),
        "audit_script_sha256": digest(Path(__file__)), "extraction_script_sha256": digest(HERE / "extract_inverse.py"),
        "artifact": {"artifact_sha256": digest(artifact_path), **artifact_checks},
        "native_mpc_execution_tested": False,
        "full_inv_bitslice_refinement_complete": False,
        "remaining_wrapper_obligations": ["hybrid-array allocation/default/index implementations",
            "subrange borrow and write-back composition", "inverse transpose and block relabeling composition"],
        "whole_aes_rustcrypto_equivalence_established": False,
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {expected_count} actual AES inverse-writer theorems; numeric artifact has zero AND and XOR gates.")


if __name__ == "__main__":
    main()
