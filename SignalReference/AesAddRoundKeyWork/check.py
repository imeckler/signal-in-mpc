#!/usr/bin/env python3
"""Audit the actual core XOR-assign leaf; reject whole-round-key proof claims."""

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
from AesAddRoundKeyWork.select_xor import select
from backend_adapter import aig

MODULES = ["AesAddRoundKeyWork/Generated/XorAssign/Types",
           "AesAddRoundKeyWork/Generated/XorAssign/Funs",
           "AesAddRoundKeyWork/Circuit", "AesAddRoundKeyWork/Proofs"]
MODELS = ["Aeneas/Std/Scalar/Core.lean", "Aeneas/Std/Scalar/Bitwise.lean", "Aeneas/Std/Primitives.lean"]
ROOT_SOURCES = ["TlsMpc/AigExport.lean", "TlsMpc/BvConstruct.lean", "backend_adapter/aig.py"]
RUST_SOURCES = ["core/src/internal_macros.rs", "core/src/ops/bit.rs"]
RUST_ARCHIVE_SHA = "f8b984f0f9a4f542a73c85be1bc379fe88455c5e96f70bd19052511d0195f5e4"
MIRI_ARCHIVE_SHA = "912904e20c37ffe461264ac7c005bc56b778d7a58fcbb29deed3445912283d21"


def audit_selection():
    original = HERE / "Artifacts/IncludeXor/add_round_key.llbc"
    selected = HERE / "Artifacts/XorAssign/selected.llbc"
    report_path = HERE / "Artifacts/XorAssign/review.json"
    report = json.loads(report_path.read_text())
    expected, changes = select(json.loads(original.read_text()))
    if json.loads(selected.read_text()) != expected:
        raise ValueError("Selected actual helper graph differs")
    changes_path = REFERENCE / report["changes_file"]
    if json.loads(changes_path.read_text()) != changes or digest(changes_path) != report["changes_sha256"]:
        raise ValueError("Exact reversible selection diff differs")
    if digest(HERE / "select_xor.py") != report["script_sha256"]:
        raise ValueError("Selection script changed")
    current = inventory(selected)
    if (current["has_errors"] or current["body_kinds"] != {"Structured": 2} or
            current["external_functions"] or current["external_or_union_types"] or
            current["explicit_exclusions"] or current["explicit_opaque_patterns"] or
            current["counts"] != {"type_decls": 0, "fun_decls": 2, "global_decls": 0,
                                  "trait_decls": 1, "trait_impls": 2, "ordered_decls": 2} or
            report["source_patches"] or report["computational_bodies_modified"] or report["aeneas_exit_code"]):
        raise ValueError("Unexpected selected helper dependencies")
    generated = HERE / "Generated/XorAssign"
    if sorted(path.name for path in generated.glob("*.lean")) != ["Funs.lean", "Types.lean"]:
        raise ValueError("Unexpected external template or generated file")
    if re.findall(r"^def ([^\s]+)", (generated / "Funs.lean").read_text(), re.M) != [
            "U64.Insts.CoreOpsBitBitXorAssignU64.bitxor_assign"]:
        raise ValueError("Generated function inventory differs")
    if re.search(r"^\s*(?:opaque|structure|inductive|def)\b", (generated / "Types.lean").read_text(), re.M):
        raise ValueError("Expected no generated types")
    for name, expected_hash in report["generated_files"].items():
        if digest(REFERENCE / name) != expected_hash:
            raise ValueError(f"Generated reference changed: {name}")
    independent_path = REFERENCE / "AesKeyScheduleWork/xor-assign-selection-review.json"
    independent = json.loads(independent_path.read_text()) if independent_path.exists() else None
    if independent is not None:
        if (not independent["independent_review"] or not independent["retained_declarations_identical"] or
                not independent["closed_computational_dependencies"] or
                independent["exact_reversible_declaration_changes"] != len(changes) or
                independent["retained_function_ids"] != [6, 121] or
                independent["generated_endpoint_function_id"] != 121 or
                independent["shared_wrapper_generated"] or independent["whole_add_round_key_reference_complete"] or
                independent["selected_llbc_sha256"] != digest(selected) or
                independent["selection_script_sha256"] != digest(HERE / "select_xor.py")):
            raise ValueError("Independent leaf-selection review does not match this selection")
    return {"selection_report_file": str(report_path.relative_to(REFERENCE)),
            "selection_report_sha256": digest(report_path), "selected_llbc_sha256": digest(selected),
            "original_llbc_sha256": digest(original), "source_fingerprint": report["input_fingerprint"],
            "selection_script_sha256": digest(HERE / "select_xor.py"),
            "selected_declarations_unchanged": True, "selection_reversible_changes": len(changes),
            "additional_trusted_declaration_selection": True,
            "selection_correctness_mechanized": False,
            "independent_review_file": str(independent_path.relative_to(REFERENCE)) if independent else None,
            "independent_review_sha256": digest(independent_path) if independent else None,
            "independent_review_present": independent is not None,
            "generated_value_function_only": True,
            "shared_argument_forwarder_refinement_claimed": False}


def audit_sysroot():
    provenance_path = REFERENCE / "PaddingWork/Unpad/sysroot-provenance.json"
    provenance = json.loads(provenance_path.read_text())
    rust_archive = ROOT / ".deps/rust-src-nightly-2026-08-18.tar.xz"
    miri_archive = REFERENCE / "PaddingWork/Unpad/miri-nightly-2026-08-18.tar.xz"
    if (provenance["rust_source_archive_sha256"] != RUST_ARCHIVE_SHA or
            provenance["miri_archive_sha256"] != MIRI_ARCHIVE_SHA or
            digest(rust_archive) != RUST_ARCHIVE_SHA or digest(miri_archive) != MIRI_ARCHIVE_SHA):
        raise ValueError("Full-MIR Rust/Miri archives differ")
    for name, expected_hash in provenance["sysroot_artifact_sha256"].items():
        if digest(ROOT / provenance["sysroot_directory"] / name) != expected_hash:
            raise ValueError(f"Full-MIR sysroot differs: {name}")
    source_dir = ROOT / provenance["source_directory"]
    for name, expected_hash in provenance["sysroot_source_files_sha256"].items():
        if digest(source_dir / name) != expected_hash:
            raise ValueError(f"Full-MIR build source differs: {name}")
    with tarfile.open(rust_archive) as bundle:
        members = bundle.getnames()
        for name in [*provenance["sysroot_source_files_sha256"], *RUST_SOURCES]:
            member = next(path for path in members if path.endswith("/library/" + name))
            if bundle.extractfile(member).read() != (source_dir / name).read_bytes():
                raise ValueError(f"Rust source differs from official archive: {name}")
    return {"provenance_file": str(provenance_path.relative_to(REFERENCE)),
            "provenance_sha256": digest(provenance_path),
            "rust_core_source_sha256": {name: digest(source_dir / name) for name in RUST_SOURCES},
            "rust_commit": provenance["rust_commit"], "source_patches": []}


def check_image(image):
    aig.validate(image)
    if image["input_bits"] != 128 or image["input_widths"] != [64, 64] or len(image["outputs"]) != 64:
        raise ValueError("Unexpected u64 XOR ABI")
    stats = aig.statistics(image)
    if stats["executed_and_gates"] != 0 or stats["executed_xor_gates"] != 64:
        raise ValueError("Expected exactly64 XOR operations and no AND operations")
    expected = [(1 << bit) ^ (1 << (64 + bit)) for bit in range(64)]
    for optimize in (False, True):
        if aig.execute(image, [1 << bit for bit in range(128)], 0, (1 << 128) - 1, optimize=optimize) != expected:
            raise ValueError("Native circuit basis results differ from XOR")
        if any(aig.execute(image, [0] * 128, 0, 1, optimize=optimize)):
            raise ValueError("Native circuit zero results differ")
    return {"nodes": len(image["nodes"]), **stats, "output_bits": 64,
            "zero_and_all_128_basis_vectors_checked": True, "raw_and_optimized_adapter_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, required=True)
    args = parser.parse_args()
    check_sources()
    reference = audit_selection()
    sysroot = audit_sysroot()
    backend = (REFERENCE / PINS["aeneas"]["directory"] / "backends/lean").resolve()
    archive = ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz"
    if digest(archive) != PINS["aeneas"]["macos_aarch64_archive_sha256"]:
        raise ValueError("Aeneas archive differs")
    with tarfile.open(archive) as bundle:
        for name in MODELS:
            if bundle.extractfile("backends/lean/" + name).read() != (backend / name).read_bytes():
                raise ValueError(f"Aeneas scalar model changed: {name}")
    for path in (ROOT / "lean-toolchain", REFERENCE / "lean-toolchain", backend / "lean-toolchain"):
        if path.read_text().strip() != PINS["aeneas"]["lean_toolchain"]:
            raise ValueError(f"Lean version differs: {path}")
    package_paths = []
    for package in json.loads((backend / "lake-manifest.json").read_text())["packages"]:
        directory = args.packages_dir / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Package revision differs: {directory}")
        path = directory / ".lake/build/lib/lean"
        if path.is_dir():
            package_paths.append(path)
    proof_paths = [REFERENCE / (module + ".lean") for module in MODULES]
    for path in proof_paths:
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", path.read_text()):
            raise ValueError(f"Incomplete or externally checked proof: {path}")
    root_hashes = {name: digest(ROOT / name) for name in ROOT_SOURCES}
    subprocess.run(["lake", "build", "TlsMpc.AigExport", "TlsMpc.BvConstruct"], cwd=ROOT, check=True)
    output = REFERENCE / ".lake/build/lib/lean"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in
        [output, ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean", *package_paths])
    for module in MODULES:
        target = output / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), module + ".lean"], cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "AesAddRoundKeyWork/Checks.lean"], cwd=REFERENCE, env=env,
                            check=True, text=True, capture_output=True)
    print(result.stdout, end="")
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    expected_count = len(re.findall(r"^#print axioms ", (HERE / "Checks.lean").read_text(), re.M))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if len(reports) != expected_count:
        raise ValueError("Missing theorem assumption reports")
    for name, axioms in reports:
        if {value.strip() for value in axioms.split(",") if value.strip()} - allowed:
            raise ValueError(f"Unexpected assumptions in {name}: {axioms}")
    image = json.loads(subprocess.check_output(["lean", "--run", "AesAddRoundKeyWork/Export.lean"],
                                               cwd=REFERENCE, env=env, text=True))
    artifact_report = check_image(image)
    artifact_path = HERE / "Artifacts/aes-core-u64-xor-assign.json"
    artifact_path.write_text(json.dumps(image, separators=(",", ":")) + "\n")
    # Reproduce the material boundary; failure is not converted into a proof.
    blocked = subprocess.run(["lean", "AesAddRoundKeyWork/Generated/IncludeXor/Funs.lean"],
                             cwd=REFERENCE, env=env, text=True, capture_output=True)
    blocked_log = HERE / "Artifacts/IncludeXor/lean-check.log"
    blocked_log.write_text(blocked.stdout + blocked.stderr)
    if blocked.returncode == 0 or "IteratorIterMut.next" not in blocked.stdout or "Type mismatch" not in blocked.stdout:
        raise ValueError("Expected mutable iterator model boundary changed; investigate")
    if root_hashes != {name: digest(ROOT / name) for name in ROOT_SOURCES}:
        raise ValueError("Shared compiler source changed during checks")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "accepted_reference": reference["independent_review_present"], "canonical_reference_integrated": False,
        "reference": reference, "sysroot": sysroot,
        "verified_operation": "Actual Rust core value-taking u64 BitXorAssign implementation, called transitively by aes0.9.1 add_round_key",
        "domain": "All two secret64-bit operands; exact successful secret64-bit write-back",
        "whole_add_round_key_reference_complete": False,
        "shared_argument_forwarder_refinement_claimed": False,
        "whole_aes_rustcrypto_equivalence_established": False,
        "mutable_iterator_blocker": {
            "reproduced_lean_exit_code": blocked.returncode,
            "log": str(blocked_log.relative_to(REFERENCE)), "log_sha256": digest(blocked_log),
            "detail": "IterMut.next has a borrow write-back continuation; pinned generic Iterator.next and Zip helpers lack that component",
            "custom_mutable_zip_model_introduced": False,
            "original_rust_loop_replaced": False},
        "source_patches": [], "custom_cryptographic_models": [], "custom_axioms": [],
        "computational_standard_models": ["UScalar bitwise XOR", "Result"],
        "allowed_foundational_axioms": sorted(allowed), "checked_theorems": expected_count,
        "proof_sources_sha256": {str(path.relative_to(REFERENCE)): digest(path) for path in proof_paths},
        "standard_model_sources_sha256": {name: digest(backend / name) for name in MODELS},
        "root_semantics_sha256": root_hashes, "export_source_sha256": digest(HERE / "Export.lean"),
        "audit_script_sha256": digest(Path(__file__)), "extraction_script_sha256": digest(HERE / "extract.py"),
        "artifact": {"artifact_sha256": digest(artifact_path), **artifact_report},
        "native_mpc_execution_tested": False,
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {expected_count} XOR leaf theorems and numeric artifact; original round-key iterator boundary reproduced.")


if __name__ == "__main__":
    main()
