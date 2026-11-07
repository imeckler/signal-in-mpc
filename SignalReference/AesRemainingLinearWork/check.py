#!/usr/bin/env python3
"""Audit the actual three remaining RustCrypto MixColumns phases and circuits."""

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
from backend_adapter import aig

MODULES = ["LibSignalReference/Generated/AesMixPhases/Types", "LibSignalReference/Generated/AesMixPhases/Funs",
           *["LibSignalReference/Proofs/" + name for name in (
               "AesMixPhaseBits", "AesMixPhaseReference", "AesMixPhaseLayout", "AesMixPhases")]]
GENERATED_DEFS = ["ror_distance", "ror", "rotate_rows_and_columns_2_2",
                  "rotate_rows_and_columns_1_1", "mix_columns_1",
                  "rotate_rows_and_columns_1_2", "rotate_rows_2", "mix_columns_2",
                  "rotate_rows_and_columns_1_3", "mix_columns_3"]
MODEL_FILES = ["Aeneas/Std/Array/Array.lean", "Aeneas/Std/Array/Core.lean",
               "Aeneas/Std/Scalar/Core.lean", "Aeneas/Std/Scalar/Bitwise.lean",
               "Aeneas/Std/Scalar/Rotate.lean", "Aeneas/Std/Scalar/Ops/Add.lean",
               "Aeneas/Std/Primitives.lean"]
ROOT_FILES = ["TlsMpc/Aes.lean", "TlsMpc/AesSbox.lean", "TlsMpc/Signal/AesMix.lean",
              "TlsMpc/Signal/AesShift.lean", "TlsMpc/Signal/AesLayoutNetwork.lean",
              "TlsMpc/Signal/AesLayout.lean", "TlsMpc/Signal/AesMixPhases.lean", "TlsMpc/ByteCircuit.lean",
              "TlsMpc/AigExport.lean", "TlsMpc/BvConstruct.lean", "backend_adapter/aig.py"]


def audit_reference():
    record_path = REFERENCE / "Extraction/aes_mix_phases.json"
    recorded = json.loads(record_path.read_text())
    current = inventory(REFERENCE / "Extraction/libsignal_aes_mix_phases.llbc")
    if (current["has_errors"] or recorded["charon_exit_code"] or recorded["aeneas_exit_code"] or
            current["body_kinds"] != {"Structured": 10, "Opaque": 1} or
            [x["name"] for x in current["external_functions"]] != ["core::num::{impl}::rotate_right"] or
            current["external_or_union_types"] or current["explicit_exclusions"] or
            current["explicit_opaque_patterns"] or recorded.get("source_patches", []) or
            current["llbc_sha256"] != recorded["llbc_sha256"] or
            recorded["rustflags"] != '--cfg aes_backend="soft"'):
        raise ValueError("MixColumns phases differ from the reviewed extraction")
    if current["counts"] != {"type_decls": 0, "fun_decls": 11, "global_decls": 0,
                             "trait_decls": 0, "trait_impls": 0, "ordered_decls": 11}:
        raise ValueError("Unexpected extraction metadata or dependencies")
    for name, expected in recorded["generated_files"].items():
        if digest(REFERENCE / name) != expected:
            raise ValueError(f"Generated reference changed: {name}")
    generated = REFERENCE / "LibSignalReference/Generated/AesMixPhases"
    if sorted(p.name for p in generated.glob("*.lean")) != ["Funs.lean", "Types.lean"]:
        raise ValueError("Unexpected generated definitions or external templates")
    if re.findall(r"^def ([^\s]+)", (generated / "Funs.lean").read_text(), re.M) != [
            "soft.fixslice." + name for name in GENERATED_DEFS]:
        raise ValueError("Generated function inventory differs")
    if re.search(r"^\s*(?:opaque|structure|inductive|def)\b", (generated / "Types.lean").read_text(), re.M):
        raise ValueError("Expected no generated types")
    return {"inventory": str(record_path.relative_to(REFERENCE)),
            "llbc_sha256": current["llbc_sha256"], "generated_files": recorded["generated_files"],
            "standard_library_llbc_functions": ["core::num::{impl}::rotate_right"],
            "discarded_metadata_types": [], "discarded_metadata_functions": []}


def expected_basis(phase):
    def byte(block, row, column):
        return [1 << (block * 128 + (column * 4 + row) * 8 + 7 - bit) for bit in range(8)]
    def xtime(a):
        return [a[7], a[0] ^ a[7], a[1], a[2] ^ a[7], a[3] ^ a[7], a[4], a[5], a[6]]
    expected = []
    for position in range(512):
        byte_position, network_bit = divmod(position, 8)
        plane, offset = divmod(byte_position, 8)
        lane = 8 * offset + 7 - network_bit
        block, row, column = lane % 4, lane // 16, lane // 4 % 4
        a, b, c, d = [byte(block, (row + n) % 4, (column + phase * n) % 4) for n in range(4)]
        expected.append(xtime(a)[plane] ^ xtime(b)[plane] ^ b[plane] ^ c[plane] ^ d[plane])
    return expected


def check_image(image, phase):
    aig.validate(image)
    if image["input_bits"] != 512 or image["input_widths"] != [8] * 64 or len(image["outputs"]) != 512:
        raise ValueError("Unexpected MixColumns phase ABI")
    stats = aig.statistics(image)
    if stats["executed_and_gates"]:
        raise ValueError("Expected only public wiring and XOR operations")
    expected = expected_basis(phase)
    for optimize in (False, True):
        got = aig.execute(image, [1 << index for index in range(512)], 0, (1 << 512) - 1, optimize=optimize)
        if got != expected or any(aig.execute(image, [0] * 512, 0, 1, optimize=optimize)):
            raise ValueError("Native artifact disagrees with the independent phase transformation")
    return {"nodes": len(image["nodes"]), **stats, "outputs": 512,
            "zero_and_all_512_basis_vectors_checked": True, "raw_and_optimized_adapter_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, required=True)
    args = parser.parse_args()
    check_sources()
    reference = audit_reference()
    backend = (REFERENCE / PINS["aeneas"]["directory"] / "backends/lean").resolve()
    archive = ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz"
    if digest(archive) != PINS["aeneas"]["macos_aarch64_archive_sha256"]:
        raise ValueError("Aeneas archive hash differs")
    with tarfile.open(archive) as bundle:
        for name in MODEL_FILES:
            if bundle.extractfile("backends/lean/" + name).read() != (backend / name).read_bytes():
                raise ValueError(f"Aeneas standard model changed: {name}")
    for path in (ROOT / "lean-toolchain", REFERENCE / "lean-toolchain", backend / "lean-toolchain"):
        if path.read_text().strip() != PINS["aeneas"]["lean_toolchain"]:
            raise ValueError(f"Lean toolchain differs: {path}")
    canonical_report_path = REFERENCE / "Extraction/proof-check.json"
    canonical_report = json.loads(canonical_report_path.read_text())
    canonical_hashes = {name: hash_ for name, hash_ in canonical_report["proof_sources_sha256"].items()
                        if name.startswith("LibSignalReference/Proofs/Aes") or
                        name.startswith("LibSignalReference/Generated/Aes")}
    if not canonical_hashes or canonical_report["accepted_custom_axioms"]:
        raise ValueError("Canonical AES dependency audit is unavailable")
    for name, expected in canonical_hashes.items():
        if digest(REFERENCE / name) != expected:
            raise ValueError(f"Canonical AES dependency changed since its audit: {name}")
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
    for name in ("TlsMpc/Signal/AesMix.lean", "TlsMpc/Signal/AesShift.lean",
                 "TlsMpc/Signal/AesLayout.lean", "TlsMpc/Signal/AesLayoutNetwork.lean"):
        if canonical_report["root_signal_sources_sha256"][name] != root_hashes[name]:
            raise ValueError(f"Root dependency changed since its canonical audit: {name}")
    subprocess.run(["lake", "build", "TlsMpc.Signal.AesMixPhases"], cwd=ROOT, check=True)
    output = REFERENCE / ".lake/build/lib/lean"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in
        [output, ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean", *package_paths])
    for module in MODULES:
        target = output / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), module + ".lean"],
                       cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "AesRemainingLinearWork/Checks.lean"], cwd=REFERENCE, env=env,
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
    exported = subprocess.check_output(["lean", "--run", "AesRemainingLinearWork/Export.lean"],
                                       cwd=REFERENCE, env=env, text=True)
    images = json.loads(exported)
    if [image["name"] for image in images] != [f"aes-mix-columns-{n}" for n in (1, 2, 3)]:
        raise ValueError("Unexpected native export inventory")
    artifact_reports = {}
    for phase, image in enumerate(images, 1):
        checks = check_image(image, phase)
        artifact_path = HERE / "Artifacts" / (image["name"] + ".json")
        artifact_path.write_text(json.dumps(image, separators=(",", ":")) + "\n")
        artifact_reports[image["name"]] = {"artifact_sha256": digest(artifact_path), **checks}
    if root_hashes != {name: digest(ROOT / name) for name in ROOT_FILES} or any(
            digest(REFERENCE / name) != expected for name, expected in canonical_hashes.items()):
        raise ValueError("Shared proof/compiler sources changed during the audit")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(), "accepted_reference": True, "canonical_reference_integrated": True,
        "reference": reference, "actual_locked_source": "aes 0.9.1 src/soft/fixslice64.rs; libsignal 0.106.1 Cargo.lock",
        "numeric_circuit_bridge_domain": "All 4 x 16 secret bytes in canonical ordinary bitplane layout; fixed 8-word state; public phase 1,2,3; output eight little-endian u64 bitplanes",
        "phase_equation": "M_k = S^(-k) M_0 S^k, with S the existing root byte ShiftRows",
        "round_phase_invariant_proved": True, "shift_rows_four_cycle_proved": True,
        "computational_standard_models": ["Array.index_usize/update", "UScalar checked shifts/addition, XOR, AND, OR, rotate_right", "Result and lift"],
        "explicit_exclusions": [], "source_patches": [], "custom_cryptographic_models": [], "custom_axioms": [],
        "allowed_foundational_axioms": sorted(allowed), "checked_theorems": expected_count,
        "proof_sources_sha256": {str(p.relative_to(REFERENCE)): digest(p) for p in proof_paths},
        "canonical_aes_dependency_sources_sha256": canonical_hashes,
        "canonical_dependency_audit_utc": canonical_report["checked_at_utc"],
        "canonical_dependencies_reused_from_existing_audit": True,
        "root_semantics_sha256": root_hashes,
        "standard_model_sources_sha256": {p: digest(backend / p) for p in MODEL_FILES},
        "unverified_export_source_sha256": digest(HERE / "Export.lean"),
        "audit_script_sha256": digest(Path(__file__)), "extraction_script_sha256": digest(REFERENCE / "extract.py"),
        "artifacts": artifact_reports, "native_mpc_execution_tested": False,
        "aes256_key_schedule_candidate": "Artifacts/Aes256KeySchedule/inventory.json",
        "aes256_key_schedule_candidate_accepted": False,
        "whole_aes_rustcrypto_equivalence_established": False,
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {expected_count} AES phase theorems and three numeric artifacts; zero executed AND gates.")


if __name__ == "__main__":
    main()
