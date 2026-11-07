#!/usr/bin/env python3
"""Audit actual RustCrypto bitslicing extraction, proofs, and wiring artifact."""

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
from extract import PINS, check_sources, digest, inventory

STD_FUNCTIONS = [
    "core::slice::{impl}::len", "core::slice::index::{impl}::index",
    "core::convert::num::{impl}::from", "core::slice::index::{impl}::get",
    "core::slice::index::{impl}::get_mut", "core::slice::index::{impl}::get_unchecked",
    "core::slice::index::{impl}::get_unchecked_mut", "core::slice::index::{impl}::index",
    "core::slice::index::{impl}::index_mut",
]
MODEL_FILES = [
    "Aeneas/Std/Slice.lean", "Aeneas/Std/SliceDef.lean", "Aeneas/Data/List/List.lean",
    "Aeneas/Std/Scalar/Core.lean",
    "Aeneas/Std/Scalar/Bitwise.lean", "Aeneas/Std/Scalar/CoreConvertNum.lean",
    "Aeneas/Std/Primitives.lean",
]
MODULES = ["Generated/Bitslice/Types", "Generated/Bitslice/Funs", "Network", "Reference",
           "Permutation", "Circuit", "Bridge"]
ROOT_FILES = ["TlsMpc/AesSbox.lean", "TlsMpc/ByteCircuit.lean", "TlsMpc/AigExport.lean",
              "TlsMpc/BvConstruct.lean"]


def check_wires(image):
    if image["input_bits"] != 512 or image["input_widths"] != [8] * 64 or len(image["outputs"]) != 512:
        raise ValueError("Unexpected bitslice ABI")
    nodes = image["nodes"]
    if any(node[0] == 2 for node in nodes):
        raise ValueError("Expected a wiring-only circuit, found an AND gate")
    if any(node != [0] and not (len(node) == 4 and node[0] == 1 and node[2] == 8) for node in nodes):
        raise ValueError("Unexpected node encoding")
    seen = set()
    for position, (node_id, inverted) in enumerate(image["outputs"]):
        byte_position, network_bit = divmod(position, 8)
        plane, offset = divmod(byte_position, 8)
        lane = 8 * offset + (7 - network_bit)
        block = lane % 4
        source_byte = (lane // 4) % 4 * 4 + lane // 16
        expected = [1, block * 16 + source_byte, 8, plane]
        if inverted != 0 or nodes[node_id] != expected:
            raise ValueError(f"Wrong public wire at output {position}")
        seen.add((expected[1], expected[3]))
    if len(seen) != 512:
        raise ValueError("Output does not cover every input bit exactly once")
    return {"nodes": len(nodes), "and_gates": 0, "outputs": 512,
            "distinct_input_wires": 512, "all_output_wire_references_checked": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, required=True)
    args = parser.parse_args()
    check_sources()
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
    extraction = HERE / "Artifacts/Bitslice"
    recorded = json.loads((extraction / "inventory.json").read_text())
    current = inventory(extraction / "aes_layout.llbc")
    if (current["has_errors"] or recorded["charon_exit_code"] or recorded["aeneas_exit_code"] or
            current["body_kinds"] != {"Structured": 3, "Opaque": 9} or
            sorted(x["name"] for x in current["external_functions"]) != sorted(STD_FUNCTIONS) or
            [x["name"] for x in current["external_or_union_types"]] != ["core::fmt::Arguments"] or
            current["explicit_exclusions"] or current["explicit_opaque_patterns"] or
            current["llbc_sha256"] != recorded["llbc_sha256"]):
        raise ValueError("AES bitslice extraction differs from the reviewed call graph")
    for name, expected in recorded["generated_files"].items():
        if digest(REFERENCE / name) != expected:
            raise ValueError(f"Generated reference changed: {name}")
    generated = HERE / "Generated/Bitslice"
    if sorted(p.name for p in generated.glob("*.lean")) != ["Funs.lean", "Types.lean"]:
        raise ValueError("Unexpected generated definitions or external templates")
    function_text = (generated / "Funs.lean").read_text()
    if re.findall(r"^def ([^\s]+)", function_text, re.M) != [
            "soft.fixslice.delta_swap_2", "soft.fixslice.bitslice.read_reordered", "soft.fixslice.bitslice"]:
        raise ValueError("Generated function inventory differs")
    if "core.fmt" in function_text or "core::fmt" in function_text:
        raise ValueError("Panic formatting unexpectedly remains computationally relevant")
    if re.search(r"^\s*(?:opaque|structure|inductive|def)\b", (generated / "Types.lean").read_text(), re.M):
        raise ValueError("Expected erased formatting metadata, found generated types")
    proof_paths = [HERE / (module + ".lean") for module in MODULES]
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
    subprocess.run(["lake", "build", "TlsMpc.ByteCircuit", "TlsMpc.AesSbox"], cwd=ROOT, check=True)
    output = REFERENCE / ".lake/build/lib/lean"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in
        [output, ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean", *package_paths])
    for module in MODULES:
        source_name = "AesLayoutWork/" + module + ".lean"
        target = output / ("AesLayoutWork/" + module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), source_name], cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "AesLayoutWork/Checks.lean"], cwd=REFERENCE, env=env,
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
    exported = subprocess.check_output(["lean", "--run", "AesLayoutWork/Export.lean"],
                                       cwd=REFERENCE, env=env, text=True)
    image = json.loads(exported)
    wiring = check_wires(image)
    artifact_path = HERE / "Artifacts/bitslice.json"
    artifact_path.write_text(exported)
    if root_hashes != {name: digest(ROOT / name) for name in ROOT_FILES}:
        raise ValueError("Root compiler sources changed during the audit")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "accepted_reference": True, "reference_inventory": "Artifacts/Bitslice/inventory.json",
        "actual_locked_source": "aes 0.9.1 src/soft/fixslice64.rs:1121-1125,1193-1267; libsignal 0.106.1 Cargo.lock",
        "selected_operation": "aes::soft::fixslice::bitslice",
        "numeric_circuit_bridge_domain": "All 4 x 16 input bytes and arbitrary 8-word initial output; output eight little-endian u64 bitplanes",
        "standard_library_llbc_functions": STD_FUNCTIONS,
        "computational_standard_models": ["Slice.len", "Slice.index_usize", "Slice.update",
            "core.slice.index.Slice.index", "core.slice.index.SliceIndexRangeUsizeSlice.index",
            "core.convert.num.FromU64U8.from", "UScalar checked shifts and bitwise operations"],
        "discarded_metadata_functions": [], "discarded_metadata_types": ["core::fmt::Arguments"],
        "discarded_metadata_reason": "Panic formatting becomes massert; generated Types has no definitions and no formatting call remains",
        "explicit_exclusions": [], "source_patches": [], "custom_cryptographic_models": [], "custom_axioms": [],
        "allowed_foundational_axioms": sorted(allowed), "checked_theorems": expected_count,
        "proof_sources_sha256": {str(p.relative_to(REFERENCE)): digest(p) for p in proof_paths},
        "root_semantics_sha256": root_hashes,
        "standard_model_sources_sha256": {p: digest(backend / p) for p in MODEL_FILES},
        "artifact_sha256": digest(artifact_path), "unverified_export_source_sha256": digest(HERE / "Export.lean"),
        "wiring_check": wiring, "native_mpc_execution_tested": False,
        "inverse_layout_complete": False, "whole_aes_rustcrypto_equivalence_established": False,
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {expected_count} forward-layout theorems and all 512 output wires; zero AND gates.")


if __name__ == "__main__":
    main()
