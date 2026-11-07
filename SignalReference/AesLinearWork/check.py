#!/usr/bin/env python3
"""Audit actual RustCrypto AES linear references, proof assumptions, and exports."""

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

STD_FUNCTIONS = {
    "MixColumns0": ["core::num::{impl}::rotate_right"],
    "ShiftRows": ["core::slice::{impl}::len", "core::slice::{impl}::iter_mut",
                  "core::iter::traits::collect::{impl}::into_iter", "core::slice::iter::{impl}::next",
                  "core::clone::impls::{impl}::clone", "core::num::niche_types::{impl}::clone"],
}
DISCARDED_TYPES = [
    "core::fmt::Arguments", "core::array::iter::IntoIter", "core::num::nonzero::NonZero",
    "core::iter::adapters::step_by::StepBy", "core::iter::adapters::chain::Chain",
    "core::iter::adapters::zip::Zip", "core::iter::adapters::intersperse::Intersperse",
    "core::iter::adapters::intersperse::IntersperseWith", "core::iter::adapters::map::Map",
    "core::iter::adapters::filter::Filter", "core::iter::adapters::filter_map::FilterMap",
    "core::iter::adapters::enumerate::Enumerate", "core::iter::adapters::peekable::Peekable",
    "core::iter::adapters::skip_while::SkipWhile", "core::iter::adapters::take_while::TakeWhile",
    "core::iter::adapters::map_while::MapWhile", "core::iter::adapters::skip::Skip",
    "core::iter::adapters::take::Take", "core::iter::adapters::scan::Scan",
    "core::iter::adapters::flatten::FlatMap", "core::iter::adapters::flatten::Flatten",
    "core::iter::adapters::map_windows::MapWindows", "core::iter::adapters::fuse::Fuse",
    "core::iter::adapters::inspect::Inspect", "core::iter::adapters::rev::Rev",
    "core::iter::adapters::copied::Copied", "core::iter::adapters::cloned::Cloned",
    "core::iter::adapters::cycle::Cycle", "core::iter::adapters::array_chunks::ArrayChunks",
    "core::num::niche_types::NonZeroUsizeInner",
]
GENERATED_DEFS = {
    "MixColumns0": ["ror_distance", "ror", "rotate_rows_2", "rotate_rows_1", "mix_columns_0"],
    "ShiftRows": ["delta_swap_1"] +
        [f"shift_rows_{n}{suffix}" for n in (1, 2, 3) for suffix in ("_loop.body", "_loop", "")],
}
MODEL_FILES = [
    "Aeneas/Std/Array/Array.lean", "Aeneas/Std/Array/Core.lean",
    "Aeneas/Std/Slice.lean", "Aeneas/Std/SliceDef.lean", "Aeneas/Std/SliceIter.lean",
    "Aeneas/Std/Core/Iter.lean", "Aeneas/Data/List/List.lean", "Aeneas/Std/Scalar/Core.lean",
    "Aeneas/Std/Scalar/Bitwise.lean", "Aeneas/Std/Scalar/Rotate.lean",
    "Aeneas/Std/Scalar/Ops/Add.lean", "Aeneas/Std/Primitives.lean",
]
MODULES = ["LibSignalReference/Generated/AesMix/Types", "LibSignalReference/Generated/AesMix/Funs",
           "LibSignalReference/Generated/AesShift/Types", "LibSignalReference/Generated/AesShift/Funs",
           *["LibSignalReference/Proofs/" + name for name in (
               "AesLinearReference", "AesLinearLayout", "AesLinearBits", "AesLinearFormula",
               "AesLinearProofs", "AesLinear", "AesShiftReference", "AesShiftBits", "AesShift")]]
CANONICAL_MODULES = ["LibSignalReference/Generated/AesLayout/Types",
                     "LibSignalReference/Generated/AesLayout/Funs",
                     "LibSignalReference/Proofs/AesLayoutReference",
                     "LibSignalReference/Proofs/AesLayoutPermutation",
                     "LibSignalReference/Proofs/AesLayout"]
ROOT_FILES = ["TlsMpc/Aes.lean", "TlsMpc/AesSbox.lean", "TlsMpc/Signal/AesLayoutNetwork.lean",
              "TlsMpc/Signal/AesLayout.lean", "TlsMpc/Signal/AesMix.lean", "TlsMpc/Signal/AesShift.lean", "TlsMpc/ByteCircuit.lean", "TlsMpc/AigExport.lean",
              "TlsMpc/BvConstruct.lean", "backend_adapter/aig.py"]


def regular_references(value):
    if isinstance(value, dict):
        if type(value.get("Regular")) is int:
            yield value["Regular"]
        for child in value.values():
            yield from regular_references(child)
    elif isinstance(value, list):
        for child in value:
            yield from regular_references(child)


def audit_reference(profile):
    key, subdir = {"MixColumns0": ("aes_mix_columns_0", "AesMix"),
                   "ShiftRows": ("aes_shift_rows", "AesShift")}[profile]
    extraction = REFERENCE / "Extraction"
    record_path = extraction / (key + ".json")
    llbc = extraction / ("libsignal_" + key + ".llbc")
    recorded = json.loads(record_path.read_text())
    current = inventory(llbc)
    opaque_types = [] if profile == "MixColumns0" else [*DISCARDED_TYPES, "core::slice::iter::IterMut"]
    body_counts = {"Structured": 5, "Opaque": 1} if profile == "MixColumns0" else {"Structured": 4, "Opaque": 6}
    if (current["has_errors"] or recorded["charon_exit_code"] or recorded["aeneas_exit_code"] or
            current["body_kinds"] != body_counts or
            sorted(x["name"] for x in current["external_functions"]) != sorted(STD_FUNCTIONS[profile]) or
            sorted(x["name"] for x in current["external_or_union_types"]) != sorted(opaque_types) or
            current["explicit_exclusions"] or current["explicit_opaque_patterns"] or recorded.get("source_patches", []) or
            current["llbc_sha256"] != recorded["llbc_sha256"] or
            recorded["rustflags"] != '--cfg aes_backend="soft"'):
        raise ValueError(f"{profile} differs from the reviewed extraction")
    for name, expected in recorded["generated_files"].items():
        if digest(REFERENCE / name) != expected:
            raise ValueError(f"Generated reference changed: {name}")
    generated = REFERENCE / "LibSignalReference/Generated" / subdir
    if sorted(p.name for p in generated.glob("*.lean")) != ["Funs.lean", "Types.lean"]:
        raise ValueError(f"Unexpected generated definitions or external templates: {profile}")
    source = (generated / "Funs.lean").read_text()
    if re.findall(r"^def ([^\s]+)", source, re.M) != ["soft.fixslice." + n for n in GENERATED_DEFS[profile]]:
        raise ValueError(f"Generated function inventory differs: {profile}")
    if any(name in source for name in ("core.fmt", "core.clone", "core.num.niche", "core.iter.adapters")):
        raise ValueError("Discarded metadata unexpectedly remains computationally relevant")
    if re.search(r"^\s*(?:opaque|structure|inductive|def)\b", (generated / "Types.lean").read_text(), re.M):
        raise ValueError("Expected no generated types")
    translated = json.loads(llbc.read_text())["translated"]
    referenced = sorted(set(ref for fn in translated["fun_decls"] if fn
                            for ref in regular_references(fn.get("body"))))
    if referenced != ([1, 2, 3, 4, 5] if profile == "MixColumns0" else [3, 4, 5, 6, 7]):
        raise ValueError("Selected body function dependencies changed")
    if any(translated["global_decls"]):
        raise ValueError("Unexpected global dependencies")
    return {"inventory": str(record_path.relative_to(REFERENCE)),
            "llbc_sha256": current["llbc_sha256"], "generated_files": recorded["generated_files"],
            "body_regular_function_ids": referenced,
            "standard_library_llbc_functions": STD_FUNCTIONS[profile],
            "discarded_metadata_types": [] if profile == "MixColumns0" else DISCARDED_TYPES,
            "modeled_types": [] if profile == "MixColumns0" else ["core::slice::iter::IterMut"],
            "discarded_metadata_functions": [] if profile == "MixColumns0" else STD_FUNCTIONS[profile][-2:]}


def expected_basis(name):
    # Each integer packs all 512 independent input-bit basis vectors. This is
    # an unverified native-export check, separate from the Lean refinement.
    def byte(block, index):
        return [1 << (block * 128 + index * 8 + 7 - bit) for bit in range(8)]
    def xtime(a):
        return [a[7], a[0] ^ a[7], a[1], a[2] ^ a[7], a[3] ^ a[7], a[4], a[5], a[6]]
    def out_byte(block, index):
        column, row = divmod(index, 4)
        if "shift-rows" in name:
            return byte(block, 4 * ((column + int(name[-1]) * row) % 4) + row)
        a, b, c, d = [byte(block, column * 4 + (row + n) % 4) for n in range(4)]
        aa, bb = xtime(a), xtime(b)
        return [aa[k] ^ bb[k] ^ b[k] ^ c[k] ^ d[k] for k in range(8)]
    expected = []
    for position in range(512):
        byte_position, network_bit = divmod(position, 8)
        plane, offset = divmod(byte_position, 8)
        lane = 8 * offset + 7 - network_bit
        expected.append(out_byte(lane % 4, (lane // 4) % 4 * 4 + lane // 16)[plane])
    return expected


def check_image(image):
    aig.validate(image)
    if image["input_bits"] != 512 or image["input_widths"] != [8] * 64 or len(image["outputs"]) != 512:
        raise ValueError("Unexpected AES linear ABI")
    stats = aig.statistics(image)
    if stats["executed_and_gates"]:
        raise ValueError("Expected only public wiring and XOR operations")
    if "shift-rows" in image["name"] and stats["raw_and_gates"]:
        raise ValueError("Expected a wiring-only ShiftRows circuit")
    expected = expected_basis(image["name"])
    packed_one = (1 << 512) - 1
    for optimize in (False, True):
        got = aig.execute(image, [1 << index for index in range(512)], 0, packed_one, optimize=optimize)
        if got != expected or any(aig.execute(image, [0] * 512, 0, 1, optimize=optimize)):
            raise ValueError("Native artifact disagrees with the independent linear transformation")
    return {"nodes": len(image["nodes"]), **stats, "outputs": 512,
            "zero_and_all_512_basis_vectors_checked": True, "raw_and_optimized_adapter_checked": True}


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
    references = {profile: audit_reference(profile) for profile in STD_FUNCTIONS}
    proof_paths = [REFERENCE / (module + ".lean") for module in MODULES]
    canonical_paths = [REFERENCE / (module + ".lean") for module in CANONICAL_MODULES]
    for path in [*proof_paths, *canonical_paths]:
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
    canonical_hashes = {str(path.relative_to(REFERENCE)): digest(path) for path in canonical_paths}
    subprocess.run(["lake", "build", "TlsMpc.Aes", "TlsMpc.Signal.AesLayout", "TlsMpc.Signal.AesMix", "TlsMpc.Signal.AesShift"], cwd=ROOT, check=True)
    output = REFERENCE / ".lake/build/lib/lean"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in
        [output, ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean", *package_paths])
    for module in [*CANONICAL_MODULES, *MODULES]:
        target = output / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), module + ".lean"], cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "AesLinearWork/Checks.lean"], cwd=REFERENCE, env=env,
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
    exported = subprocess.check_output(["lean", "--run", "AesLinearWork/Export.lean"],
                                       cwd=REFERENCE, env=env, text=True)
    images = json.loads(exported)
    if [image["name"] for image in images] != ["aes-mix-columns-0", *[f"aes-shift-rows-{n}" for n in (1, 2, 3)]]:
        raise ValueError("Unexpected native export inventory")
    artifact_reports = {}
    for image in images:
        checks = check_image(image)
        artifact_path = HERE / "Artifacts" / (image["name"] + ".json")
        artifact_path.write_text(json.dumps(image, separators=(",", ":")) + "\n")
        artifact_reports[image["name"]] = {"artifact_sha256": digest(artifact_path), **checks}
    if root_hashes != {name: digest(ROOT / name) for name in ROOT_FILES} or canonical_hashes != {
            str(path.relative_to(REFERENCE)): digest(path) for path in canonical_paths}:
        raise ValueError("Shared proof/compiler sources changed during the audit")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(), "accepted_reference": True, "canonical_reference_integrated": True,
        "references": references, "actual_locked_source": "aes 0.9.1 src/soft/fixslice64.rs; libsignal 0.106.1 Cargo.lock",
        "numeric_circuit_bridge_domain": "All 4 x 16 secret bytes in the canonical ordinary bitplane layout; fixed 8-word state; output eight little-endian u64 bitplanes",
        "selected_operations": ["mix_columns_0", "shift_rows_1", "shift_rows_2", "shift_rows_3"],
        "shape_errors": "All three translated ShiftRows functions reject a slice whose public length differs from 8; numeric circuit domain fixes length 8",
        "computational_standard_models": ["Array.index_usize/update", "Slice.len", "core.slice.Slice.iter_mut",
            "core.slice.iter.IteratorIterMut.next with borrow writeback", "IntoIterator blanket identity (inlined)",
            "UScalar checked shifts/addition, XOR, AND, and rotate_right", "Result, massert, and loop"],
        "discarded_metadata_reason": "Generated Types files are empty; no clone/adaptor/panic-formatting computation remains; discarded clone IDs 129/130 are not referenced by selected bodies",
        "explicit_exclusions": [], "source_patches": [], "custom_cryptographic_models": [], "custom_axioms": [],
        "allowed_foundational_axioms": sorted(allowed), "checked_theorems": expected_count,
        "proof_sources_sha256": {str(p.relative_to(REFERENCE)): digest(p) for p in proof_paths},
        "canonical_layout_sources_sha256": canonical_hashes, "root_semantics_sha256": root_hashes,
        "standard_model_sources_sha256": {p: digest(backend / p) for p in MODEL_FILES},
        "unverified_export_source_sha256": digest(HERE / "Export.lean"),
        "audit_script_sha256": digest(Path(__file__)), "extraction_script_sha256": digest(REFERENCE / "extract.py"),
        "artifacts": artifact_reports, "native_mpc_execution_tested": False,
        "other_mix_columns_phases_complete": False, "whole_aes_rustcrypto_equivalence_established": False,
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {expected_count} AES linear theorems and four numeric artifacts; zero executed AND gates.")


if __name__ == "__main__":
    main()
