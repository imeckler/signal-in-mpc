#!/usr/bin/env python3
"""Audit the isolated PKCS7 extraction and kernel-check its refinement proofs."""

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
from PaddingWork.extract_padding import SCOPED

STD_FUNCTIONS = [
    "core::slice::{impl}::len", "core::fmt::{impl}::from_str",
    "core::slice::index::{impl}::index_mut", "core::slice::{impl}::fill",
    "core::slice::index::{impl}::get", "core::slice::index::{impl}::get_mut",
    "core::slice::index::{impl}::get_unchecked",
    "core::slice::index::{impl}::get_unchecked_mut",
    "core::slice::index::{impl}::index", "core::slice::index::{impl}::index_mut",
    "core::clone::impls::{impl}::clone", "core::slice::index::{impl}::index",
]
MODEL_FILES = [
    "Aeneas/Std/Slice.lean", "Aeneas/Std/Scalar/Core.lean",
    "Aeneas/Std/Scalar/Casts.lean", "Aeneas/Std/Scalar/CloneCopy.lean",
    "Aeneas/Std/Scalar/Ops/Sub.lean", "Aeneas/Std/Primitives.lean",
]


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
    extraction = HERE / "Artifacts/ExcludeArraySize"
    recorded = json.loads((extraction / "inventory.json").read_text())
    current = inventory(extraction / "pkcs7.llbc")
    expected_exclusions = [x.removeprefix("--exclude=") for x in SCOPED]
    expected_exclusions.append("hybrid_array::traits::ArraySize")
    if (current["has_errors"] or recorded["charon_exit_code"] or recorded["aeneas_exit_code"] or
            current["body_kinds"] != {"Structured": 1, "Opaque": 12} or
            sorted(x["name"] for x in current["external_functions"]) != sorted(STD_FUNCTIONS) or
            [x["name"] for x in current["external_or_union_types"]] != ["core::fmt::Arguments"] or
            current["explicit_exclusions"] != expected_exclusions or
            current["llbc_sha256"] != recorded["llbc_sha256"]):
        raise ValueError("PKCS7 extraction differs from the reviewed call graph")
    for name, expected in recorded["generated_files"].items():
        if digest(REFERENCE / name) != expected:
            raise ValueError(f"Generated reference changed: {name}")
    generated = HERE / "Generated/ExcludeArraySize"
    if sorted(p.name for p in generated.glob("*.lean")) != ["Funs.lean", "Types.lean"]:
        raise ValueError("Unexpected generated definitions or external templates")
    function_text = (generated / "Funs.lean").read_text()
    if re.findall(r"^def ([^\s]+)", function_text, re.M) != ["Pkcs7.Insts.Block_paddingPadding.raw_pad"]:
        raise ValueError("Generated function inventory differs")
    if "core.fmt" in function_text or "core::fmt" in function_text:
        raise ValueError("Panic formatting unexpectedly remains computationally relevant")
    if re.search(r"^\s*(?:opaque|structure|inductive|def)\b", (generated / "Types.lean").read_text(), re.M):
        raise ValueError("Expected erased formatting/trait metadata, found generated types")
    proof_paths = [*sorted(generated.glob("*.lean")), HERE / "Proofs.lean"]
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
    subprocess.run(["lake", "build", "TlsMpc.Signal.Cbc"], cwd=ROOT, check=True)
    output = REFERENCE / ".lake/build/lib/lean"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in
        [output, ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean", *package_paths])
    for module in ["PaddingWork/Generated/ExcludeArraySize/Types",
                   "PaddingWork/Generated/ExcludeArraySize/Funs", "PaddingWork/Proofs"]:
        target = output / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), module + ".lean"], cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "PaddingWork/Checks.lean"], cwd=REFERENCE, env=env,
                            check=True, text=True, capture_output=True)
    print(result.stdout, end="")
    axioms = re.findall(r"depends on axioms: \[([^]]*)\]", result.stdout)
    expected_count = len(re.findall(r"^#print axioms ", (HERE / "Checks.lean").read_text(), re.M))
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if len(axioms) != expected_count:
        raise ValueError("Missing theorem assumption reports")
    for names in axioms:
        if {x.strip() for x in names.split(",") if x.strip()} - allowed:
            raise ValueError(f"Unexpected proof assumptions: {names}")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "accepted_reference": True, "reference_inventory": "Artifacts/ExcludeArraySize/inventory.json",
        "actual_locked_source": "block-padding0.4.2 src/lib.rs186-195; libsignal0.106.1 Cargo.lock",
        "selected_operation": "Pkcs7::raw_pad",
        "full_domain": "All Slice<U8> and Usize values; exact translated assertion failures and successful byte output",
        "numeric_circuit_bridge_domain": "AES block length16, all positions0..15, all byte values; arbitrary unchanged full-block prefix",
        "standard_library_llbc_functions": STD_FUNCTIONS,
        "discarded_metadata_functions": ["core::fmt::{impl}::from_str"],
        "discarded_metadata_types": ["core::fmt::Arguments"],
        "discarded_metadata_reason": "Panic formatting is replaced with massert; generated Types has no definitions and Funs contains no formatting call",
        "explicit_exclusions": expected_exclusions,
        "source_patches": [], "custom_cryptographic_models": [], "custom_axioms": [],
        "allowed_foundational_axioms": sorted(allowed), "checked_theorems": expected_count,
        "proof_sources_sha256": {str(p.relative_to(REFERENCE)): digest(p) for p in proof_paths},
        "root_semantics_sha256": {str(p.relative_to(ROOT)): digest(p) for p in
            [ROOT / "TlsMpc/Signal/Cbc.lean", ROOT / "TlsMpc/Aes.lean",
             ROOT / "TlsMpc/AesSbox.lean", ROOT / "TlsMpc/ByteCircuit.lean",
             ROOT / "TlsMpc/AigExport.lean", ROOT / "TlsMpc/BvConstruct.lean"]},
        "standard_model_sources_sha256": {p: digest(backend / p) for p in MODEL_FILES},
        "whole_cbc_rustcrypto_equivalence_established": False,
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print("PKCS7 total behavior and numeric CBC-padding bridge checked; whole CBC remains separate.")


if __name__ == "__main__":
    main()
