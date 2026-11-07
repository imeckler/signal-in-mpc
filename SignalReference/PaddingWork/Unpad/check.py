#!/usr/bin/env python3
"""Check the real full-MIR unpad reference, its circuit bridge and proof assumptions."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[1]
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest, inventory
from PaddingWork.Unpad.build_sysroot import MIRI_HASH, RUST_SOURCE_HASH

MODEL_FILES = ["Aeneas/Std/Slice.lean", "Aeneas/Std/SliceIter.lean", "Aeneas/Std/Core/Iter.lean",
               "Aeneas/Std/Scalar/Core.lean", "Aeneas/Std/Scalar/Casts.lean",
               "Aeneas/Std/Scalar/Ops/Sub.lean", "Aeneas/Std/Primitives.lean", "Aeneas/Std/WP.lean"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, required=True)
    args = parser.parse_args()
    check_sources()
    backend = (REFERENCE / PINS["aeneas"]["directory"] / "backends/lean").resolve()
    review = json.loads((HERE / "review.json").read_text())
    sysroot = json.loads((HERE / "sysroot-provenance.json").read_text())
    if sysroot["miri_archive_sha256"] != MIRI_HASH or sysroot["rust_source_archive_sha256"] != RUST_SOURCE_HASH:
        raise ValueError("Full-MIR provenance archive pins differ from reviewed tool release")
    for name, expected in sysroot["sysroot_source_files_sha256"].items():
        if digest(ROOT / sysroot["source_directory"] / name) != expected:
            raise ValueError(f"Rust core source differs: {name}")
    for name, expected in sysroot["sysroot_artifact_sha256"].items():
        if digest(ROOT / sysroot["sysroot_directory"] / name) != expected:
            raise ValueError(f"Full-MIR sysroot differs: {name}")
    if digest(HERE / "miri-nightly-2026-08-18.tar.xz") != sysroot["miri_archive_sha256"]:
        raise ValueError("Official Miri archive differs")
    if digest(ROOT / ".deps/rust-src-nightly-2026-08-18.tar.xz") != sysroot["rust_source_archive_sha256"]:
        raise ValueError("Official Rust source archive differs")
    with tarfile.open(ROOT / ".deps/rust-src-nightly-2026-08-18.tar.xz") as bundle:
        members = bundle.getnames()
        for name in sysroot["sysroot_source_files_sha256"]:
            member = next(p for p in members if p.endswith("/library/" + name))
            if bundle.extractfile(member).read() != (ROOT / sysroot["source_directory"] / name).read_bytes():
                raise ValueError(f"Rust core source differs from official source archive: {name}")
    aeneas_archive = ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz"
    if digest(aeneas_archive) != PINS["aeneas"]["macos_aarch64_archive_sha256"]:
        raise ValueError("Official Aeneas archive differs")
    with tarfile.open(aeneas_archive) as bundle:
        for name in MODEL_FILES:
            if bundle.extractfile("backends/lean/" + name).read() != (backend / name).read_bytes():
                raise ValueError(f"Aeneas model changed: {name}")
    for path in (ROOT / "lean-toolchain", REFERENCE / "lean-toolchain", backend / "lean-toolchain"):
        if path.read_text().strip() != PINS["aeneas"]["lean_toolchain"]:
            raise ValueError(f"Lean version differs: {path}")
    extraction = HERE / "Artifacts/RawSliceIteratorFullMir"
    recorded = json.loads((extraction / "inventory.json").read_text())
    if (PINS["charon"]["commit"] not in recorded["versions"]["charon"] or
            PINS["aeneas"]["release"] not in recorded["versions"]["aeneas"] or
            recorded["versions"]["rustc"] != PINS["charon"]["rustc_version"]):
        raise ValueError("Reference extraction tool versions differ")
    current = inventory(extraction / "pkcs7_unpad.llbc")
    if (recorded["charon_exit_code"] or recorded["aeneas_exit_code"] or current["has_errors"] or
            current["body_kinds"] != {"Structured": 6, "Opaque": 20} or
            current["counts"]["fun_decls"] != 26 or
            current["llbc_sha256"] != recorded["llbc_sha256"] or
            [f["name"] for f in current["external_functions"]] != review["reviewed_llbc_opaque_functions"] or
            [f["name"] for f in current["external_or_union_types"]] != review["reviewed_llbc_opaque_types"] or
            current["explicit_exclusions"] != review["explicit_exclusions"]):
        raise ValueError("Unpad extraction differs from its reviewed call graph")
    generated = HERE / "Generated/RawSliceIteratorFullMir"
    if sorted(p.name for p in generated.glob("*.lean")) != ["Funs.lean", "Types.lean"]:
        raise ValueError("External template or unexpected generated file")
    for name, expected in recorded["generated_files"].items():
        if digest(REFERENCE / name) != expected:
            raise ValueError(f"Generated reference changed: {name}")
    if len(re.findall(r"^def\s", (generated / "Funs.lean").read_text(), re.M)) != 9:
        raise ValueError("Generated function or loop count differs")
    if re.findall(r"^def\s+([^\s]+)", (generated / "Types.lean").read_text(), re.M) != ["Error", "Pkcs7.unpad.closure"]:
        raise ValueError("Unexpected generated types or metadata")
    computational = "\n".join(line for line in (generated / "Funs.lean").read_text().splitlines()
                               if not line.strip().startswith(("--", "/--", "Source:", "Name pattern:", "Visibility:")))
    if any(name in computational for name in ["core.fmt", "core.iter.adapters", "core.array.iter",
                                               "core.num.nonzero", "core.num.niche_types"]):
        raise ValueError("Discarded trait/panic metadata has entered the computational reference")
    sources = [*sorted(generated.glob("*.lean")), HERE / "Circuit.lean", HERE / "Proofs.lean", HERE / "Bridge.lean"]
    for path in sources:
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", path.read_text()):
            raise ValueError(f"Incomplete proof or custom assumption: {path}")
    package_paths = []
    for package in json.loads((backend / "lake-manifest.json").read_text())["packages"]:
        directory = args.packages_dir / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Cached package revision differs: {directory}")
        if (directory / ".lake/build/lib/lean").is_dir():
            package_paths.append(directory / ".lake/build/lib/lean")
    subprocess.run(["lake", "build", "TlsMpc.ByteAuth"], cwd=ROOT, check=True)
    output = REFERENCE / ".lake/build/lib/lean"
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(path) for path in
        [output, ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean", *package_paths])
    for module in ["PaddingWork/Unpad/Generated/RawSliceIteratorFullMir/Types",
                   "PaddingWork/Unpad/Generated/RawSliceIteratorFullMir/Funs",
                   "PaddingWork/Unpad/Circuit", "PaddingWork/Unpad/Proofs", "PaddingWork/Unpad/Bridge"]:
        target = output / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), module + ".lean"], cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "PaddingWork/Unpad/Checks.lean"], cwd=REFERENCE, env=env,
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
        "checked_at_utc": datetime.now(timezone.utc).isoformat(), "accepted_reference": True,
        "reference_inventory": "Artifacts/RawSliceIteratorFullMir/inventory.json", "review": "review.json",
        "sysroot_provenance": "sysroot-provenance.json", "checked_theorems": expected_count,
        "allowed_foundational_axioms": sorted(allowed), "custom_axioms": [],
        "proof_sources_sha256": {str(p.relative_to(REFERENCE)): digest(p) for p in sources},
        "standard_model_sources_sha256": {p: digest(backend / p) for p in MODEL_FILES},
        "root_semantics_sha256": {str(p.relative_to(ROOT)): digest(p) for p in
            [ROOT / "TlsMpc/ByteAuth.lean", ROOT / "TlsMpc/ByteCircuit.lean", ROOT / "TlsMpc/AigExport.lean"]},
        "all_input_bytes_proved": True, "input_length_bytes": 16, "output_length_bytes": 18,
        "all_outputs_secret": True, "output_encoding_injective": True,
        "whole_cbc_refinement_established": False, "authenticated_release_composition_established": False,
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Actual PKCS7 unpad16 implementation and numeric secret-output circuit bridge checked.")


if __name__ == "__main__":
    main()
