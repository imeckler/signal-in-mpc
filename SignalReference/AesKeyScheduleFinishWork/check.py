#!/usr/bin/env python3
"""Audit actual AES256 key-schedule postprocessing equivalence."""

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
from extract import PINS, check_sources, digest
from AesKeyScheduleLeavesWork.check import audit_reference

MODULES = ["AesKeyScheduleFinishWork." + name for name in
           ("Windows", "Restoration", "Phases", "Finish")]
PREFIXES = ("LibSignalReference.", "AesKeyScheduleWork.",
            "AesKeyScheduleLeavesWork.", "AesKeyScheduleFinishWork.")


def source_dependencies():
    """Return exact transitive workspace sources and a build order."""
    reference, root, order = {}, {}, []

    def visit(module):
        relative = module.replace(".", "/") + ".lean"
        if relative in reference or relative in root:
            return
        if module.startswith("TlsMpc."):
            source, destination = ROOT / relative, root
        elif module.startswith(PREFIXES):
            source, destination = REFERENCE / relative, reference
        else:
            return
        destination[relative] = digest(source)
        for imported in re.findall(r"^import ([A-Za-z0-9_.]+)", source.read_text(), re.M):
            visit(imported)
        if destination is reference:
            order.append(module)

    for module in MODULES:
        visit(module)
    return reference, root, order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, required=True)
    args = parser.parse_args()
    check_sources()
    reference = audit_reference()
    canonical_path = REFERENCE / "Extraction/proof-check.json"
    leaves_path = REFERENCE / "AesKeyScheduleLeavesWork/proof-check.json"
    key_path = REFERENCE / "AesKeyScheduleWork/check-report.json"
    canonical = json.loads(canonical_path.read_text())
    leaves = json.loads(leaves_path.read_text())
    key = json.loads(key_path.read_text())
    if canonical["accepted_custom_axioms"] or leaves["custom_axioms"]:
        raise ValueError("A reused proof audit accepts custom axioms")
    ref_hashes, root_hashes, order = source_dependencies()
    for name, expected in ref_hashes.items():
        if name.startswith("LibSignalReference/") and canonical["proof_sources_sha256"].get(name) != expected:
            raise ValueError(f"Canonical proof changed since its completed audit: {name}")
        if name.startswith("AesKeyScheduleLeavesWork/") and leaves["proof_sources_sha256"].get(name) != expected:
            raise ValueError(f"Frozen helper proof changed since its completed audit: {name}")
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", (REFERENCE / name).read_text()):
            raise ValueError(f"Incomplete or externally checked proof source: {name}")
    backend = (REFERENCE / PINS["aeneas"]["directory"] / "backends/lean").resolve()
    archive = ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz"
    if digest(archive) != PINS["aeneas"]["macos_aarch64_archive_sha256"]:
        raise ValueError("Official Aeneas archive changed")
    models = set(canonical["standard_model_sources_sha256"])
    models |= set(leaves["standard_model_sources_sha256"])
    models |= set(key["standard_model_sources_sha256"])
    with tarfile.open(archive) as bundle:
        for name in models:
            original = bundle.extractfile("backends/lean/" + name)
            if original is None or original.read() != (backend / name).read_bytes():
                raise ValueError(f"Official Aeneas standard model differs: {name}")
    for path in (ROOT / "lean-toolchain", REFERENCE / "lean-toolchain", backend / "lean-toolchain"):
        if path.read_text().strip() != PINS["aeneas"]["lean_toolchain"]:
            raise ValueError(f"Lean toolchain differs: {path}")
    paths = [REFERENCE / ".lake/build/lib/lean", ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean"]
    revisions = {}
    for package in json.loads((backend / "lake-manifest.json").read_text())["packages"]:
        directory = args.packages_dir / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Cached proof package differs: {directory}")
        revisions[package["name"]] = revision
        built = directory / ".lake/build/lib/lean"
        if built.is_dir():
            paths.append(built)
    subprocess.run(["lake", "build", "TlsMpc.Signal.AesKeySchedule"], cwd=ROOT, check=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    rebuilt = []
    for module in order:
        if module.startswith("LibSignalReference."):
            continue  # Reused canonical proofs are checked against their completed audit above.
        relative = module.replace(".", "/")
        target = paths[0] / (relative + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), relative + ".lean"], cwd=REFERENCE,
                       env=env, check=True)
        rebuilt.append(module)
    result = subprocess.run(["lean", "AesKeyScheduleFinishWork/Checks.lean"], cwd=REFERENCE,
                            env=env, text=True, capture_output=True, check=True)
    (HERE / "axiom-report.txt").write_text(result.stdout)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    expected_names = re.findall(r"^#print axioms (\S+)", (HERE / "Checks.lean").read_text(), re.M)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if [name for name, _ in reports] != expected_names:
        raise ValueError("Missing or unexpected theorem assumption reports")
    for name, names in reports:
        if {entry.strip() for entry in names.split(",") if entry.strip()} - allowed:
            raise ValueError(f"Unexpected theorem assumptions in {name}: {names}")
    if (ref_hashes, root_hashes, order) != source_dependencies():
        raise ValueError("Proof or root operation sources changed during audit")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "accepted_reference": True,
        "reference": reference,
        "proof_namespace": "LibSignalReference.Candidate.AesKeyScheduleFinish",
        "proof_sources_sha256": ref_hashes,
        "root_sources_sha256": root_hashes,
        "rebuilt_reference_modules": rebuilt,
        "canonical_dependency_audit_utc": canonical["checked_at_utc"],
        "canonical_dependency_audit_sha256": digest(canonical_path),
        "frozen_helper_dependency_audit_utc": leaves["checked_at_utc"],
        "frozen_helper_dependency_audit_sha256": digest(leaves_path),
        "standard_model_sources_sha256": {name: digest(backend / name) for name in sorted(models)},
        "proof_package_revisions": revisions,
        "checked_theorems": len(reports),
        "theorems": [name for name, _ in reports],
        "axiom_report_sha256": digest(HERE / "axiom-report.txt"),
        "allowed_foundational_axioms": sorted(allowed),
        "custom_axioms": [], "source_patches": [], "custom_cryptographic_models": [],
        "input_domain": "Every Aeneas Array U64 120, all7680 word bits unrestricted and secret; loop bounds and offsets public",
        "operation": "Exact generated post-loop0 tail: step_by32 over8..104, three inverse-shift groups, special104..112 inverse1, and NOT restoration rounds1..14",
        "result": "Actual translated operation returns .ok and mapped entire120-word output equals root AesKeySchedule.finish concrete input",
        "trusted_boundary": ["Faithful Charon/Aeneas translation", "Reviewed unused-metadata selection", "Pinned Aeneas array/slice and iterator standard models"],
        "whole_key_schedule_equivalence_established_here": False,
        "independent_protocol_or_security_proof_added": False,
        "new_native_backend_execution": False,
        "audit_source_sha256": digest(Path(__file__)),
        "reference_audit_helper_sha256": digest(REFERENCE / "AesKeyScheduleLeavesWork/check.py"),
        "checks_source_sha256": digest(HERE / "Checks.lean"),
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {len(reports)} actual postprocessing endpoints; only standard foundational axioms.")


if __name__ == "__main__":
    main()
