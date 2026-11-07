#!/usr/bin/env python3
"""Audit reusable helper bridges from the actual reviewed AES256 extraction."""

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
from AesKeyScheduleWork.inspect_metadata import select

MODULES = ["AesKeyScheduleLeavesWork/" + name for name in
           ("Equalities", "SubBytes", "InverseShift", "Nots", "Layout")]
GENERATED = ["AesKeyScheduleWork/Generated/Types", "AesKeyScheduleWork/Generated/Funs"]


def source_dependencies():
    """Record every workspace Lean import, including reused canonical proofs."""
    pending = list(MODULES)
    reference, root = {}, {}
    while pending:
        module = pending.pop()
        relative = module.replace(".", "/") + ".lean"
        if relative in reference or relative in root:
            continue
        if module.startswith("TlsMpc"):
            source, destination = ROOT / relative, root
        elif module.startswith(("LibSignalReference", "AesKeyScheduleWork", "AesKeyScheduleLeavesWork")):
            source, destination = REFERENCE / relative, reference
        else:
            continue
        destination[relative] = digest(source)
        pending.extend(re.findall(r"^import ([A-Za-z0-9_.]+)", source.read_text(), re.M))
    return reference, root


def audit_reference():
    original = REFERENCE / "Extraction/libsignal_aes256_key_schedule.llbc"
    selected = REFERENCE / "AesKeyScheduleWork/selected.llbc"
    review_path = REFERENCE / "AesKeyScheduleWork/review.json"
    review = json.loads(review_path.read_text())
    expected, changes = select(json.loads(original.read_text()))
    if (json.loads(selected.read_text()) != expected or changes != review["changes"] or
            digest(selected) != review["selected_sha256"] or review["source_patches"] or
            review["computational_bodies_modified"] or review["aeneas_exit_code"]):
        raise ValueError("Reviewed actual key-schedule extraction differs")
    if digest(REFERENCE / "AesKeyScheduleWork/inspect_metadata.py") != review["script_sha256"]:
        raise ValueError("Trusted selector differs from its generated-reference record")
    independent_path = REFERENCE / review["independent_review"]
    independent = json.loads(independent_path.read_text())
    if (not independent["independent_review"] or independent["concerns"] or
            independent["reviewed_filter_sha256"] != review["script_sha256"] or
            independent["selected_llbc_sha256"] != digest(selected) or
            independent["exact_reversible_changes"] != len(changes) or
            not independent["full_retained_semantic_json_scanned"]):
        raise ValueError("Independent hardened-selector review differs")
    generated = REFERENCE / "AesKeyScheduleWork/Generated"
    if sorted(path.name for path in generated.glob("*.lean")) != ["Funs.lean", "Types.lean"]:
        raise ValueError("Unexpected external template in actual extraction")
    for name, expected_hash in review["generated_files"].items():
        if digest(REFERENCE / name) != expected_hash:
            raise ValueError(f"Actual generated helper changed: {name}")
    return {"source_llbc_sha256": digest(original), "selected_llbc_sha256": digest(selected),
            "selection_review_file": str(review_path.relative_to(REFERENCE)),
            "selection_review_sha256": digest(review_path),
            "independent_review_file": str(independent_path.relative_to(REFERENCE)),
            "independent_review_sha256": digest(independent_path),
            "trusted_selector_sha256": review["script_sha256"],
            "additional_trusted_metadata_preprocessing": True,
            "metadata_selection_correctness_mechanized": False,
            "generated_files": review["generated_files"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages-dir", type=Path, required=True)
    args = parser.parse_args()
    check_sources()
    reference = audit_reference()
    canonical = json.loads((REFERENCE / "Extraction/proof-check.json").read_text())
    key_audit = json.loads((REFERENCE / "AesKeyScheduleWork/check-report.json").read_text())
    ref_hashes, root_hashes = source_dependencies()
    for name, expected_hash in ref_hashes.items():
        if name.startswith("LibSignalReference/") and canonical["proof_sources_sha256"].get(name) != expected_hash:
            raise ValueError(f"Reused canonical proof differs from its completed audit: {name}")
    if canonical["accepted_custom_axioms"]:
        raise ValueError("Canonical dependency audit has custom axioms")
    for name in ref_hashes:
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", (REFERENCE / name).read_text()):
            raise ValueError(f"Incomplete or externally checked proof dependency: {name}")
    backend = (REFERENCE / PINS["aeneas"]["directory"] / "backends/lean").resolve()
    archive = ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz"
    if digest(archive) != PINS["aeneas"]["macos_aarch64_archive_sha256"]:
        raise ValueError("Official Aeneas archive differs")
    models = set(canonical["standard_model_sources_sha256"]) | set(key_audit["standard_model_sources_sha256"])
    with tarfile.open(archive) as bundle:
        for name in models:
            if bundle.extractfile("backends/lean/" + name).read() != (backend / name).read_bytes():
                raise ValueError(f"Official Aeneas model changed: {name}")
    for path in (ROOT / "lean-toolchain", REFERENCE / "lean-toolchain", backend / "lean-toolchain"):
        if path.read_text().strip() != PINS["aeneas"]["lean_toolchain"]:
            raise ValueError(f"Lean toolchain differs: {path}")
    paths = [REFERENCE / ".lake/build/lib/lean", ROOT / ".lake/build/lib/lean", backend / ".lake/build/lib/lean"]
    package_revisions = {}
    for package in json.loads((backend / "lake-manifest.json").read_text())["packages"]:
        directory = args.packages_dir / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Cached proof package differs: {directory}")
        package_revisions[package["name"]] = revision
        path = directory / ".lake/build/lib/lean"
        if path.is_dir():
            paths.append(path)
    subprocess.run(["lake", "build", "TlsMpc.Signal.AesKeySchedule"], cwd=ROOT, check=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    for module in [*GENERATED, *MODULES]:
        target = paths[0] / (module + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lean", "-o", str(target), module + ".lean"], cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "AesKeyScheduleLeavesWork/Checks.lean"], cwd=REFERENCE,
                            env=env, text=True, capture_output=True, check=True)
    (HERE / "axiom-report.txt").write_text(result.stdout)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    expected_names = re.findall(r"^#print axioms (\S+)", (HERE / "Checks.lean").read_text(), re.M)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if [name for name, _ in reports] != expected_names:
        raise ValueError("Missing or unexpected theorem assumption reports")
    for name, names in reports:
        if {axiom.strip() for axiom in names.split(",") if axiom.strip()} - allowed:
            raise ValueError(f"Unexpected proof assumptions in {name}: {names}")
    if (ref_hashes, root_hashes) != source_dependencies():
        raise ValueError("Proof or root operation source changed during audit")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "accepted_reference": True, "canonical_leaf_package_integrated": False,
        "reference": reference,
        "proof_namespace": "LibSignalReference.Proofs.AesKeyScheduleLeaves",
        "proof_sources_sha256": ref_hashes, "root_sources_sha256": root_hashes,
        "canonical_dependency_audit_utc": canonical["checked_at_utc"],
        "canonical_dependencies_reused_from_completed_audit": True,
        "standard_model_sources_sha256": {name: digest(backend / name) for name in sorted(models)},
        "proof_package_revisions": package_revisions,
        "checked_theorems": len(reports), "theorems": [name for name, _ in reports],
        "axiom_report_sha256": digest(HERE / "axiom-report.txt"),
        "allowed_foundational_axioms": sorted(allowed), "custom_axioms": [],
        "source_patches": [], "custom_cryptographic_models": [],
        "whole_word_sbox_bridge": "All eight arbitrary secret64-bit words; actual sub_bytes followed by sub_bytes_nots equals existing root AesSbox.circuit wordOps",
        "inverse_shift_bridge": "Actual inverse1/2/3 equals accepted forward3/2/1 for every Result input; fixed eight-word success and wrong-shape rejection transferred",
        "shape_lemmas": ["sub_bytes_preserves_shape", "nots_preserves_shape"],
        "independent_protocol_or_security_proof_added": False,
        "new_native_artifacts_or_backend_tests_needed": False,
        "existing_numeric_artifact_bridges_reused": True,
        "complete_key_schedule_equivalence_established_here": False,
        "audit_source_sha256": digest(Path(__file__)),
        "checks_source_sha256": digest(HERE / "Checks.lean"),
    }
    (HERE / "proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {len(reports)} actual key-schedule helper bridge endpoints; standard three axioms only.")


if __name__ == "__main__":
    main()
