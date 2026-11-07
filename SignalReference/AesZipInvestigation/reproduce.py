#!/usr/bin/env python3
"""Reproduce the model mismatch without changing Rust or standard models."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest
from AesAddRoundKeyWork.inspect_metadata import select
from AesAddRoundKeyWork.check import audit_sysroot


def main():
    check_sources()
    sysroot = audit_sysroot()
    original = REFERENCE / "AesAddRoundKeyWork/Artifacts/IncludeXor/add_round_key.llbc"
    prior = json.loads((REFERENCE / "AesAddRoundKeyWork/proof-check.json").read_text())
    if digest(original) != prior["reference"]["original_llbc_sha256"]:
        raise ValueError("The actual previously audited extraction changed")
    selected, changes = select(json.loads(original.read_text()), "IncludeXor")
    dest = HERE / "Artifacts/Baseline"
    dest.mkdir(parents=True, exist_ok=True)
    llbc = dest / "selected.llbc"
    llbc.write_text(json.dumps(selected, separators=(",", ":")) + "\n")
    (dest / "selection-changes.json").write_text(json.dumps(changes, indent=2) + "\n")
    tool = (REFERENCE / PINS["aeneas"]["directory"]).resolve()
    if PINS["aeneas"]["release"] not in subprocess.check_output([str(tool / "aeneas"), "-version"], text=True):
        raise ValueError("Aeneas pin differs")
    archive = ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz"
    if digest(archive) != PINS["aeneas"]["macos_aarch64_archive_sha256"]:
        raise ValueError("Aeneas official archive differs")
    models = ["Aeneas/Std/Core/Iter.lean", "Aeneas/Std/SliceIter.lean"]
    with tarfile.open(archive) as bundle:
        for name in models:
            if bundle.extractfile("backends/lean/" + name).read() != (tool / "backends/lean" / name).read_bytes():
                raise ValueError(f"Pinned model changed: {name}")
    generated = HERE / "Generated/Baseline"
    generated.mkdir(parents=True, exist_ok=True)
    command = [str(tool / "aeneas"), "-backend", "lean", str(llbc), "-dest", str(REFERENCE),
               "-subdir", "/AesZipInvestigation/Generated/Baseline", "-split-files",
               "-namespace", "RustCryptoAesZipDiagnostic", "-warnings-as-errors", "-no-progress-bar",
               "-print-error-emitters"]
    with (dest / "aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError("Expected baseline Aeneas emission to succeed before the Lean type mismatch")
    paths = [HERE / "LeanBuild", tool / "backends/lean/.lake/build/lib/lean"]
    packages = Path("/Users/izzy/repos/eco-theorem-combined/.lake/packages")
    package_revisions = {}
    for package in json.loads((tool / "backends/lean/lake-manifest.json").read_text())["packages"]:
        directory = packages / package["name"]
        revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=directory, text=True).strip()
        if revision != package["rev"]:
            raise ValueError(f"Proof package pin changed: {directory}")
        package_revisions[package["name"]] = revision
        if (directory / ".lake/build/lib/lean").is_dir():
            paths.append(directory / ".lake/build/lib/lean")
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    target = paths[0] / "AesZipInvestigation/Generated/Baseline/Types.olean"
    target.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["lean", "-o", str(target), "AesZipInvestigation/Generated/Baseline/Types.lean"],
                   cwd=REFERENCE, env=env, check=True)
    result = subprocess.run(["lean", "AesZipInvestigation/Generated/Baseline/Funs.lean"],
                            cwd=REFERENCE, env=env, text=True, capture_output=True)
    (dest / "lean.log").write_text(result.stdout + result.stderr)
    if result.returncode != 1 or "IteratorIterMut.next" not in result.stdout or "Type mismatch" not in result.stdout:
        raise RuntimeError("Actual generated loop no longer has the expected diagnosed mismatch; inspect it")
    minimal = subprocess.run(["lean", "AesZipInvestigation/ModelSignatureMismatch.lean"],
                             cwd=REFERENCE, env=env, text=True, capture_output=True)
    (dest / "minimal-lean.log").write_text(minimal.stdout + minimal.stderr)
    if minimal.returncode != 1 or "IteratorIterMut.next" not in minimal.stdout or "Type mismatch" not in minimal.stdout:
        raise RuntimeError("The minimal official-model signature mismatch changed")
    report = {
        "accepted_reference": False, "diagnostic_only": True,
        "source_patches": [], "standard_model_changes": [], "new_axioms": [],
        "source_llbc_sha256": digest(original), "selected_llbc_sha256": digest(llbc),
        "existing_selector_sha256": digest(REFERENCE / "AesAddRoundKeyWork/inspect_metadata.py"),
        "retained_computational_declarations_unchanged": True,
        "unused_zip_dictionary_slots_removed": len(changes),
        "selection_changes_sha256": digest(dest / "selection-changes.json"),
        "aeneas_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
        "aeneas_exit_code": 0, "lean_exit_code": result.returncode,
        "minimal_model_mismatch_exit_code": minimal.returncode,
        "generated_files_sha256": {str(p.relative_to(REFERENCE)): digest(p) for p in sorted(generated.glob("*.lean"))},
        "official_model_sources_sha256": {name: digest(tool / "backends/lean" / name) for name in models},
        "proof_package_revisions": package_revisions, "sysroot": sysroot,
        "reproduction_script_sha256": digest(Path(__file__)),
        "sysroot_audit_helper_sha256": digest(REFERENCE / "AesAddRoundKeyWork/check.py"),
    }
    (dest / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Reproduced actual generated-loop and minimal official-model type failures; no accepted reference.")


if __name__ == "__main__":
    main()
