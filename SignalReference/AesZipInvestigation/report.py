#!/usr/bin/env python3
"""Verify and record the bounded actual-source Zip investigation."""
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest
from AesAddRoundKeyWork.check import audit_sysroot


def main():
    check_sources()
    sysroot = audit_sysroot()
    charon_root = (REFERENCE / PINS["charon"]["directory"]).resolve()
    charon_archive = ROOT / ".deps/charon-4ad295c.tar.gz"
    if digest(charon_archive) != PINS["charon"]["source_archive_sha256"]:
        raise ValueError("Pinned Charon source archive differs")
    charon_files = ["src/options.rs", "src/transform/normalize/partial_monomorphization.rs",
                    "src/ast/type_level/substitute.rs"]
    with tarfile.open(charon_archive) as bundle:
        members = bundle.getnames()
        for name in charon_files:
            member = next(value for value in members if value.endswith("/charon/" + name))
            if bundle.extractfile(member).read() != (charon_root / name).read_bytes():
                raise ValueError(f"Pinned Charon source differs: {name}")
    rust = ROOT / ".deps/rust-nightly-2026-08-18/lib/rustlib/src/rust/library"
    rust_files = ["core/src/iter/adapters/zip.rs", "core/src/iter/traits/iterator.rs",
                  "core/src/slice/iter.rs", "core/src/slice/iter/macros.rs", "core/src/option.rs"]
    with tarfile.open(ROOT / ".deps/rust-src-nightly-2026-08-18.tar.xz") as bundle:
        members = bundle.getnames()
        for name in rust_files:
            member = next(value for value in members if value.endswith("/library/" + name))
            if bundle.extractfile(member).read() != (rust / name).read_bytes():
                raise ValueError(f"Official Rust source differs: {name}")
    baseline = json.loads((HERE / "Artifacts/Baseline/report.json").read_text())
    if (baseline["aeneas_exit_code"], baseline["lean_exit_code"], baseline["minimal_model_mismatch_exit_code"]) != (0, 1, 1):
        raise ValueError("Baseline status differs from diagnosed model failures")
    variants = {}
    expected = {"MutAll": (0, 2), "MutAllZip": (101, None), "MutExceptZip": (101, None),
                "MutExceptConstructor": (0, 2), "MutExceptNext": (101, None)}
    for name, status in expected.items():
        directory = HERE / "Artifacts" / name
        inventory = json.loads((directory / "inventory.json").read_text())
        actual = (inventory["charon_exit_code"], inventory.get("aeneas_exit_code"))
        if actual != status or inventory["source_patches"] or inventory["standard_model_changes"]:
            raise ValueError(f"Variant no longer has the recorded unmodified failure: {name}")
        if actual[0] == 101:
            log = (directory / "charon.log").read_text()
            if "src/ast/type_level/substitute.rs:117" not in log:
                raise ValueError(f"Unexpected Charon failure: {name}")
        else:
            log = (directory / "aeneas.log").read_text()
            if "Name clash detected" not in log or "could not find the information for item 'zip'" not in log:
                raise ValueError(f"Unexpected Aeneas failure: {name}")
        variants[name] = {"charon_exit_code": actual[0], "aeneas_exit_code": actual[1],
                          "inventory_sha256": digest(directory / "inventory.json")}
    mono_log = (HERE / "Artifacts/MonoDiagnostic/aeneas.log").read_text()
    if "Compiler source: llbc/TypesAnalysis.ml, line 229" not in mono_log:
        raise ValueError("Full-monomorphized region diagnostic differs")
    files = {}
    for directory in (HERE / "Artifacts", HERE / "Generated"):
        for path in sorted(directory.rglob("*")):
            if path.is_file():
                files[str(path.relative_to(HERE))] = digest(path)
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "accepted_reference": False, "diagnostic_only": True,
        "whole_round_key_equivalence_established": False,
        "new_theorems": [], "new_computational_models": [], "source_patches": [],
        "standard_model_changes": [], "toolchain_changes": [], "native_backend_execution": False,
        "aeneas_commit": PINS["aeneas"]["commit"], "charon_commit": PINS["charon"]["commit"],
        "rust_commit": sysroot["rust_commit"], "sysroot": sysroot,
        "selected_source": "aes0.9.1 src/soft/fixslice64.rs:1362-1367 add_round_key",
        "aes_source_sha256": digest(ROOT / ".deps/libsignal-vendor/aes-0.9.1/src/soft/fixslice64.rs"),
        "baseline": baseline, "variants": variants,
        "charon_sources_sha256": {name: digest(charon_root / name) for name in charon_files},
        "rust_sources_sha256": {name: digest(rust / name) for name in rust_files},
        "artifacts_sha256": files,
        "investigation_sources_sha256": {path.name: digest(path) for path in HERE.iterdir()
                                          if path.is_file() and path.suffix in (".py", ".lean", ".md")},
        "pinned_ocaml_source_fetch_available": False,
        "ocaml_emitter_locations_from_pinned_executable": True,
        "adjacent_ocaml_explanation": {
            "commit": "7161abf2b8a830d7534f007f2b82e7931e66b921",
            "path": "src/llbc/TypesAnalysis.ml",
            "sha256": digest(ROOT / ".deps/aeneas-7161abf2b8a830d7534f007f2b82e7931e66b921/src/llbc/TypesAnalysis.ml"),
            "exact_pinned_source_equivalence_claimed": False,
        },
        "boundary": "Mutable write-back continuations cannot be discarded; no flag-only accepted translation found among these targeted profiles",
        "proposed_fixes_implemented": False,
    }
    (HERE / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Verified five targeted unaccepted profiles and exact model-failure reproduction; report.json written.")


if __name__ == "__main__":
    main()
