#!/usr/bin/env python3
"""Audit the actual SHA core initializer and constructor/compression composition."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tomllib

from select_initial import select, FUNCTIONS, TYPES, GLOBALS

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    extraction_path = HERE / "Artifacts/core_new_closed/inventory.json"
    extraction = json.loads(extraction_path.read_text())
    assert extraction["charon_exit_code"] == 0 and not extraction["has_errors"]
    assert extraction["counts"]["ordered_decls"] == 10
    assert extraction["source_patches"] == [] and extraction["custom_models"] == []
    assert digest(HERE / "extract.py") == extraction["script_sha256"]
    for name, expected in extraction["source_sha256"].items():
        assert digest(ROOT / name) == expected, name
    original = HERE / "Artifacts/core_new_closed/sha_wrapper.llbc"
    before = json.loads(original.read_text())
    after, changes, excluded_refs = select(before)
    selected_path = HERE / "InitialSelected/selected.llbc"
    assert json.loads(selected_path.read_text()) == after
    changes_path = HERE / "InitialSelected/changes.json"
    assert json.loads(changes_path.read_text()) == changes and len(changes) == 3
    selection_path = HERE / "InitialSelected/review.json"
    selection = json.loads(selection_path.read_text())
    assert selection["aeneas_exit_code"] == 0 and selection["remaining_external_templates"] == []
    assert selection["unchanged_computational_declarations"] == sorted(FUNCTIONS)
    assert selection["unchanged_type_declarations"] == sorted(TYPES)
    assert selection["unchanged_globals"] == sorted(GLOBALS)
    assert selection["excluded_non_emitted_references_to_removed_metadata"] == excluded_refs
    for path, field in ((original, "original_llbc_sha256"), (selected_path, "selected_llbc_sha256"),
                        (HERE / "select_initial.py", "selection_script_sha256"), (changes_path, "changes_sha256")):
        assert digest(path) == selection[field]
    for name, expected in selection["generated_files"].items():
        assert digest(REFERENCE / name) == expected, name
    source = ROOT / ".deps/libsignal-vendor/sha2-0.11.0/src/block_api.rs"
    for index in (0, 161):
        assert before["translated"]["fun_decls"][index]["item_meta"]["source_text"] in source.read_text()

    # Verify the registry archives themselves against the lockfile, then every
    # archived file byte-for-byte. The checksum manifest alone is not the pin.
    cargo_lock = ROOT / ".deps/libsignal-v0.106.1/Cargo.lock"
    lock = tomllib.loads(cargo_lock.read_text())
    registry_sources = []
    archive_report = {}
    for name, dependency in extraction["dependencies"].items():
        version = dependency["version"]
        package = next(p for p in lock["package"] if p["name"] == name and p["version"] == version)
        archive = ROOT / ".deps/libsignal-crates" / f"{name}-{version}.crate"
        assert digest(archive) == package["checksum"] == dependency["package_sha256"]
        directory = ROOT / ".deps/libsignal-vendor" / f"{name}-{version}"
        matched = []
        with tarfile.open(archive) as bundle:
            for member in bundle.getmembers():
                if member.isfile():
                    prefix, filename = member.name.split("/", 1)
                    assert prefix == f"{name}-{version}"
                    path = directory / filename
                    assert bundle.extractfile(member).read() == path.read_bytes(), path
                    matched.append(path)
        extras = {p for p in directory.rglob("*") if p.is_file()} - set(matched)
        assert extras == {directory / ".cargo-checksum.json"}, extras
        registry_sources += [archive, *matched, *extras]
        archive_report[name] = {"version": version, "sha256": digest(archive),
                                "upstream_files_compared_byte_for_byte": len(matched),
                                "only_extra_vendor_file": ".cargo-checksum.json"}

    proof_sources = set()
    def visit(module):
        if module.startswith("TlsMpc"):
            path = ROOT / (module.replace(".", "/") + ".lean")
        elif module.startswith(("LibSignalReference", "Sha256WrapperWork")):
            path = REFERENCE / (module.replace(".", "/") + ".lean")
        else:
            return
        if path in proof_sources:
            return
        assert path.exists(), path
        proof_sources.add(path)
        for child in re.findall(r"^import ([A-Za-z0-9_.]+)", path.read_text(), re.M):
            visit(child)
    visit("Sha256WrapperWork.Initial")
    archive = REFERENCE / "ProstEncodingWork/AdvanceWork/TranslatorCandidate/aeneas-5b9dcf33.tar.gz"
    assert digest(archive) == "ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453"
    models = sorted((ROOT / ".deps/aeneas-2026-08-27/backends/lean/Aeneas/Std").rglob("*.lean"))
    with tarfile.open(archive) as bundle:
        members = {m.name.split("/", 1)[1]: m for m in bundle.getmembers() if "/" in m.name and m.isfile()}
        for path in models:
            name = str(path.relative_to(ROOT / ".deps/aeneas-2026-08-27"))
            assert bundle.extractfile(members[name]).read() == path.read_bytes(), path
    sources = set(registry_sources + models) | proof_sources | {
        Path(__file__), HERE / "extract.py", HERE / "select_initial.py", HERE / "Checks.lean",
        original, extraction_path, selected_path, changes_path, selection_path,
        ROOT / ".deps/run-signal-lean.py", cargo_lock, archive,
        ROOT / ".deps/aeneas-2026-08-27/aeneas",
        ROOT / ".deps/charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8/charon/target/release/charon",
        ROOT / ".deps/rust-nightly-2026-08-18/bin/rustc",
    }
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sorted(sources)}
    subprocess.run(["python3", ".deps/run-signal-lean.py", "Sha256WrapperWork/InitialGenerated/Types",
                    "Sha256WrapperWork/InitialGenerated/Funs", "Sha256WrapperWork/Initial"], cwd=ROOT, check=True)
    cache = Path("/Users/izzy/repos/eco-theorem-combined/.lake/packages")
    paths = [REFERENCE / ".lake/build/lib/lean", ROOT / ".lake/build/lib/lean",
             ROOT / ".deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean"]
    paths += sorted(p / ".lake/build/lib/lean" for p in cache.iterdir() if (p / ".lake/build/lib/lean").is_dir())
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in paths)
    result = subprocess.run(["lean", "Sha256WrapperWork/Checks.lean"], cwd=REFERENCE, env=env,
                            text=True, capture_output=True, check=True)
    expected = re.findall(r"^#print axioms (\S+)", (HERE / "Checks.lean").read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert [name for name, _ in found] == expected and len(found) == 8
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, assumptions in found:
        assert not ({a.strip() for a in assumptions.split(",") if a.strip()} - allowed), name
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sorted(sources)}
    (HERE / "axioms.txt").write_text(result.stdout)
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "checked_endpoints": len(found), "theorems": expected,
        "allowed_foundational_axioms": sorted(allowed), "custom_axioms": [],
        "accepted_reference": False, "independent_selection_review": "pending separate acceptance record",
        "versions": extraction["versions"], "rustflags": extraction["rustflags"],
        "original_llbc_sha256": digest(original), "selected_llbc_sha256": digest(selected_path),
        "selection_script_sha256": digest(HERE / "select_initial.py"),
        "source_sha256": snapshot, "registry_archives": archive_report,
        "all_standard_model_files_match_pinned_archive": len(models),
        "axiom_report_sha256": digest(HERE / "axioms.txt"),
        "reference_scope": "Actual sha2 0.11.0 Sha256VarCore::new, including sizes28/32/invalid; constructor followed by already-accepted actual compact compress_u32 on sixteen shared words.",
        "numeric_artifact_theorem": "LibSignalReference.Candidate.Sha256Wrapper.initial_compression_refines_artifact",
        "domain": "All sixteen input U32 words and all secret assignments representing them. Constructor size32 is public; separate exact constructor theorem covers every Usize and actual invalid-size result.",
        "standard_model_boundary": "Unchanged upstream array/scalar/Result models; existing accepted compression proof supplies the compact round semantics.",
        "additional_trusted_preprocessing": "Three exact unused ArraySize implementation metadata deletions; ordered roots unchanged; non-emitted references explicitly listed in selection review.",
        "selection_correctness_mechanized": False,
        "source_patches": [], "custom_models": [],
        "full_sha256_digest_wrapper_refined": False,
        "actual_update_core_refined": False, "actual_finalize_core_refined": False,
        "actual_block_buffer_refined": False, "native_mpc_executed_by_this_check": False,
    }
    (HERE / "proof-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Checked eight actual SHA initializer/compression endpoints; standard axioms only; wrappers remain unproved.")


if __name__ == "__main__":
    main()
