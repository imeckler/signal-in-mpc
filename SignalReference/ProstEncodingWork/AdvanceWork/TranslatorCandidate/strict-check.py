#!/usr/bin/env python3
"""Audit the unaccepted exact-pin translator candidate and its Lean proofs."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[2]
ROOT = REFERENCE.parent
SOURCE = HERE / "aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3"
PREFIX = "ProstEncodingWork/AdvanceWork/TranslatorCandidate/"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / "original-source-manifest.json").read_text())
    patch = json.loads((HERE / "candidate-patch.json").read_text())
    changed = [name for name, expected in manifest["source_sha256"].items()
               if digest(SOURCE / name) != expected]
    assert changed == patch["changed_files"] == ["src/interp/InterpStatements.ml"]
    assert digest(SOURCE / changed[0]) == patch["after_sha256"]
    assert digest(HERE / "never-continuation.patch") == patch["patch_sha256"]
    assert digest(HERE / "apply_candidate.py") == patch["script_sha256"]
    assert digest(HERE / "aeneas-5b9dcf33.tar.gz") == manifest["archive_sha256"]
    pins = json.loads((REFERENCE / "pins.json").read_text())
    assert digest(ROOT / ".deps/charon-4ad295c.tar.gz") == pins["charon"]["source_archive_sha256"]
    assert digest(ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz") == pins["aeneas"]["macos_aarch64_archive_sha256"]
    with tarfile.open(ROOT / ".deps/aeneas-macos-aarch64-2026-08-27.tar.gz") as archive:
        candidates = [m for m in archive.getmembers() if m.isfile() and Path(m.name).name == "aeneas"]
        assert len(candidates) == 1
        release_binary_hash = hashlib.file_digest(archive.extractfile(candidates[0]), "sha256").hexdigest()
    assert digest(ROOT / ".deps/aeneas-2026-08-27/aeneas") == release_binary_hash
    # Read-only comparison of every original OCaml dependency source to its archive.
    charon_source = HERE / "charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8"
    with tarfile.open(ROOT / ".deps/charon-4ad295c.tar.gz") as archive:
        charon_checked = 0
        for member in archive.getmembers():
            relative = Path(*Path(member.name).parts[1:])
            if member.isfile() and (str(relative).startswith("charon-ml/") or
                    str(relative) in ("dune", "dune-project", "charon.opam", "name_matcher_parser.opam")):
                assert hashlib.file_digest(archive.extractfile(member), "sha256").hexdigest() == digest(charon_source / relative)
                charon_checked += 1
    for row in json.loads((HERE / "download-plan.json").read_text())["sources"] + \
            json.loads((HERE / "visitors-download-plan.json").read_text()):
        assert hashlib.new(row["algorithm"], Path(row["path"]).read_bytes()).hexdigest() == row["checksum"]
    packages = (HERE / "installed-packages.txt").read_text()
    assert re.search(r"^visitors\s+20260520$", packages, re.M)
    assert re.search(r"^ppxlib\s+0\.37\.0$", packages, re.M)
    baseline = json.loads((HERE / "baseline-comparison.json").read_text())
    candidate = json.loads((HERE / "candidate-comparison.json").read_text())
    assert candidate["accepted_translator"] is False
    assert baseline["accepted_binary_sha256"] == candidate["accepted_binary_sha256"] == release_binary_hash
    for label, comparison in (("Baseline", baseline), ("Candidate", candidate)):
        assert comparison["binary_sha256"] == digest(HERE / "Bin" / label.lower())
        for target, result in comparison["targets"].items():
            expected = 2 if label == "Baseline" and target in ("Regressions", "Slice") else 0
            assert result["exit_code"] == expected and result["external_templates"] == []
            for filename, expected_hash in result["generated_sha256"].items():
                assert digest(HERE / "Generated" / label / target / filename) == expected_hash
            assert digest(HERE / "Generated" / label / target / "translation.log") == result["log_sha256"]
    for target in ("Varint", "UInt32"):
        assert candidate["targets"][target]["identical_to_baseline_except_import_destination"]
        for path in (HERE / "Generated/Candidate" / target).glob("*.lean"):
            assert path.read_text().replace("Generated.Candidate.", "Generated.Baseline.") == \
                (HERE / "Generated/Baseline" / target / path.name).read_text()
    selection = json.loads((HERE / "SliceSelected/review.json").read_text())
    assert selection["selected_llbc_sha256"] == digest(HERE / "SliceSelected/slice.llbc")
    assert selection["script_sha256"] == digest(HERE / "select_slice.py")
    assert selection["changes_sha256"] == digest(HERE / "SliceSelected/changes.json")
    assert selection["exact_reversible_changes"] == 1 and selection["all_declarations_identical"]
    generated_modules = [PREFIX + f"Generated/Candidate/{target}/{name}"
                         for target in ("Regressions", "Slice", "Varint", "UInt32") for name in ("Types", "Funs")]
    own_modules = [PREFIX + name for name in ("NeverContinuation", "NeverChecks", "RegressionProofs", "SliceProofs", "Checks")]
    lean_paths = [REFERENCE / (module + ".lean") for module in generated_modules + own_modules]
    for path in lean_paths:
        source = re.sub(r"/\-.*?\-/", "", path.read_text(), flags=re.S)
        source = re.sub(r"--[^\n]*", "", source)
        assert not re.search(r"\b(sorry|admit|axiom|native_decide|bv_decide)\b", source), path
    files = lean_paths + [HERE / filename for filename in (
        "check.py", "apply_candidate.py", "compare.py", "select_slice.py", "extract_regressions.py",
        "never-continuation.patch", "candidate-patch.json", "baseline-comparison.json", "candidate-comparison.json",
        "original-source-manifest.json", "dependency-plan.json", "download-plan.json", "visitors-download-plan.json",
        "installed-packages.txt", "SliceSelected/slice.llbc", "SliceSelected/review.json", "SliceSelected/changes.json",
        "RegressionRust/Cargo.toml", "RegressionRust/src/lib.rs", "Regressions/calls.llbc", "Regressions/calls-inventory.json")]
    files += [HERE.parent / "report.json", ROOT / ".deps/run-signal-lean.py",
              ROOT / ".deps/libsignal-vendor/bytes-1.12.0/src/lib.rs",
              ROOT / ".deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_impl.rs",
              ROOT / ".deps/libsignal-v0.106.1/Cargo.lock", REFERENCE / "pins.json"]
    files += [ROOT / ".deps/aeneas-2026-08-27/backends/lean/Aeneas/Std" / name
              for name in ("Primitives.lean", "Slice.lean", "Core/Fmt.lean")]
    snapshot = {str(path.relative_to(ROOT)): digest(path) for path in files}
    audit = subprocess.run([sys.executable, str(ROOT / ".deps/run-signal-lean.py"),
                            *generated_modules, *own_modules], cwd=ROOT, text=True, capture_output=True)
    (HERE / "axiom-report.txt").write_text(audit.stdout + audit.stderr)
    if audit.returncode:
        print(audit.stdout + audit.stderr)
        raise RuntimeError("Candidate generated code or proof audit failed")
    names = []
    for name in ("NeverChecks.lean", "Checks.lean"):
        names += re.findall(r"^#print axioms (\S+)", (HERE / name).read_text(), re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit.stdout)
    assert [name for name, _ in reports] == names and len(names) == 20
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, assumptions in reports:
        assert not ({x.strip() for x in assumptions.split(",") if x.strip()} - allowed), name
    assert snapshot == {str(path.relative_to(ROOT)): digest(path) for path in files}
    independent = REFERENCE / "TranslatorNeverReview/review.json"
    output = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "candidate_only": True, "accepted_translator": False,
        "independent_review_location_if_present": str(independent.relative_to(ROOT)) if independent.exists() else None,
        "checks_passed": True, "checked_theorems": len(names), "theorems": names,
        "allowed_foundational_axioms": sorted(allowed), "custom_axioms": [],
        "axiom_report_sha256": digest(HERE / "axiom-report.txt"),
        "unchanged_original_aeneas_source_files": len(manifest["source_sha256"]) - 1,
        "unchanged_charon_source_files_checked": charon_checked,
        "only_translator_source_change": changed,
        "accepted_release_binary_verified_against_pinned_archive": True,
        "accepted_binary_sha256": release_binary_hash,
        "baseline_binary_sha256": baseline["binary_sha256"],
        "candidate_binary_sha256": candidate["binary_sha256"],
        "candidate_patch_sha256": patch["patch_sha256"],
        "actual_slice_domain": "All Slice U8 and Usize counts; exact suffix on success and actual panic on out-of-range count, including full consumption",
        "never_regression_domain": "Every generic Stops dictionary Result Never, every failure constructor and divergence; guarded success also preserved",
        "existing_codegen_regressions": "Actual varint and UInt32 outputs identical except import destinations",
        "additional_trusted_selection": "One reviewed-candidate code-generation-root filter; every actual declaration and body unchanged",
        "known_independent_negative_control": "Original synthetic spin_stop loop with no breaks remains unsupported by the unchanged loop translator; generic dictionary regressions cover arbitrary Result.div without replacing that loop",
        "standard_models_used": ["Result/Never", "scalar comparisons", "Slice.len", "Slice RangeFrom indexing/drop", "panic formatting"],
        "standard_models_changed": [], "actual_rust_sources_changed": [],
        "remaining_boundaries": [
            "Independent review and explicit acceptance/pinning of this translator candidate and root-only selection.",
            "The Lean proof verifies the continuation equation and emitted operation; it does not mechanize the whole OCaml translator.",
            "Actual Vec reserve/as_slice/put and complete Signal length-delimited message composition remain separate obligations.",
        ],
        "source_sha256": snapshot,
    }
    (HERE / "proof-report.json").write_text(json.dumps(output, indent=2) + "\n")
    print("Checked 20 candidate endpoints: Never fail/div propagation and actual slice success/error, accepted binary unchanged.")


if __name__ == "__main__":
    main()
