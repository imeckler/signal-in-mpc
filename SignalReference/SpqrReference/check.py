#!/usr/bin/env python3
"""Audit actual SPQR varint equivalence; no whole-serializer claim is made."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    extraction_path = HERE / "Artifacts/varint/inventory.json"
    extraction = json.loads(extraction_path.read_text())
    assert extraction["charon_exit_code"] == 0 and not extraction["has_errors"]
    assert extraction["counts"]["ordered_decls"] > 0
    assert extraction["source_patches"] == [] and not extraction["hax_cfg_enabled"]
    assert digest(HERE / "extract.py") == extraction["script_sha256"]
    for name, expected in extraction["source_sha256"].items():
        assert digest(ROOT / name) == expected, name
    original = HERE / "Artifacts/varint/spqr.llbc"
    assert digest(original) == "4ca6cf0b654e390018974569b0ed956687aa4a52206cf7354fa2ada91f2829ab"
    selection_path = HERE / "VarintSelected/review.json"
    selection = json.loads(selection_path.read_text())
    assert selection["aeneas_exit_code"] == 0 and selection["remaining_external_templates"] == []
    assert selection["reversible_changes"] == 7 and selection["unchanged_computational_declarations"] == [0, 4]
    assert digest(HERE / "VarintSelected/selected.llbc") == selection["selected_sha256"]
    assert digest(HERE / "VarintSelected/changes.json") == selection["changes_sha256"]
    assert digest(HERE / "select_varint.py") == selection["script_sha256"]
    for name, expected in selection["generated_files"].items():
        assert digest(REFERENCE / name) == expected
    spqr = ROOT / ".deps/libsignal-vendor/spqr"
    vendor = json.loads((spqr / ".cargo-checksum.json").read_text())
    for name, expected in vendor["files"].items():
        assert digest(spqr / name) == expected, name
    # Cargo's checksum map is empty for this git dependency. Independently
    # compare every archived upstream file rather than counting that vacuous
    # check as source verification.
    spqr_archive = ROOT / ".deps/spqr-06959b4.tar.gz"
    assert digest(spqr_archive) == "f8fd4b1356a678fa49bbf4c51801c38d3b53ea800178579bef9ff47321b2058f"
    archive_sources = []
    with tarfile.open(spqr_archive) as bundle:
        for member in bundle.getmembers():
            if member.isfile():
                prefix, name = member.name.split("/", 1)
                assert prefix == "SparsePostQuantumRatchet-06959b4708f9b7b1e94d0f8cc835f3958c077e94"
                path = spqr / name
                assert path.read_bytes() == bundle.extractfile(member).read(), name
                archive_sources.append(path)
    assert len(archive_sources) == 99
    extras = set(p for p in spqr.rglob("*") if p.is_file()) - set(archive_sources)
    assert extras == {spqr / ".cargo-checksum.json"}, extras
    translated = json.loads(original.read_text())["translated"]
    source_text = translated["fun_decls"][0]["item_meta"]["source_text"]
    assert source_text in (spqr / "src/lib.rs").read_text()
    assert "hax_lib::assume!" in source_text
    funs = (HERE / "VarintGenerated/Funs.lean").read_text()
    assert "alloc.vec.Vec.push" in funs and "StepUsize" in funs
    assert "hax" not in funs

    base_report_path = REFERENCE / "ProstEncodingWork/check-report.json"
    base_report = json.loads(base_report_path.read_text())
    for name, expected in base_report["source_sha256"].items():
        assert digest(ROOT / name) == expected, name
    sources = [Path(__file__), HERE / "extract.py", HERE / "select_varint.py", original,
               extraction_path, selection_path, HERE / "VarintSelected/selected.llbc",
               HERE / "VarintSelected/changes.json", HERE / "VarintReference.lean",
               HERE / "VarintCircuit.lean", HERE / "Checks.lean", base_report_path,
               ROOT / ".deps/run-signal-lean.py", *sorted((HERE / "VarintGenerated").glob("*.lean"))]
    sources += [ROOT / name for name in extraction["source_sha256"]]
    sources += [spqr_archive, *archive_sources]
    sources += [REFERENCE / "ProstEncodingWork" / name for name in
                ("Reference.lean", "NatBridge.lean", "VecBridge.lean", "CircuitBridge.lean")]
    root_sources = set()
    def visit(module):
        if not module.startswith("TlsMpc"):
            return
        path = ROOT / (module.replace(".", "/") + ".lean")
        if path in root_sources:
            return
        root_sources.add(path)
        for imported in re.findall(r"^import ([A-Za-z0-9_.]+)", path.read_text(), re.M):
            visit(imported)
    visit("TlsMpc.Signal.Varint64")
    sources += sorted(root_sources)
    archive = REFERENCE / "ProstEncodingWork/AdvanceWork/TranslatorCandidate/aeneas-5b9dcf33.tar.gz"
    assert digest(archive) == "ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453"
    models = sorted((ROOT / ".deps/aeneas-2026-08-27/backends/lean/Aeneas/Std").rglob("*.lean"))
    with tarfile.open(archive) as bundle:
        members = {m.name.split("/", 1)[1]: m for m in bundle.getmembers() if "/" in m.name and m.isfile()}
        for path in models:
            name = str(path.relative_to(ROOT / ".deps/aeneas-2026-08-27"))
            assert bundle.extractfile(members[name]).read() == path.read_bytes(), path
    sources += [archive, *models]
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    modules = ["SpqrReference/VarintGenerated/Types", "SpqrReference/VarintGenerated/Funs",
               "SpqrReference/VarintReference", "SpqrReference/VarintCircuit"]
    subprocess.run(["python3", ".deps/run-signal-lean.py", *modules], cwd=ROOT, check=True)
    cache = Path("/Users/izzy/repos/eco-theorem-combined/.lake/packages")
    paths = [REFERENCE / ".lake/build/lib/lean", ROOT / ".lake/build/lib/lean",
             ROOT / ".deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean"]
    paths += sorted(p / ".lake/build/lib/lean" for p in cache.iterdir() if (p / ".lake/build/lib/lean").is_dir())
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in paths)
    result = subprocess.run(["lean", "SpqrReference/Checks.lean"], cwd=REFERENCE, env=env,
                            text=True, capture_output=True, check=True)
    expected = re.findall(r"^#print axioms (\S+)", (HERE / "Checks.lean").read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert [name for name, _ in found] == expected and len(found) == 21
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, assumptions in found:
        assert not ({a.strip() for a in assumptions.split(",") if a.strip()} - allowed), name
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sources}
    (HERE / "axioms.txt").write_text(result.stdout)
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "checked_endpoints": len(found), "theorems": expected,
        "allowed_foundational_axioms": sorted(allowed), "custom_axioms": [],
        "accepted_reference": False, "independent_selection_review": "pending separate acceptance record",
        "spqr_commit": extraction["spqr_commit"], "versions": extraction["versions"],
        "original_llbc_sha256": digest(original), "selected_llbc_sha256": selection["selected_sha256"],
        "selection_script_sha256": selection["script_sha256"],
        "source_sha256": snapshot,
        "cargo_git_vendor_checksum_entries": len(vendor["files"]),
        "upstream_spqr_archive_sha256": digest(spqr_archive),
        "all_upstream_spqr_files_compared_byte_for_byte": len(archive_sources),
        "only_extra_vendor_file": ".cargo-checksum.json",
        "all_standard_model_files_match_pinned_archive": len(models),
        "axiom_report_sha256": digest(HERE / "axioms.txt"),
        "reference_scope": "Actual spqr1.6.0 encode_varint plus MAX_VARINT_BYTES_LEN, through unchanged official Vec.push/Range/Step models.",
        "unconditional_operation_theorem": "LibSignalReference.Candidate.SpqrVarint.encode_eq_run",
        "numeric_artifact_theorem": "LibSignalReference.Candidate.SpqrVarint.uint64_refines_artifact",
        "guarded_numeric_artifact_theorem": "LibSignalReference.Candidate.SpqrVarint.uint64_guarded_refines_artifact",
        "domain": "All shared U64 values, canonical public widths1..10, and initial buffer.length+10<=Usize.max; shared U32 widening is also covered for widths1..5.",
        "error_behavior": "encode_eq_run retains all Result behavior of actual translated Vec.push calls, without any success or capacity assumption; success/artifact theorems state the capacity bound explicitly.",
        "hax_configuration": "Normal cfg(not(hax)): actual assume! macro expands to unit; no hax proposition is assumed. Pinned dummy macro sources recorded.",
        "standard_model_boundary": "Unchanged upstream scalar/Range/StepUsize/Vec.push models; host allocation behavior is represented by those official models.",
        "additional_trusted_preprocessing": "Seven exact dead Step-metadata edits; independent review and separate acceptance are required.",
        "selection_correctness_mechanized": False,
        "full_spqr_message_serializer_refined": False,
        "full_spqr_state_machine_refined": False,
        "native_mpc_executed_by_this_check": False,
    }
    (HERE / "proof-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Checked 21 actual-SPQR varint endpoints; standard axioms only; full serializer remains unproved.")


if __name__ == "__main__":
    main()
