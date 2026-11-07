#!/usr/bin/env python3
"""Check actual Prost/bytes provenance and the uint32 MPC refinement proofs."""
from datetime import datetime, timezone
import copy
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
spec = importlib.util.spec_from_file_location("prost_extract", HERE / "extract.py")
extraction = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extraction)
digest = extraction.digest


def walk(value):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def check_selection():
    independent_path = REFERENCE / "prost-selection-independent-review.json"
    independent = json.loads(independent_path.read_text())
    if (independent.get("checks_passed") is not True or
            independent.get("exact_reversible_changes") != 11 or
            independent.get("full_original_bodies_unchanged") != [0, 7] or
            independent.get("retained_called_buffer_fields") != ["put_slice", "put_u8"]):
        raise ValueError("The independent selection review does not cover this graph")
    for filename, expected in independent["sha256"].items():
        if digest(ROOT / filename) != expected:
            raise ValueError(f"Reviewed provenance changed: {filename}")
    original_path = HERE / "Artifacts/EncodeBody/prost_encoding.llbc"
    selected_path = HERE / "Artifacts/EncodeSelected/selected.llbc"
    changes_path = HERE / "Artifacts/EncodeSelected/changes.json"
    before = json.loads(original_path.read_text())
    after = json.loads(selected_path.read_text())
    changes = json.loads(changes_path.read_text())
    replay = copy.deepcopy(before)
    for change in changes:
        target = replay
        for key in change["path"][:-1]:
            target = target[key]
        if target[change["path"][-1]] != change["before"]:
            raise ValueError("Selection replay precondition differs")
        target[change["path"][-1]] = change["after"]
    if replay != after:
        raise ValueError("Selection contains unreported changes")
    report = json.loads((HERE / "Artifacts/EncodeSelected/review.json").read_text())
    if report["aeneas_exit_code"] or report["remaining_external_templates"]:
        raise ValueError("The selected actual encoder has unresolved generated templates")
    for filename, expected in report["generated_files"].items():
        if digest(REFERENCE / filename) != expected:
            raise ValueError(f"Selected generated reference changed: {filename}")
    return before, report, [independent_path, original_path, selected_path, changes_path,
                           HERE / "Artifacts/EncodeSelected/review.json"]


def check_vec(encoder):
    manifest_path = HERE / "Artifacts/VecPutSlice/inventory.json"
    manifest = json.loads(manifest_path.read_text())
    llbc_path = HERE / "Artifacts/VecPutSlice/prost_encoding.llbc"
    if (manifest["charon_exit_code"] or manifest["aeneas_exit_code"] or
            manifest["has_errors"] or digest(llbc_path) != manifest["llbc_sha256"]):
        raise ValueError("Actual Vec reference extraction is incomplete or changed")
    for filename, expected in manifest["generated_files"].items():
        if digest(REFERENCE / filename) != expected:
            raise ValueError(f"Vec generated reference changed: {filename}")
    tr = json.loads(llbc_path.read_text())["translated"]
    implementation = tr["trait_impls"][0]
    if (implementation["methods"][5]["skip_binder"]["id"] != 0 or
            implementation["methods"][7]["skip_binder"]["id"] != 7):
        raise ValueError("Actual Vec BufMut method selection differs")
    override = tr["fun_decls"][0]
    if (override["src"]["TraitImpl"]["item_id"] != 5 or
            override["src"]["TraitImpl"]["reuses_default"] is not False or
            tr["fun_decls"][7]["src"]["TraitDefault"]["item_id"] != 7):
        raise ValueError("Actual buffer override/default provenance differs")
    bytes_source = (ROOT / ".deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_mut.rs").read_text()
    if override["item_meta"]["source_text"] not in bytes_source:
        raise ValueError("The Vec override is not the pinned actual source")
    core_default = encoder["translated"]["fun_decls"][7]
    vec_default = tr["fun_decls"][7]
    if (vec_default["item_meta"]["source_text"] not in bytes_source or
            core_default["item_meta"]["name"] != vec_default["item_meta"]["name"]):
        raise ValueError("The inherited actual put_u8 default has different source identity")
    # The cross-crate default has no source_text in Charon; use its exact
    # qualified name and body source range, bound to the pinned bytes source.
    # Local MIR contains an extra borrow-check FakeRead, so raw-body identity
    # between the local and cross-crate extraction is deliberately not claimed.
    for endpoint in ["beg", "end"]:
        if core_default["body"]["Structured"]["span"]["data"][endpoint] != \
                vec_default["body"]["Structured"]["span"]["data"][endpoint]:
            raise ValueError("The inherited default's body source range differs")
    expected_ordered = [{"TraitDecl": {"NonRec": 2}}, {"Fun": {"NonRec": 191}},
                        {"TraitImpl": {"NonRec": 1}}, {"Type": {"NonRec": 1}},
                        {"Type": {"NonRec": 0}}, {"Fun": {"NonRec": 51}}, {"Fun": {"NonRec": 0}}]
    if tr["ordered_decls"] != expected_ordered:
        raise ValueError("The selected Vec emission graph differs")
    calls = [node["Call"]["call"]["func"]["Regular"]["kind"]
             for node in walk(override["body"]) if isinstance(node, dict) and "Call" in node]
    if calls != [{"Fun": {"Regular": 51}}]:
        raise ValueError("The actual Vec override calls an unexpected operation")
    # The selected generated body contains only the accepted official Vec
    # extension model, with the official scalar-byte Clone dictionary.
    generated = (HERE / "Generated/VecPutSlice/Funs.lean").read_text()
    if len(re.findall(r"^def ", generated, re.M)) != 1 or \
            "alloc.vec.Vec.extend_from_slice core.clone.CloneU8 self src" not in generated:
        raise ValueError("Unexpected computational dependency in selected Vec output")
    return manifest, [manifest_path, llbc_path]


def main():
    extraction.canonical.check_sources()
    for filename, expected in extraction.SOURCE_HASHES.items():
        if digest(ROOT / filename) != expected:
            raise ValueError(f"Pinned source differs: {filename}")
    lock = tomllib.loads((ROOT / ".deps/libsignal-v0.106.1/Cargo.lock").read_text())
    for package, version in [("prost", "0.14.4"), ("bytes", "1.12.0")]:
        entry = next(row for row in lock["package"] if row["name"] == package and row["version"] == version)
        checksum = json.loads((ROOT / f".deps/libsignal-vendor/{package}-{version}/.cargo-checksum.json").read_text())
        if entry["checksum"] != checksum["package"]:
            raise ValueError(f"Locked vendor package mismatch: {package}")
    before, selected, provenance = check_selection()
    vec, vec_provenance = check_vec(before)
    provenance += vec_provenance
    modules = ["Reference", "NatBridge", "VecBridge", "CircuitBridge", "Checks"]
    own = [HERE / (module + ".lean") for module in modules]
    generated = [HERE / "Generated" / kind / name for kind in ["EncodeSelected", "VecPutSlice"]
                 for name in ["Types.lean", "Funs.lean"]]
    for directory in [HERE / "Generated/EncodeSelected", HERE / "Generated/VecPutSlice"]:
        if list(directory.glob("*_Template.lean")):
            raise ValueError("Unresolved generated template in an accepted selected module")
    for path in own[:-1] + generated:
        source = re.sub(r"/\-.*?\-/", "", path.read_text(), flags=re.S)
        source = re.sub(r"--[^\n]*", "", source)
        if re.search(r"\b(sorry|admit|axiom|native_decide|bv_decide)\b", source):
            raise ValueError(f"Unaccepted proof or model declaration: {path}")
    sources = own + generated + provenance + [HERE / name for name in
        ["extract.py", "inspect_metadata.py", "select_buffer.py", "check.py"]]
    sources += [ROOT / filename for filename in extraction.SOURCE_HASHES]
    sources += [ROOT / name for name in ["TlsMpc/Signal/Varint.lean", "TlsMpc/Signal/OpenResult.lean",
        "TlsMpc/ByteAuth.lean", "TlsMpc/Sha256.lean", "TlsMpc/ByteCircuit.lean", "TlsMpc/AigExport.lean",
        ".deps/run-signal-lean.py"]]
    sources += [ROOT / ".deps/aeneas-2026-08-27/backends/lean/Aeneas/Std" / name for name in
                ["Vec.lean", "Slice.lean", "Core/Iter.lean", "Scalar/Bitwise.lean", "Scalar/Casts.lean"]]
    snapshot = {str(path.relative_to(ROOT)): digest(path) for path in sources}
    subprocess.run(["lake", "build", "TlsMpc.Signal.Varint"], cwd=ROOT, check=True)
    build_modules = [f"ProstEncodingWork/Generated/{kind}/{name}" for kind in ["EncodeSelected", "VecPutSlice"]
                     for name in ["Types", "Funs"]]
    build_modules += ["ProstEncodingWork/" + module for module in modules]
    audit = subprocess.run([sys.executable, str(ROOT / ".deps/run-signal-lean.py"), *build_modules],
                           cwd=ROOT, text=True, capture_output=True)
    (HERE / "axiom-report.txt").write_text(audit.stdout + audit.stderr)
    if audit.returncode:
        print(audit.stdout + audit.stderr)
        raise RuntimeError("The actual varint circuit refinement failed to build")
    names = re.findall(r"^#print axioms (\S+)", (HERE / "Checks.lean").read_text(), re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit.stdout)
    if [name for name, _ in reports] != names:
        raise ValueError("Missing or unexpected axiom audit endpoint")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, entries in reports:
        if {entry.strip() for entry in entries.split(",") if entry.strip()} - allowed:
            raise ValueError(f"Unaccepted theorem assumptions: {name}")
    if snapshot != {str(path.relative_to(ROOT)): digest(path) for path in sources}:
        raise ValueError("Sources changed during the audit")
    report = {"checked_at_utc": datetime.now(timezone.utc).isoformat(),
              "kind": "actual_prost_varint_to_numeric_mpc_refinement",
              "accepted_selected_reference": True, "source_sha256": snapshot,
              "checked_theorems": len(names), "theorems": names,
              "allowed_foundational_axioms": sorted(allowed), "custom_axioms": [],
              "axiom_report_sha256": digest(HERE / "axiom-report.txt"),
              "selected_functions": ["prost0.14.4 encoding::varint::encode_varint",
                                     "bytes1.12.0 BufMut::put_u8 default",
                                     "bytes1.12.0 BufMut for Vec<u8>::put_slice"],
              "actual_vec_dispatch_checked": {"implementation_id": 0, "put_slice_slot": 5,
                                              "put_slice_function": 0, "put_u8_slot": 7,
                                              "put_u8_default_function": 7},
              "buffer_contract": "Discharged using the actual selected Vec override and default, under the official Aeneas Vec model",
              "domain": {"generic_loop": "All uint64 values and all supplied buffer Result behaviors",
                         "concrete_vec_success": "buf.length + 10 <= Usize.max",
                         "counter_circuit": "All uint32 values; public width1..5 passing canonicalGroups",
                         "output": "Exact appended bytes; every numeric MPC output bit proved equal"},
              "additional_trusted_preprocessing": "Independently reviewed11-change metadata/code-generation-root selection; no computational body changed",
              "selection_correctness_mechanized": False,
              "remaining_boundaries": ["Whole SignalMessage::new and derive-generated Prost field composition",
                                       "Scalar encoded_len_varint NonZeroU64 dependencies remain unaccepted diagnostic templates",
                                       "Pinned extraction and official standard models are trusted",
                                       "Native serialization, backend adapter and MPC execution remain unverified"],
              "backend_compiled_here": False, "native_mpc_executed": False,
              "extraction_rerun_by_this_audit": False}
    (HERE / "check-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {len(names)} endpoints: actual Prost/Vec append equals the numeric uint32 circuit.")


if __name__ == "__main__":
    main()
