#!/usr/bin/env python3
"""Select one closed, unchanged actual nested function from Charon's LLBC.

The full inverse-layout wrapper is not an accepted reference. This additional
trusted extraction selection retains only its actual byte-writing callee,
whose complete signature and body have no declaration dependencies.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest, inventory, name_of


def walk(value):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def fingerprint(data):
    result = copy.deepcopy(data)
    result["translated"]["short_names"].sort(key=lambda item: json.dumps(item["key"], sort_keys=True))
    return hashlib.sha256(json.dumps(result, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def select(before):
    expected_fingerprint = "6b1f920e3287589a294a0e9cd88e59a0134661a7c9eb2b380d6cea9f1129f888"
    if fingerprint(before) != expected_fingerprint:
        raise ValueError("Input differs from the reviewed complete Charon graph")
    if before["has_errors"]:
        raise ValueError("Cannot select from an incomplete Charon translation")
    function = before["translated"]["fun_decls"][1]
    assert name_of(function["item_meta"]) == "aes::soft::fixslice::inv_bitslice::write_reordered"
    assert function["src"] == "Normal" and "Structured" in function["body"]
    calls = []
    for node in walk(function):
        if not isinstance(node, dict):
            continue
        # A closed built-in-only declaration has no user type, function,
        # trait, global, or hash-cons dependency that could be dropped below.
        assert not any(key in node for key in ("HashConsedValue", "Deduplicated", "TraitMethod", "TraitImpl", "TraitRef", "Global", "GlobalRef"))
        assert type(node.get("Regular")) is not int
        if "Adt" in node:
            adt = node["Adt"]
            if isinstance(adt, list):
                assert len(adt) == 3 and adt[1:] == [None, None]
                adt = adt[0]
            assert isinstance(adt, dict) and adt["id"] == {"Builtin": "Tuple"}
        if "Call" in node:
            call = node["Call"]["call"]
            assert call["func"]["Regular"]["kind"] == {
                "Fun": {"Builtin": {"Index": {"is_array": False, "mutability": "Mut", "is_range": False}}}}
            assert not call["func"]["Regular"]["generics"]["trait_refs"]
            calls.append(call)
    assert len(calls) == 8
    after = copy.deepcopy(before)
    translated = after["translated"]
    changes = []
    for kind in ("type_decls", "fun_decls", "global_decls", "trait_decls", "trait_impls"):
        for index, declaration in enumerate(translated[kind]):
            if declaration is not None and not (kind == "fun_decls" and index == 1):
                changes.append({"path": ["translated", kind, index], "before": copy.deepcopy(declaration), "after": None})
                translated[kind][index] = None
    old_order = translated["ordered_decls"]
    translated["ordered_decls"] = [{"Fun": {"NonRec": 1}}]
    changes.append({"path": ["translated", "ordered_decls"], "before": old_order, "after": translated["ordered_decls"]})
    restored = copy.deepcopy(after)
    for change in changes:
        slot = restored
        for key in change["path"][:-1]:
            slot = slot[key]
        slot[change["path"][-1]] = change["before"]
    assert restored == before
    assert translated["fun_decls"][1] == function
    return after, changes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--canonical", action="store_true")
    args = parser.parse_args()
    check_sources()
    original = HERE / "Artifacts/InvBitsliceScoped/aes_inverse_layout.llbc"
    before = json.loads(original.read_text())
    after, changes = select(before)
    destination = (REFERENCE / "Extraction/aes-inverse-write-selection") if args.canonical else (HERE / "Artifacts/WriteReordered")
    destination.mkdir(parents=True, exist_ok=True)
    selected = (REFERENCE / "Extraction/libsignal_aes_inverse_write.llbc") if args.canonical else (destination / "selected.llbc")
    selected.write_text(json.dumps(after, separators=(",", ":")) + "\n")
    change_file = destination / "selection-changes.json"
    change_file.write_text(json.dumps(changes, separators=(",", ":")) + "\n")
    aeneas = (REFERENCE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    if PINS["aeneas"]["release"] not in subprocess.check_output([str(aeneas), "-version"], text=True):
        raise ValueError("Aeneas version differs from the pinned release")
    generated = (REFERENCE / "LibSignalReference/Generated/AesInverseWrite") if args.canonical else (HERE / "Generated/WriteReordered")
    generated.mkdir(parents=True, exist_ok=True)
    for previous in generated.glob("*.lean"):
        previous.unlink()
    command = [str(aeneas), "-backend", "lean", str(selected), "-dest", str(REFERENCE),
               "-subdir", "/" + str(generated.relative_to(REFERENCE)), "-split-files",
               "-namespace", "RustCryptoAesInverseWrite", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_only": True, "accepted_reference": False,
              "additional_trusted_declaration_selection": True, "selection_correctness_mechanized": False,
              "original_llbc_sha256": digest(original), "original_fingerprint": fingerprint(before),
              "selected_llbc_sha256": digest(selected), "selected_function_id": 1,
              "selected_function_name": name_of(after["translated"]["fun_decls"][1]["item_meta"]),
              "selected_declaration_identical": True, "closed_builtin_only_signature_and_body": True,
              "builtin_mutable_index_operations": 8, "change_count": len(changes),
              "reversible_changes_file": str(change_file.relative_to(REFERENCE)),
              "reversible_changes_sha256": digest(change_file),
              "independent_review_file": "AesKeyScheduleWork/inverse-writer-selection-review.json",
              "all_other_json_values_identical": True, "source_patches": [],
              "aeneas_exit_code": result.returncode,
              "generated_files": {str(path.relative_to(REFERENCE)): digest(path) for path in sorted(generated.glob("*.lean"))},
              "inventory": inventory(selected), "selection_script_sha256": digest(Path(__file__)),
              "full_inv_bitslice_refinement_complete": False}
    review_path = destination / "review.json"
    review_path.write_text(json.dumps(report, indent=2) + "\n")
    if args.canonical:
        original_inventory = HERE / "Artifacts/InvBitsliceScoped/inventory.json"
        canonical_report = json.loads(original_inventory.read_text())
        canonical_report.update(inventory(selected))
        canonical_report.update({
            "profile": "aes_inverse_write",
            "candidate_reference": False,
            "accepted_reference": False,
            "proof_status": "run canonical Lean proof checks after integration",
            "generated_files": report["generated_files"],
            "aeneas_command": [part.replace(str(ROOT), "$WORKSPACE") for part in command],
            "aeneas_exit_code": result.returncode,
            "source_llbc_file": str(original.relative_to(REFERENCE)),
            "source_llbc_sha256": digest(original),
            "source_llbc_canonical_fingerprint": fingerprint(before),
            "source_inventory_file": str(original_inventory.relative_to(REFERENCE)),
            "source_inventory_sha256": digest(original_inventory),
            "selection_review_file": str(review_path.relative_to(REFERENCE)),
            "selection_review_sha256": digest(review_path),
            "selection_script_file": str(Path(__file__).relative_to(REFERENCE)),
            "selection_script_sha256": digest(Path(__file__)),
            "additional_trusted_declaration_selection": True,
            "selection_correctness_mechanized": False,
            "independent_review_file": report["independent_review_file"],
            "independent_review_sha256": digest(REFERENCE / report["independent_review_file"]),
            "full_inv_bitslice_refinement_complete": False,
        })
        (REFERENCE / "Extraction/aes_inverse_write.json").write_text(json.dumps(canonical_report, indent=2) + "\n")
    print(f"Selected actual nested writer; Aeneas exit={result.returncode}; full wrapper remains unproved.")
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
