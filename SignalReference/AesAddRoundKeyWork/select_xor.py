#!/usr/bin/env python3
"""Select the two actual closed u64 XOR-assignment functions from the graph."""

import copy
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest, inventory, name_of
from MetadataWork.trim_step_metadata import walk, reviewed_input_fingerprint

INPUT_FINGERPRINT = "300bd089be43fed9094af3ef359a0fdb92ded0d907c0a09353de40bc240a3c5c"
KEEP = {"type_decls": set(), "fun_decls": {6, 121}, "global_decls": set(),
        "trait_decls": {21}, "trait_impls": {5, 7}}


def select(before):
    if before["has_errors"] or reviewed_input_fingerprint(before) != INPUT_FINGERPRINT:
        raise ValueError("Actual XOR-assignment dependency graph differs")
    data = copy.deepcopy(before)
    tr = data["translated"]
    for function in (6, 121):
        assert name_of(tr["fun_decls"][function]["item_meta"]) == "core::ops::bit::{impl}::bitxor_assign"
        assert "Structured" in tr["fun_decls"][function]["body"]
    assert name_of(tr["trait_decls"][21]["item_meta"]) == "core::ops::bit::BitXorAssign"
    assert tr["trait_impls"][5]["impl_trait"]["id"] == 21
    assert tr["trait_impls"][7]["impl_trait"]["id"] == 21
    for impl, global_id in ((5, 6), (7, 7)):
        assert tr["trait_impls"][impl]["vtable"]["id"] == global_id
        assert tr["global_decls"][global_id] is None
    for kind, indices in KEEP.items():
        for index in indices:
            for node in walk(tr[kind][index]):
                if not isinstance(node, dict):
                    continue
                assert not any(key in node for key in ("HashConsedValue", "Deduplicated", "Global", "GlobalRef"))
                if isinstance(node.get("Regular"), int):
                    assert node["Regular"] == 121
                if "TraitMethod" in node:
                    assert node["TraitMethod"] == [21, 0]
                if "TraitImpl" in node:
                    reference = node["TraitImpl"]
                    if "id" in reference:
                        assert reference["id"] in (5, 7)
                    else:
                        assert reference["impl_ref"]["id"] in (5, 7)
                        assert reference["trait_ref"]["id"] == 21
                if "Adt" in node:
                    adt = node["Adt"]
                    if type(adt) is int:
                        # Charon already omitted this unused trait-vtable type.
                        assert node is tr["trait_decls"][21]["vtable"]["id"]
                        assert adt == 45 and tr["type_decls"][45] is None
                        continue
                    if adt == [None, []]:
                        continue  # The zero-field unit aggregate constant.
                    if isinstance(adt, list):
                        assert adt[1:] == [None, None]
                        adt = adt[0]
                    assert adt["id"] == {"Builtin": "Tuple"}
                if "trait_decl_ref" in node:
                    assert node["trait_decl_ref"]["skip_binder"]["id"] == 21
                if "impl_trait" in node:
                    assert node["impl_trait"]["id"] == 21
    changes = []
    for kind, indices in KEEP.items():
        for index, declaration in enumerate(tr[kind]):
            if declaration is not None and index not in indices:
                changes.append({"path": ["translated", kind, index], "before": declaration, "after": None})
                tr[kind][index] = None
    old_order = tr["ordered_decls"]
    tr["ordered_decls"] = [entry for entry in old_order if entry in
                            ({"Fun": {"NonRec": 121}}, {"Fun": {"NonRec": 6}})]
    assert tr["ordered_decls"] == [{"Fun": {"NonRec": 121}}, {"Fun": {"NonRec": 6}}]
    changes.append({"path": ["translated", "ordered_decls"], "before": old_order, "after": tr["ordered_decls"]})
    restored = copy.deepcopy(data)
    for change in changes:
        slot = restored
        for key in change["path"][:-1]:
            slot = slot[key]
        slot[change["path"][-1]] = change["before"]
    assert restored == before
    return data, changes


def main():
    check_sources()
    original = HERE / "Artifacts/IncludeXor/add_round_key.llbc"
    data, changes = select(json.loads(original.read_text()))
    destination = HERE / "Artifacts/XorAssign"
    destination.mkdir(exist_ok=True)
    selected = destination / "selected.llbc"
    selected.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    changes_file = destination / "selection-changes.json"
    changes_file.write_text(json.dumps(changes, separators=(",", ":")) + "\n")
    generated = HERE / "Generated/XorAssign"
    generated.mkdir(parents=True, exist_ok=True)
    for previous in generated.glob("*.lean"):
        previous.unlink()
    aeneas = (REFERENCE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    command = [str(aeneas), "-backend", "lean", str(selected), "-dest", str(REFERENCE),
               "-subdir", "/AesAddRoundKeyWork/Generated/XorAssign", "-split-files",
               "-namespace", "RustCryptoAesXorAssign", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        status = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_only": True, "accepted_reference": False,
              "original_sha256": digest(original), "selected_sha256": digest(selected),
              "input_fingerprint": INPUT_FINGERPRINT, "kept_declarations": {k: sorted(v) for k, v in KEEP.items()},
              "change_count": len(changes), "changes_file": str(changes_file.relative_to(REFERENCE)),
              "changes_sha256": digest(changes_file), "selected_declarations_identical": True,
              "computational_bodies_modified": [], "source_patches": [],
              "additional_trusted_declaration_selection": True, "selection_correctness_mechanized": False,
              "retained_unused_metadata": [
                  "BitXorAssign trait vtable type45; already absent in original graph; no dyn calls or values",
                  "BitXorAssign impl5 vtable global6 and impl7 vtable global7; both already absent in original graph; no computational references"],
              "aeneas_exit_code": status.returncode,
              "generated_files": {str(path.relative_to(REFERENCE)): digest(path) for path in sorted(generated.glob("*.lean"))},
              "inventory": inventory(selected), "script_sha256": digest(Path(__file__)),
              "whole_add_round_key_reference_complete": False}
    (destination / "review.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Selected actual XOR-assignment leaves; Aeneas exit={status.returncode}; loop remains unproved")
    return status.returncode


if __name__ == "__main__":
    raise SystemExit(main())
