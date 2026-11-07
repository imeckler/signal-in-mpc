#!/usr/bin/env python3
"""Candidate root-only selection of the two unchanged actual slice bodies.

All declarations remain identical. The sole change removes unrelated opaque
implementation roots introduced by Charon's reference-type path limitation.
Independent review is required before acceptance.
"""
import copy
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "Artifacts/SliceImplsClosed/slice_advance.llbc"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def nodes(value):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def main():
    pinned = json.loads((HERE.parent / "report.json").read_text())["sha256"]
    key = "SignalReference/ProstEncodingWork/AdvanceWork/Artifacts/SliceImplsClosed/slice_advance.llbc"
    assert digest(SOURCE) == pinned[key]
    before = json.loads(SOURCE.read_text())
    after = copy.deepcopy(before)
    tr = after["translated"]
    removed_functions = [0, 1, 3, 4, 5, 6, 7, 8]
    removed_types = [4, 5, 6, 10, 11, 12]
    removed = [{"Fun": {"NonRec": i}} for i in removed_functions]
    removed += [{"Type": {"NonRec": i}} for i in removed_types]
    removed += [{"TraitDecl": {"NonRec": 0}}]
    for i in removed_functions:
        assert tr["fun_decls"][i]["body"] == "Opaque"
    actual = [i for i, f in enumerate(tr["fun_decls"]) if f and f["body"] != "Opaque"]
    assert actual == [2, 264]
    called = set()
    for i in actual:
        for node in nodes(tr["fun_decls"][i]["body"]):
            if isinstance(node, dict) and isinstance(node.get("Regular"), int):
                called.add(node["Regular"])
            if isinstance(node, dict) and isinstance(node.get("Trait"), list):
                call = node["Trait"]
                if len(call) == 2:
                    assert call[0]["Untagged"]["trait_decl_ref"]["skip_binder"]["id"] != 0
    assert not called.intersection(removed_functions)
    original_roots = tr["ordered_decls"]
    assert all(root in original_roots for root in removed)
    tr["ordered_decls"] = [root for root in original_roots if root not in removed]
    restored = copy.deepcopy(after)
    restored["translated"]["ordered_decls"] = original_roots
    assert restored == before
    destination = HERE / "SliceSelected"
    destination.mkdir(exist_ok=True)
    selected = destination / "slice.llbc"
    selected.write_text(json.dumps(after, separators=(",", ":")) + "\n")
    change = {"path": ["translated", "ordered_decls"],
              "before": original_roots, "after": tr["ordered_decls"]}
    changes = destination / "changes.json"
    changes.write_text(json.dumps([change], indent=2) + "\n")
    review = {"accepted_reference": False, "candidate_only": True,
              "independent_review": "pending", "additional_trusted_selection": True,
              "source_llbc_sha256": digest(SOURCE), "selected_llbc_sha256": digest(selected),
              "script_sha256": digest(Path(__file__)), "changes_sha256": digest(changes),
              "exact_reversible_changes": 1, "all_declarations_identical": True,
              "actual_computational_declarations": actual,
              "removed_codegen_roots_only": removed,
              "actual_direct_call_ids": sorted(called),
              "source_patches": [], "computational_body_patches": []}
    (destination / "review.json").write_text(json.dumps(review, indent=2) + "\n")
    print("Candidate slice selection: one reversible root-only change, both actual bodies identical.")


if __name__ == "__main__":
    main()
