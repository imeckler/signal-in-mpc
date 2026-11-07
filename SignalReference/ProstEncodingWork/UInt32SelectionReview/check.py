#!/usr/bin/env python3
"""Independent exact-input review of the actual uint32 field selection.

This is a reproducible trusted extraction review, not a mechanized theorem
about the selector. It does not edit or regenerate the author's artifacts.
"""
import copy
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[1]
ROOT = REFERENCE.parent
WORK = REFERENCE / "SignalMessageWork"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def walk(value, path=()):
    yield path, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from walk(child, (*path, key))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from walk(child, (*path, index))


def main():
    original = WORK / "Artifacts/UInt32Field/signal_message.llbc"
    selected = WORK / "Artifacts/UInt32Selected/selected.llbc"
    changes_path = WORK / "Artifacts/UInt32Selected/changes.json"
    authored_review = WORK / "Artifacts/UInt32Selected/review.json"
    selector = WORK / "select_uint32.py"
    pins = {
        original: "81547c219ca760c0d2ba2902d1af5b21e6b727184978338ea7287d2cfc49de7e",
        selected: "7576b3b2feaf05e39e838bc5c8ec45898195e59b1ef4c8f1f0d358a1e89626fe",
        changes_path: "d019d9df42860169517cbd2084e73d7d5fa21aed70154233275f434a6e82cbbe",
        selector: "88d60cb001ecc6601195c49b2d7f803d2c1d407ac6588f59746032703a21908e",
    }
    for path, expected in pins.items():
        assert digest(path) == expected, path
    before, after = (json.loads(p.read_text()) for p in (original, selected))
    changes = json.loads(changes_path.read_text())
    report = json.loads(authored_review.read_text())
    expected_paths = [
        ["translated", "trait_decls", 4, "methods", 2],
        ["translated", "trait_impls", 4, "methods", 2],
        ["translated", "fun_decls", 246],
        ["translated", "trait_decls", 4, "methods", 6],
        ["translated", "trait_impls", 4, "methods", 6],
        ["translated", "fun_decls", 250],
        ["translated", "trait_decls", 0, "methods", 0],
        ["translated", "trait_decls", 0, "methods", 1],
        ["translated", "trait_decls", 0, "methods", 3],
        ["translated", "ordered_decls"],
    ]
    assert [c["path"] for c in changes] == expected_paths
    assert all(c["after"] is None for c in changes[:-1])
    replay = copy.deepcopy(before)
    for c in changes:
        target = replay
        for key in c["path"][:-1]:
            target = target[key]
        assert target[c["path"][-1]] == c["before"]
        target[c["path"][-1]] = c["after"]
    assert replay == after
    restored = copy.deepcopy(after)
    for c in reversed(changes):
        target = restored
        for key in c["path"][:-1]:
            target = target[key]
        assert target[c["path"][-1]] == c["after"]
        target[c["path"][-1]] = c["before"]
    assert restored == before
    b, a = before["translated"], after["translated"]
    removed_roots = [{"Fun": {"NonRec": i}} for i in (5, 246, 250)] + [{"Type": {"NonRec": 2}}]
    assert a["ordered_decls"] == [x for x in b["ordered_decls"] if x not in removed_roots]
    computational = [i for i, f in enumerate(b["fun_decls"]) if f and f["body"] != "Opaque"]
    assert computational == [0, 1, 2, 7, 48, 145, 256, 257, 286, 287]
    for key in ("type_decls", "fun_decls", "global_decls", "trait_decls", "trait_impls"):
        assert len(a[key]) == len(b[key])
        for index, value in enumerate(a[key]):
            if (key, index) in (("trait_decls", 0), ("trait_decls", 4), ("trait_impls", 4)):
                continue  # Exact field differences are checked by the exhaustive replay.
            if (key, index) in (("fun_decls", 246), ("fun_decls", 250)):
                assert value is None and b[key][index]["body"] == "Opaque"
            else:
                assert value == b[key][index], (key, index)
    for slot, function, name in ((2, 246, "forward_overflowing"), (6, 250, "backward_overflowing")):
        assert b["trait_decls"][4]["methods"][slot]["skip_binder"]["name"] == name
        assert b["trait_impls"][4]["methods"][slot]["skip_binder"]["id"] == function
    for slot, name in ((0, "remaining_mut"), (1, "advance_mut"), (3, "chunk_mut")):
        assert b["trait_decls"][0]["methods"][slot]["skip_binder"]["name"] == name
    for slot, name in ((5, "put_slice"), (7, "put_u8")):
        assert a["trait_decls"][0]["methods"][slot] == b["trait_decls"][0]["methods"][slot]
        assert a["trait_decls"][0]["methods"][slot]["skip_binder"]["name"] == name
    # Inspect every retained semantic declaration, including signatures, globals,
    # trait defaults and function pointers, rather than only function bodies.
    removed_fields = {(0, 0), (0, 1), (0, 3), (4, 2), (4, 6)}
    buffer_calls, semantic_nodes = set(), 0
    for key in ("type_decls", "fun_decls", "global_decls", "trait_decls", "trait_impls"):
        for path, node in walk(a[key], (key,)):
            semantic_nodes += 1
            if not isinstance(node, dict):
                continue
            regular = node.get("Regular")
            assert not isinstance(regular, int) or regular not in (5, 246, 250), path
            trait_method = node.get("TraitMethod")
            if isinstance(trait_method, list) and len(trait_method) == 2:
                assert tuple(trait_method) not in removed_fields, path
            call = node.get("Trait")
            if isinstance(call, list) and len(call) == 2:
                ref = call[0].get("Untagged", {}).get("trait_decl_ref", {}).get("skip_binder", {})
                if "id" in ref:
                    field = (ref["id"], call[1])
                    assert field not in removed_fields, path
                    if field[0] == 0:
                        buffer_calls.add(field[1])
    assert buffer_calls == {5, 7}
    assert b["fun_decls"][5] == a["fun_decls"][5]  # Uncalled opaque default retained as metadata.
    assert b["type_decls"][2] == a["type_decls"][2]  # UninitSlice signature metadata retained.
    assert a["fun_decls"][253]["body"] == "Opaque"  # Official RangeInclusive.new model.
    assert report["aeneas_exit_code"] == 0 and report["remaining_external_templates"] == []
    assert report["reversible_changes"] == 10
    for filename, expected in report["generated_files"].items():
        assert digest(REFERENCE / filename) == expected
    inventory = json.loads((WORK / "Artifacts/UInt32Field/inventory.json").read_text())
    assert inventory["charon_exit_code"] == 0 and not inventory["has_errors"]
    assert inventory["source_patches"] == []
    for filename, expected in inventory["source_sha256"].items():
        assert digest(ROOT / filename) == expected
    iterator_model = ROOT / ".deps/aeneas-2026-08-27/backends/lean/Aeneas/Std/Core/Iter.lean"
    iterator_text = iterator_model.read_text()
    assert "def core.ops.range.RangeInclusive.new" in iterator_text
    assert "StepInst.forward_checked range' 1#usize" in iterator_text
    assert "forward_overflowing" not in iterator_text and "backward_overflowing" not in iterator_text
    files = [*pins, authored_review, WORK / "Artifacts/UInt32Field/inventory.json",
             iterator_model, Path(__file__)]
    output = {
        "independent_review": True,
        "reviewer": "/root/signal_lean_aeneas/pkcs7_reference",
        "author": "/root/signal_lean_aeneas",
        "checks_passed": True,
        "accepted_scope": "Selected actual Prost uint32 field/tag/varint and byte-default semantics under supplied BufMut operations",
        "original_llbc_sha256": digest(original),
        "selected_llbc_sha256": digest(selected),
        "selection_script_sha256": digest(selector),
        "exact_reversible_changes": len(changes),
        "retained_declarations_identical": True,
        "unchanged_computational_declarations": computational,
        "semantic_declaration_nodes_scanned": semantic_nodes,
        "retained_called_buffer_fields": ["put_slice", "put_u8"],
        "unused_opaque_metadata_retained": ["default BufMut.put_slice declaration 5", "UninitSlice type declaration 2"],
        "official_standard_models": ["RangeInclusive.new", "Range.next and StepI32.forward_checked", "scalar operations and casts", "Array.to_slice"],
        "additional_trusted_preprocessing": True,
        "mechanized_selection_correctness": False,
        "source_patches": [],
        "custom_crypto_or_buffer_models_added": [],
        "remaining_obligations": [
            "Instantiate the selected BufMut dictionary with proved concrete buffer semantics, as required by any claimed concrete Vec endpoint.",
            "Compose length-delimited fields and derive-generated SignalMessage serialization before claiming whole-message reference equivalence.",
        ],
        "sha256": {str(p.relative_to(ROOT)): digest(p) for p in files},
        "generated_files": report["generated_files"],
    }
    (HERE / "review.json").write_text(json.dumps(output, indent=2) + "\n")
    print("Passed: 10 reversible changes, all 10 actual bodies unchanged, full semantic reference scan, official models and generated pins.")


if __name__ == "__main__":
    main()
