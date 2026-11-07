#!/usr/bin/env python3
"""Select the exact actual SPQR graph by removing unused Step metadata only.

Every retained computational declaration and Rust source is unchanged. This
candidate trusted preprocessing step requires independent review before use
as an accepted implementation reference.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


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
    original = HERE / "Artifacts/varint/spqr.llbc"
    assert digest(original) == "4ca6cf0b654e390018974569b0ed956687aa4a52206cf7354fa2ada91f2829ab"
    before = json.loads(original.read_text())
    after = copy.deepcopy(before)
    t = after["translated"]
    changes = []

    def replace(path, value):
        target = after
        for key in path[:-1]:
            target = target[key]
        changes.append({"path": path, "before": target[path[-1]], "after": value})
        target[path[-1]] = value

    for slot, function, name in ((2, 96, "forward_overflowing"), (6, 100, "backward_overflowing")):
        assert t["trait_decls"][1]["methods"][slot]["skip_binder"]["name"] == name
        assert t["trait_impls"][2]["methods"][slot]["skip_binder"]["id"] == function
        assert t["fun_decls"][function]["body"] == "Opaque"
        replace(["translated", "trait_decls", 1, "methods", slot], None)
        replace(["translated", "trait_impls", 2, "methods", slot], None)
        replace(["translated", "fun_decls", function], None)
    omit = [{"Fun": {"NonRec": n}} for n in (96, 100)]
    replace(["translated", "ordered_decls"], [x for x in t["ordered_decls"] if x not in omit])
    restored = copy.deepcopy(after)
    for change in reversed(changes):
        target = restored
        for key in change["path"][:-1]:
            target = target[key]
        target[change["path"][-1]] = change["before"]
    assert restored == before
    computational = []
    for index, function in enumerate(before["translated"]["fun_decls"]):
        if function and function["body"] != "Opaque":
            computational.append(index)
            assert t["fun_decls"][index] == function
    assert computational == [0, 4]
    for kind in ("type_decls", "fun_decls", "global_decls", "trait_decls", "trait_impls"):
        for path, node in walk(t[kind], (kind,)):
            if not isinstance(node, dict):
                continue
            regular = node.get("Regular")
            assert not isinstance(regular, int) or regular not in (96, 100), path
            assert node.get("TraitMethod") not in [[1, 2], [1, 6]], path
            call = node.get("Trait")
            if isinstance(call, list) and len(call) == 2:
                assert (call[0]["Untagged"]["trait_decl_ref"]["skip_binder"]["id"], call[1]) not in ((1, 2), (1, 6)), path
            default = node.get("default")
            if isinstance(default, dict):
                assert default.get("id") not in (96, 100), path
            for source in ("TraitDefault", "TraitImpl"):
                origin = node.get(source)
                if isinstance(origin, dict) and "trait_ref" in origin and "item_id" in origin:
                    assert (origin["trait_ref"]["id"], origin["item_id"]) not in ((1, 2), (1, 6)), path
    for impl in t["trait_impls"]:
        if impl:
            assert all(m is None or m["skip_binder"]["id"] not in (96, 100) for m in impl["methods"])
    destination = HERE / "VarintSelected"
    destination.mkdir(parents=True, exist_ok=True)
    selected = destination / "selected.llbc"
    selected.write_text(json.dumps(after, separators=(",", ":")) + "\n")
    changes_path = destination / "changes.json"
    changes_path.write_text(json.dumps(changes, indent=2) + "\n")
    generated = HERE / "VarintGenerated"
    generated.mkdir(parents=True, exist_ok=True)
    for old in generated.glob("*.lean"):
        old.unlink()
    command = [str(ROOT / ".deps/aeneas-2026-08-27/aeneas"), "-backend", "lean", str(selected),
               "-dest", str(REFERENCE), "-subdir", "/SpqrReference/VarintGenerated", "-split-files",
               "-namespace", "SpqrReference", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_only": True, "accepted_reference": False, "independent_review": "pending",
              "original_sha256": digest(original), "selected_sha256": digest(selected),
              "script_sha256": digest(Path(__file__)), "changes_sha256": digest(changes_path),
              "reversible_changes": len(changes), "unchanged_computational_declarations": computational,
              "additional_trusted_preprocessing": True, "source_patches": [],
              "aeneas_exit_code": result.returncode,
              "aeneas_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "generated_files": {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob("*.lean")},
              "remaining_external_templates": [p.name for p in generated.glob("*_Template.lean")]}
    (destination / "review.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"SPQR varint selection: Aeneas exit {result.returncode}; templates {report['remaining_external_templates']}")
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
