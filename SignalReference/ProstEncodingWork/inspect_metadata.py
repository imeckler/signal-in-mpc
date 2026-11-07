#!/usr/bin/env python3
"""Isolated prost metadata compatibility candidate; no computational edits."""
import copy
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from MetadataWork.trim_step_metadata import walk, reviewed_input_fingerprint, digest

FINGERPRINT = "34ccfba7fe54db4fdd6a8fabef12acdcfde0889969b8114618b721d37bb9e608"


def select(before):
    if reviewed_input_fingerprint(before) != FINGERPRINT:
        raise ValueError("The selected prost graph changed")
    after = copy.deepcopy(before)
    tr = after["translated"]
    changes = []
    def remove(path):
        target = after
        for key in path[:-1]:
            target = target[key]
        changes.append({"path": path, "before": target[path[-1]], "after": None})
        target[path[-1]] = None
    for slot, function, name in [(2, 139, "forward_overflowing"), (6, 143, "backward_overflowing")]:
        assert tr["trait_decls"][2]["methods"][slot]["skip_binder"]["name"] == name
        assert tr["trait_impls"][2]["methods"][slot]["skip_binder"]["id"] == function
        assert tr["fun_decls"][function]["body"] == "Opaque"
        remove(["translated", "trait_decls", 2, "methods", slot])
        remove(["translated", "trait_impls", 2, "methods", slot])
        remove(["translated", "fun_decls", function])
    old = tr["ordered_decls"]
    tr["ordered_decls"] = [x for x in old if x not in [{"Fun": {"NonRec": i}} for i in (139, 143)]]
    changes.append({"path": ["translated", "ordered_decls"], "before": old, "after": tr["ordered_decls"]})
    restored = copy.deepcopy(after)
    for change in changes:
        target = restored
        for key in change["path"][:-1]:
            target = target[key]
        target[change["path"][-1]] = change["before"]
    assert restored == before
    semantic = {k: v for k, v in tr.items() if k not in ("item_names", "short_names")}
    for node in walk(semantic):
        if isinstance(node, dict):
            assert node.get("Regular") not in (139, 143)
            assert node.get("TraitMethod") not in [[2, 2], [2, 6]]
            if isinstance(node.get("skip_binder"), dict):
                assert node["skip_binder"].get("id") not in (139, 143)
    for i, function in enumerate(before["translated"]["fun_decls"]):
        if function and function["body"] != "Opaque":
            assert function == tr["fun_decls"][i]
    return after, changes


def main():
    original = HERE / "Artifacts/EncodeBody/prost_encoding.llbc"
    data, changes = select(json.loads(original.read_text()))
    destination = HERE / "Artifacts/EncodeBodyStep"
    destination.mkdir(parents=True, exist_ok=True)
    selected = destination / "selected.llbc"
    selected.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    changes_path = destination / "changes.json"
    changes_path.write_text(json.dumps(changes, indent=2) + "\n")
    generated = HERE / "Generated/EncodeBodyStep"
    generated.mkdir(parents=True, exist_ok=True)
    for path in generated.glob("*.lean"):
        path.unlink()
    command = [str(ROOT / ".deps/aeneas-2026-08-27/aeneas"), "-backend", "lean", str(selected),
               "-dest", str(REFERENCE), "-subdir", "/ProstEncodingWork/Generated/EncodeBodyStep",
               "-split-files", "-namespace", "ProstEncoding", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        status = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_only": True, "accepted_reference": False,
              "input_fingerprint": FINGERPRINT, "original_sha256": digest(original),
              "selected_sha256": digest(selected), "script_sha256": digest(Path(__file__)),
              "changes_sha256": digest(changes_path), "reversible_changes": len(changes),
              "all_retained_computational_bodies_identical": True,
              "source_patches": [], "additional_trusted_preprocessing": True,
              "independent_review": "pending", "aeneas_exit_code": status.returncode,
              "aeneas_command": [x.replace(str(ROOT), "$WORKSPACE") for x in command],
              "generated_files": {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob("*.lean")},
              "remaining_external_templates": [p.name for p in generated.glob("*_Template.lean")]}
    (destination / "review.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Candidate only: Aeneas exit {status.returncode}; external templates {report['remaining_external_templates']}")
    return status.returncode


if __name__ == "__main__":
    raise SystemExit(main())
