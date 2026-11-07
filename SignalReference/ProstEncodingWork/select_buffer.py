#!/usr/bin/env python3
"""Candidate extraction of the actual generic loop, preserving buffer calls.

The unrelated BufMut required methods are omitted from its translated record;
the called put_u8 and put_slice fields and their exact signatures remain.
The unused opaque default put_slice declaration remains in the LLBC metadata,
but is not a code-generation root. No actual body is edited or replaced.
"""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
spec = importlib.util.spec_from_file_location("prost_step_metadata", HERE / "inspect_metadata.py")
metadata = importlib.util.module_from_spec(spec)
spec.loader.exec_module(metadata)
digest = metadata.digest
walk = metadata.walk


def main():
    original = HERE / "Artifacts/EncodeBody/prost_encoding.llbc"
    before = json.loads(original.read_text())
    selected, changes = metadata.select(before)
    tr = selected["translated"]
    for slot, name in [(0, "remaining_mut"), (1, "advance_mut"), (3, "chunk_mut")]:
        assert tr["trait_decls"][0]["methods"][slot]["skip_binder"]["name"] == name
        changes.append({"path": ["translated", "trait_decls", 0, "methods", slot],
                        "before": tr["trait_decls"][0]["methods"][slot], "after": None})
        tr["trait_decls"][0]["methods"][slot] = None
    old = tr["ordered_decls"]
    tr["ordered_decls"] = [x for x in old if x not in [{"Type": {"NonRec": 3}}, {"Fun": {"NonRec": 5}}]]
    changes.append({"path": ["translated", "ordered_decls"], "before": old, "after": tr["ordered_decls"]})
    restored = copy.deepcopy(selected)
    for change in reversed(changes):
        target = restored
        for key in change["path"][:-1]:
            target = target[key]
        target[change["path"][-1]] = change["before"]
    assert restored == before
    for fn in tr["fun_decls"]:
        if fn and fn["body"] != "Opaque":
            for node in walk(fn):
                if isinstance(node, dict):
                    assert node.get("Regular") != 5
                    assert node.get("TraitMethod") not in [[0, 0], [0, 1], [0, 3]]
                    trait = node.get("Trait")
                    if isinstance(trait, list) and len(trait) == 2:
                        declaration = trait[0]["Untagged"]["trait_decl_ref"]["skip_binder"]["id"]
                        assert [declaration, trait[1]] not in [[0, 0], [0, 1], [0, 3]]
    for index, fn in enumerate(before["translated"]["fun_decls"]):
        if fn and fn["body"] != "Opaque":
            assert fn == tr["fun_decls"][index]
    destination = HERE / "Artifacts/EncodeSelected"
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / "selected.llbc"
    llbc.write_text(json.dumps(selected, separators=(",", ":")) + "\n")
    changes_path = destination / "changes.json"
    changes_path.write_text(json.dumps(changes, indent=2) + "\n")
    generated = HERE / "Generated/EncodeSelected"
    generated.mkdir(parents=True, exist_ok=True)
    for path in generated.glob("*.lean"):
        path.unlink()
    command = [str(ROOT / ".deps/aeneas-2026-08-27/aeneas"), "-backend", "lean", str(llbc),
               "-dest", str(REFERENCE), "-subdir", "/ProstEncodingWork/Generated/EncodeSelected",
               "-split-files", "-namespace", "ProstEncoding", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        status = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_only": True, "accepted_reference": False,
              "input_fingerprint": metadata.FINGERPRINT, "original_sha256": digest(original),
              "selected_sha256": digest(llbc), "script_sha256": digest(Path(__file__)),
              "step_script_sha256": digest(HERE / "inspect_metadata.py"),
              "changes_sha256": digest(changes_path), "reversible_changes": len(changes),
              "all_retained_computational_bodies_identical": True,
              "called_buffer_fields": ["put_u8", "put_slice"],
              "unused_default_put_slice_declaration_retained": True,
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
