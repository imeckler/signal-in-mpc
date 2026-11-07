#!/usr/bin/env python3
"""Unaccepted probe: exclude two uncalled mutable RangeFull dictionary methods.

The unchanged official SliceIndex record may still require these fields. This
probe records whether the exact dead selection is enough; it supplies no model
or missing field and never changes computational declarations.
"""
import copy
import json
from pathlib import Path
import subprocess
from select_metadata import digest, walk, ROOT, REFERENCE, HERE


def main():
    original = HERE / "Artifacts/serialize_closed/spqr.llbc"
    assert digest(original) == "a8e05615a83936385db06ac03dc6805679bcb9c9b94ab54c5953b4bf4cf92d44"
    base = HERE / "Selected/selected.llbc"
    original_data = json.loads(original.read_text())
    before = json.loads(base.read_text())
    after = copy.deepcopy(before)
    changes = json.loads((HERE / "Selected/changes.json").read_text())
    for kind, index in (("trait_decls", 6), ("trait_impls", 10)):
        for slot in (1, 5):
            target = after["translated"][kind][index]["methods"]
            changes.append({"path": ["translated", kind, index, "methods", slot],
                            "before": target[slot], "after": None})
            target[slot] = None
    roots = after["translated"]["ordered_decls"]
    keep = [x for x in roots if x not in [{"Fun": {"NonRec": i}} for i in (116, 120)]]
    changes.append({"path": ["translated", "ordered_decls"], "before": roots, "after": keep})
    after["translated"]["ordered_decls"] = keep
    for kind in ("type_decls", "fun_decls", "global_decls"):
        assert after["translated"][kind] == before["translated"][kind]
    restored = copy.deepcopy(after)
    for change in reversed(changes):
        target = restored
        for key in change["path"][:-1]:
            target = target[key]
        assert target[change["path"][-1]] == change["after"]
        target[change["path"][-1]] = change["before"]
    assert restored == original_data
    for kind in ("type_decls", "fun_decls", "global_decls", "trait_decls", "trait_impls"):
        for path, node in walk(after["translated"][kind], (kind,)):
            if not isinstance(node, dict):
                continue
            regular = node.get("Regular")
            assert not isinstance(regular, int) or regular not in (116, 120), path
            assert node.get("TraitMethod") not in [[6, 1], [6, 5]], path
            call = node.get("Trait")
            if isinstance(call, list) and len(call) == 2:
                assert (call[0]["Untagged"]["trait_decl_ref"]["skip_binder"]["id"], call[1]) not in ((6, 1), (6, 5)), path
    dest = HERE / "SharedIndexProbe"
    dest.mkdir(exist_ok=True)
    selected = dest / "selected.llbc"
    selected.write_text(json.dumps(after, separators=(",", ":")) + "\n")
    (dest / "changes.json").write_text(json.dumps(changes, indent=2) + "\n")
    generated = dest / "Generated"
    generated.mkdir(exist_ok=True)
    command = [str(ROOT / ".deps/aeneas-2026-08-27/aeneas"), "-backend", "lean", str(selected),
               "-dest", str(REFERENCE), "-subdir", "/SpqrReference/SharedIndexProbe/Generated",
               "-split-files", "-namespace", "SpqrSharedIndexProbe", "-warnings-as-errors", "-no-progress-bar"]
    with (dest / "aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {"accepted_reference": False, "probe_only": True, "source_sha256": digest(original),
              "selected_sha256": digest(selected), "script_sha256": digest(Path(__file__)),
              "changes_sha256": digest(dest / "changes.json"), "reversible_changes": len(changes),
              "all_computational_declarations_identical": True,
              "excluded_computational_roots": [116, 120],
              "retained_excluded_function_provenance": {"116": "TraitImpl SliceIndex.get_mut(6,1)", "120": "TraitImpl SliceIndex.index_mut(6,5)"},
              "aeneas_exit_code": result.returncode,
              "generated_files": {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob("*.lean")},
              "templates": [p.name for p in generated.glob("*_Template.lean")],
              "lean_typechecked": False}
    (dest / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Shared RangeFull probe: Aeneas exit", result.returncode)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
