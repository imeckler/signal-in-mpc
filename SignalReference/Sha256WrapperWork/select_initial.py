#!/usr/bin/env python3
"""Select the unchanged SHA core initializer past unused ArraySize metadata.

This is an additional, reviewable trusted extraction step. Only the ten original
ordered roots are translated. The other original declarations remain available
as diagnostic/name metadata; in particular, their bodies are not claimed proved.
"""
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
from extract import PINS, digest, inventory

FUNCTIONS = {0, 15, 16, 17, 161}
TYPES = {0, 1, 2}
GLOBALS = {1, 2}
REMOVED_IMPLS = {6, 9, 80}
FINGERPRINT = "0c1eda93571496180358ee68e8972d5663256eb8f7bd1448d28d25cd5ede2d54"


def walk(value, path=()):
    yield path, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from walk(child, path + (key,))
    elif isinstance(value, list):
        for key, child in enumerate(value):
            yield from walk(child, path + (key,))


def fingerprint(value):
    value = copy.deepcopy(value)
    value["translated"]["short_names"].sort(key=lambda x: json.dumps(x["key"], sort_keys=True))
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def select(original):
    assert not original["has_errors"] and fingerprint(original) == FINGERPRINT
    translated = original["translated"]
    expected_roots = [{"Type": {"NonRec": n}} for n in (1, 2, 0)] + [
        {"Fun": {"NonRec": 161}}, {"Fun": {"NonRec": 17}},
        {"Fun": {"NonRec": 16}}, {"Global": {"NonRec": 2}},
        {"Fun": {"NonRec": 15}}, {"Global": {"NonRec": 1}}, {"Fun": {"NonRec": 0}}]
    assert translated["ordered_decls"] == expected_roots
    # Scan every selected computational declaration, including signatures,
    # local types, constants and function pointers. Naming/provenance records
    # are unchanged and are not a supplied trait dictionary or call body.
    calls, global_refs, type_refs = set(), set(), set()
    for kind, ids in (("fun_decls", FUNCTIONS), ("type_decls", TYPES), ("global_decls", GLOBALS)):
        for index in ids:
            declaration = translated[kind][index]
            semantic = {k: v for k, v in declaration.items()
                        if k not in ("item_meta", "src", "layout", "ptr_metadata")}
            for path, node in walk(semantic):
                if not isinstance(node, dict):
                    continue
                assert not any(k in node for k in ("HashConsedValue", "Deduplicated", "TraitMethod", "TraitImpl", "TraitRef")), (kind, index, path)
                if type(node.get("Regular")) is int:
                    calls.add(node["Regular"])
                if "Global" in node and isinstance(node["Global"], dict):
                    global_refs.add(node["Global"]["id"])
                if type(node.get("Adt")) is int:
                    type_refs.add(node["Adt"])
    assert calls == {15, 16, 17, 161} and global_refs == GLOBALS and type_refs == TYPES
    # Constants have actual initializers, not opaque values supplied by a model.
    assert {translated["global_decls"][n]["value"]["Untagged"][0]["Call"][0]["kind"]["Fun"]["Regular"]
            for n in GLOBALS} == {15, 16}
    assert all("Structured" in translated["fun_decls"][n]["body"] for n in FUNCTIONS)
    selected = copy.deepcopy(original)
    changes = []
    for index in sorted(REMOVED_IMPLS):
        impl = selected["translated"]["trait_impls"][index]
        assert impl["impl_trait"]["id"] == 8 and translated["trait_decls"][8] is None
        assert impl["methods"] == [] and impl["consts"] == []
        changes.append({"path": ["translated", "trait_impls", index], "before": copy.deepcopy(impl), "after": None})
        selected["translated"]["trait_impls"][index] = None
    # Explicitly inventory remaining references in non-emitted declarations.
    # These are not silently represented as a closed whole-crate translation.
    excluded_refs = []
    for path, node in walk(selected["translated"]):
        if isinstance(node, dict) and isinstance(node.get("TraitImpl"), dict):
            impl = node["TraitImpl"]
            index = impl.get("id", impl.get("impl_ref", {}).get("id"))
            if index in REMOVED_IMPLS:
                assert path[0] in ("fun_decls", "trait_impls")
                if path[0] == "fun_decls":
                    assert path[1] not in FUNCTIONS
                excluded_refs.append({"path": list(path + ("TraitImpl",)), "removed_impl": index})
    restored = copy.deepcopy(selected)
    for change in changes:
        restored["translated"]["trait_impls"][change["path"][-1]] = change["before"]
    assert restored == original
    return selected, changes, excluded_refs


def main():
    original_path = HERE / "Artifacts/core_new_closed/sha_wrapper.llbc"
    original = json.loads(original_path.read_text())
    selected, changes, excluded_refs = select(original)
    destination = HERE / "InitialSelected"
    destination.mkdir(exist_ok=True)
    selected_path = destination / "selected.llbc"
    selected_path.write_text(json.dumps(selected, separators=(",", ":")) + "\n")
    changes_path = destination / "changes.json"
    changes_path.write_text(json.dumps(changes, separators=(",", ":")) + "\n")
    aeneas = (REFERENCE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    assert PINS["aeneas"]["release"] in subprocess.check_output([str(aeneas), "-version"], text=True)
    generated = HERE / "InitialGenerated"
    generated.mkdir(exist_ok=True)
    for previous in generated.glob("*.lean"):
        previous.unlink()
    command = [str(aeneas), "-backend", "lean", str(selected_path), "-dest", str(REFERENCE),
               "-subdir", "/Sha256WrapperWork/InitialGenerated", "-split-files", "-namespace", "Sha256Wrapper",
               "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "aeneas.log").open("w") as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {
        "accepted_reference": False, "additional_trusted_selection": True,
        "selection_correctness_mechanized": False,
        "original_llbc_sha256": digest(original_path), "original_fingerprint": fingerprint(original),
        "selected_llbc_sha256": digest(selected_path), "selection_script_sha256": digest(Path(__file__)),
        "changes_sha256": digest(changes_path), "reversible_changes": len(changes),
        "unchanged_computational_declarations": sorted(FUNCTIONS),
        "unchanged_type_declarations": sorted(TYPES), "unchanged_globals": sorted(GLOBALS),
        "ordered_roots_unchanged": True, "all_retained_declarations_identical": True,
        "selected_semantic_callgraph_closed": True,
        "excluded_non_emitted_references_to_removed_metadata": excluded_refs,
        "scope": "Actual Sha256VarCore::new, actual H256_224/H256_256 constants, and empty Drop path; no other wrapper is translated or proved by this selection.",
        "aeneas_command": [s.replace(str(ROOT), "$WORKSPACE") for s in command],
        "aeneas_exit_code": result.returncode,
        "remaining_external_templates": [p.name for p in generated.glob("*_Template.lean")],
        "generated_files": {str(p.relative_to(REFERENCE)): digest(p) for p in sorted(generated.glob("*.lean"))},
        "inventory": inventory(selected_path), "source_patches": [], "custom_models": [],
    }
    (destination / "review.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Actual core initializer: Aeneas exit {result.returncode}; three metadata deletions; other wrappers excluded.")
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
