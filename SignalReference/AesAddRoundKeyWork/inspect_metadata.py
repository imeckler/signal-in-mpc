#!/usr/bin/env python3
"""Candidate: omit unused Iterator.zip dictionary slots, retain actual zip call."""

import argparse
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

INPUT_FINGERPRINTS = {
    "Base": "8052c79c2892dea4bbccc61b35fef92cbee86295bad84d8ec587c68b886c5ee2",
    "IncludeXor": "300bd089be43fed9094af3ef359a0fdb92ded0d907c0a09353de40bc240a3c5c",
}


def select(before, variant="Base"):
    if before["has_errors"] or reviewed_input_fingerprint(before) != INPUT_FINGERPRINTS[variant]:
        raise ValueError("Actual add_round_key graph differs from selected candidate")
    data = copy.deepcopy(before)
    tr = data["translated"]
    changes = []
    def remove(path):
        value = data
        for key in path[:-1]:
            value = value[key]
        changes.append({"path": path, "before": value[path[-1]], "after": None})
        value[path[-1]] = None
    assert name_of(tr["trait_decls"][0]["item_meta"]) == "core::iter::traits::iterator::Iterator"
    assert tr["trait_decls"][0]["methods"][9]["skip_binder"]["name"] == "zip"
    assert name_of(tr["fun_decls"][3]["item_meta"]) == "core::iter::traits::iterator::Iterator::zip"
    remove(["translated", "trait_decls", 0, "methods", 9])
    for impl, expected_name in ((0, "core::slice::iter::{impl}"),
                                (3, "core::iter::adapters::zip::{impl}"),
                                (4, "core::slice::iter::{impl}")):
        assert name_of(tr["trait_impls"][impl]["item_meta"]) == expected_name
        assert tr["trait_impls"][impl]["methods"][9]["skip_binder"]["id"] == 3
        assert tr["trait_impls"][impl]["methods"][9]["kind"] == {"TraitMethod": [0, 9]}
        remove(["translated", "trait_impls", impl, "methods", 9])
    restored = copy.deepcopy(data)
    for change in changes:
        slot = restored
        for key in change["path"][:-1]:
            slot = slot[key]
        slot[change["path"][-1]] = change["before"]
    assert restored == before
    assert tr["fun_decls"] == before["translated"]["fun_decls"]
    semantic = {key: value for key, value in tr.items() if key not in ("item_names", "short_names")}
    for node in walk(semantic):
        if isinstance(node, dict):
            assert node.get("TraitMethod") != [0, 9]
            default = node.get("TraitDefault")
            if isinstance(default, dict) and [default["trait_ref"]["id"], default["item_id"]] == [0, 9]:
                assert node is tr["fun_decls"][3]["src"]
    assert any(isinstance(node, dict) and node.get("Regular") == 3 for node in walk(tr["fun_decls"][0]["body"]))
    return data, changes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--variant", choices=INPUT_FINGERPRINTS, default="Base")
    args = parser.parse_args()
    check_sources()
    destination = (HERE / "Artifacts") if args.variant == "Base" else (HERE / "Artifacts" / args.variant)
    original = destination / "add_round_key.llbc"
    before = json.loads(original.read_text())
    data, changes = select(before, args.variant)
    selected = destination / "selected.llbc"
    selected.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    aeneas = (REFERENCE / PINS["aeneas"]["directory"] / "aeneas").resolve()
    generated = (HERE / "Generated") if args.variant == "Base" else (HERE / "Generated" / args.variant)
    generated.mkdir(parents=True, exist_ok=True)
    for previous in generated.glob("*.lean"):
        previous.unlink()
    command = [str(aeneas), "-backend", "lean", str(selected), "-dest", str(REFERENCE),
               "-subdir", "/" + str(generated.relative_to(REFERENCE)), "-split-files",
               "-namespace", "RustCryptoAesAddRoundKey", "-warnings-as-errors", "-no-progress-bar"]
    with (destination / "selected-aeneas.log").open("w") as log:
        status = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {"candidate_only": True, "accepted_reference": False,
              "original_sha256": digest(original), "selected_sha256": digest(selected),
              "input_fingerprint": INPUT_FINGERPRINTS[args.variant],
              "changes": changes, "computational_bodies_modified": [], "source_patches": [],
              "zip_function_3_retained_unchanged": True,
              "trait_default_provenance_retained": True,
              "all_retained_semantic_references_checked": True,
              "aeneas_exit_code": status.returncode,
              "generated_files": {str(path.relative_to(REFERENCE)): digest(path) for path in sorted(generated.glob("*.lean"))},
              "inventory": inventory(selected), "script_sha256": digest(Path(__file__))}
    (destination / "review.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Candidate zip metadata selection exit={status.returncode}; not an accepted reference")
    return status.returncode


if __name__ == "__main__":
    raise SystemExit(main())
