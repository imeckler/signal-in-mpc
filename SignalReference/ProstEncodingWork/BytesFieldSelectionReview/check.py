#!/usr/bin/env python3
"""Independent review of one exact actual Prost bytes-field selection.

Only this review directory is written. The selected program, Rust sources,
translator and standard models are never changed or regenerated here.
This executable review is trusted preprocessing evidence, not a proof of
the selector or of the missing concrete payload adapter.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[1]
ROOT = REFERENCE.parent
WORK = REFERENCE / "SignalMessageWork/BytesFieldWork"
KINDS = ("type_decls", "fun_decls", "global_decls", "trait_decls", "trait_impls")


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
    original = WORK / "Artifacts/bytes_field.llbc"
    selected = WORK / "Selected/selected.llbc"
    changes_path = WORK / "Selected/changes.json"
    selector = WORK / "select_bytes.py"
    pins = {
        original: "51a0baeaba1a94c79c6ef533daa82eeb986976ae5a3d8b2b208b973c23efad8b",
        selected: "774e6ccb883a87e8c243474991d5bd8e79c3d0f2ddd998780962b5c18488a2a0",
        changes_path: "40f55d35ca2f6523bcbeb2d291c4b6ea27ab73a6b830689e4f662e0a3274875b",
        selector: "d314e125d79367012aa903d6a1baa44a229650f2c34bdacfdb149cd00af37227",
    }
    for path, expected in pins.items():
        assert digest(path) == expected, path
    before, after = (json.loads(p.read_text()) for p in (original, selected))
    changes = json.loads(changes_path.read_text())
    expected_paths = [
        ["translated", "trait_decls", 7, "methods", 2],
        ["translated", "trait_impls", 4, "methods", 2],
        ["translated", "fun_decls", 247],
        ["translated", "trait_decls", 7, "methods", 6],
        ["translated", "trait_impls", 4, "methods", 6],
        ["translated", "fun_decls", 251],
        ["translated", "trait_decls", 1, "methods", 0],
        ["translated", "trait_decls", 1, "methods", 1],
        ["translated", "trait_decls", 1, "methods", 3],
        ["translated", "ordered_decls"],
    ]
    assert [c["path"] for c in changes] == expected_paths
    assert all(c["after"] is None for c in changes[:-1])
    replay = copy.deepcopy(before)
    for change in changes:
        target = replay
        for key in change["path"][:-1]:
            target = target[key]
        assert target[change["path"][-1]] == change["before"]
        target[change["path"][-1]] = change["after"]
    assert replay == after
    restored = copy.deepcopy(after)
    for change in reversed(changes):
        target = restored
        for key in change["path"][:-1]:
            target = target[key]
        assert target[change["path"][-1]] == change["after"]
        target[change["path"][-1]] = change["before"]
    assert restored == before
    b, a = before["translated"], after["translated"]
    omitted_roots = [{"Fun": {"NonRec": i}} for i in (5, 247, 251)] + [{"Type": {"NonRec": 2}}]
    assert a["ordered_decls"] == [x for x in b["ordered_decls"] if x not in omitted_roots]
    computational = [i for i, f in enumerate(b["fun_decls"]) if f and f["body"] != "Opaque"]
    assert computational == [0, 1, 2, 7, 48, 50, 146, 257, 258, 287, 288]
    for kind in KINDS:
        assert len(a[kind]) == len(b[kind])
        for index, value in enumerate(a[kind]):
            if (kind, index) in (("trait_decls", 1), ("trait_decls", 7), ("trait_impls", 4)):
                continue  # Their exact differences are covered by exhaustive reversible replay.
            if (kind, index) in (("fun_decls", 247), ("fun_decls", 251)):
                assert value is None and b[kind][index]["body"] == "Opaque"
            else:
                assert value == b[kind][index], (kind, index)
    for slot, function, name in ((2, 247, "forward_overflowing"), (6, 251, "backward_overflowing")):
        assert b["trait_decls"][7]["methods"][slot]["skip_binder"]["name"] == name
        assert b["trait_impls"][4]["methods"][slot]["skip_binder"]["id"] == function
    for slot, name in ((0, "remaining_mut"), (1, "advance_mut"), (3, "chunk_mut")):
        assert b["trait_decls"][1]["methods"][slot]["skip_binder"]["name"] == name
    for trait, slot, name in ((1, 5, "put_slice"), (1, 7, "put_u8"), (2, 0, "len"), (2, 2, "append_to")):
        assert a["trait_decls"][trait]["methods"][slot] == b["trait_decls"][trait]["methods"][slot]
        assert a["trait_decls"][trait]["methods"][slot]["skip_binder"]["name"] == name

    # Scan complete retained declarations, including all signatures, constants,
    # function pointers, trait defaults, implementation methods and vtables.
    removed_fields = {(1, 0), (1, 1), (1, 3), (7, 2), (7, 6)}
    semantic_nodes = 0
    calls = set()
    for kind in KINDS:
        for path, node in walk(a[kind], (kind,)):
            semantic_nodes += 1
            if not isinstance(node, dict):
                continue
            regular = node.get("Regular")
            assert not isinstance(regular, int) or regular not in (5, 247, 251), path
            method = node.get("TraitMethod")
            if isinstance(method, list) and len(method) == 2:
                assert tuple(method) not in removed_fields, path
            call = node.get("Trait")
            if isinstance(call, list) and len(call) == 2:
                ref = call[0].get("Untagged", {}).get("trait_decl_ref", {}).get("skip_binder", {})
                if "id" in ref:
                    field = (ref["id"], call[1])
                    assert field not in removed_fields, path
                    calls.add(field)
            default = node.get("default")
            if isinstance(default, dict):
                assert default.get("id") not in (247, 251), path
                if default.get("id") == 5:
                    assert path == ("trait_decls", 1, "methods", 5, "skip_binder")
            for source in ("TraitDefault", "TraitImpl"):
                provenance = node.get(source)
                if isinstance(provenance, dict) and "trait_ref" in provenance and "item_id" in provenance:
                    assert (provenance["trait_ref"]["id"], provenance["item_id"]) not in removed_fields, path
    assert {x for x in calls if x[0] in (1, 2)} == {(1, 5), (1, 7), (2, 0), (2, 2)}
    for impl in a["trait_impls"]:
        if impl:
            for method in impl["methods"]:
                if method:
                    assert method["skip_binder"]["id"] not in (5, 247, 251)
    assert a["fun_decls"][5] == b["fun_decls"][5] and a["fun_decls"][5]["body"] == "Opaque"
    assert a["type_decls"][2] == b["type_decls"][2]
    assert a["fun_decls"][254]["body"] == "Opaque"  # Official RangeInclusive.new model.
    expected_call_graph = {
        0: ([1, 2], [(2, 0), (2, 2)]), 1: ([2, 48, 49, 254], []),
        2: ([51, 52], [(1, 7)]), 7: ([], [(1, 5)]), 48: ([146], []),
        50: ([], [(2, 0)]), 146: ([], [(4, 1), (4, 2), (9, 0), (9, 1)]),
        257: ([], []), 258: ([], []), 287: ([], []), 288: ([], []),
    }
    for index, expected in expected_call_graph.items():
        regulars, traits = set(), set()
        for _, node in walk(a["fun_decls"][index]["body"]):
            if not isinstance(node, dict):
                continue
            if isinstance(node.get("Regular"), int):
                regulars.add(node["Regular"])
            call = node.get("Trait")
            if isinstance(call, list) and len(call) == 2:
                traits.add((call[0]["Untagged"]["trait_decl_ref"]["skip_binder"]["id"], call[1]))
        assert (sorted(regulars), sorted(traits)) == expected, index

    inventory_path = WORK / "Artifacts/inventory.json"
    inventory = json.loads(inventory_path.read_text())
    assert inventory["charon_exit_code"] == 0 and not inventory["has_errors"]
    assert inventory["source_patches"] == []
    assert digest(WORK / "extract.py") == inventory["script_sha256"]
    for name, expected in inventory["source_sha256"].items():
        assert digest(ROOT / name) == expected, name
    # Local source text embedded by Charon is exact pinned Prost source.
    for index in (0, 1, 2, 50, 287, 288):
        meta = a["fun_decls"][index]["item_meta"]
        filename = "src/encoding/varint.rs" if index == 2 else "src/encoding.rs"
        assert meta["source_text"] in (ROOT / ".deps/libsignal-vendor/prost-0.14.4" / filename).read_text()
    authored_path = WORK / "Selected/review.json"
    authored = json.loads(authored_path.read_text())
    assert authored["aeneas_exit_code"] == 0 and authored["remaining_external_templates"] == []
    assert authored["reversible_changes"] == 10 and authored["unchanged_computational_declarations"] == computational
    for name, expected in authored["generated_files"].items():
        assert digest(REFERENCE / name) == expected, name
    assert not list((WORK / "GeneratedSelected").glob("*_Template.lean"))

    # Verify unchanged standard-model sources against the exact upstream archive,
    # not merely against a mutable workspace manifest.
    archive = REFERENCE / "ProstEncodingWork/AdvanceWork/TranslatorCandidate/aeneas-5b9dcf33.tar.gz"
    assert digest(archive) == "ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453"
    model_dir = ROOT / ".deps/aeneas-2026-08-27/backends/lean/Aeneas/Std"
    model_hashes = {}
    with tarfile.open(archive) as bundle:
        members = {m.name.split("/", 1)[1]: m for m in bundle.getmembers() if "/" in m.name and m.isfile()}
        for model in sorted(model_dir.rglob("*.lean")):
            name = "backends/lean/Aeneas/Std/" + str(model.relative_to(model_dir))
            assert model.read_bytes() == bundle.extractfile(members[name]).read(), model
            model_hashes[str(model.relative_to(ROOT))] = digest(model)
    iterator = (model_dir / "Core/Iter.lean").read_text()
    assert "StepInst.forward_checked range' 1#usize" in iterator
    assert "def core.ops.range.RangeInclusive.new" in iterator
    assert "forward_overflowing" not in iterator and "backward_overflowing" not in iterator

    proof_path = WORK / "proof-check.json"
    proof = json.loads(proof_path.read_text())
    for name, expected in proof["source_sha256"].items():
        assert digest(ROOT / name) == expected, name
    assert digest(WORK / "axioms.txt") == proof["axiom_report_sha256"]
    assert proof["checked_endpoints"] == 9 and proof["custom_axioms"] == []
    assert proof["concrete_vector_append_refined"] is False
    assert proof["full_signalmessage_encoder_refined"] is False
    assert len(proof["undischarged_hypotheses"]) == 2

    # Fresh kernel checks use a private olean directory; parent sources and
    # build outputs are untouched. Other imported proof modules are the pinned
    # dependencies already recorded by the parent audit.
    lean_root = HERE / "Lean"
    cache = Path("/Users/izzy/repos/eco-theorem-combined/.lake/packages")
    paths = [lean_root, REFERENCE / ".lake/build/lib/lean", ROOT / ".lake/build/lib/lean",
             ROOT / ".deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean"]
    paths += sorted(p / ".lake/build/lib/lean" for p in cache.iterdir() if (p / ".lake/build/lib/lean").is_dir())
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(str(p) for p in paths)
    modules = ["GeneratedSelected/Types", "GeneratedSelected/Funs", "Reference"]
    commands, logs = [], []
    for module in modules:
        name = "SignalMessageWork/BytesFieldWork/" + module
        output = lean_root / (name + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        command = ["lean", "-o", str(output), name + ".lean"]
        result = subprocess.run(command, cwd=REFERENCE, env=env, text=True, capture_output=True, check=True)
        commands.append([x.replace(str(ROOT), "$WORKSPACE") for x in command])
        logs.append(result.stdout + result.stderr)
    command = ["lean", "SignalMessageWork/BytesFieldWork/Checks.lean"]
    result = subprocess.run(command, cwd=REFERENCE, env=env, text=True, capture_output=True, check=True)
    commands.append(command)
    endpoints = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert [name for name, _ in endpoints] == proof["theorems"]
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, assumptions in endpoints:
        assert not ({x.strip() for x in assumptions.split(",") if x.strip()} - allowed), name
    (HERE / "axioms.txt").write_text(result.stdout)
    (HERE / "build.log").write_text("".join(logs) + result.stderr)
    # Detect any concurrent source changes before committing this review.
    for name, expected in proof["source_sha256"].items():
        assert digest(ROOT / name) == expected, name
    files = [*pins, authored_path, inventory_path, proof_path, WORK / "Reference.lean",
             WORK / "Checks.lean", WORK / "extract.py", archive, Path(__file__)]
    report = {
        "independent_review": True,
        "reviewer": "/root/signal_lean_aeneas/pkcs7_reference",
        "author": "/root/signal_lean_aeneas",
        "checks_passed": True,
        "accepted_scope": "Reviewed exact generic Prost bytes::encode graph and conditional circuit composition for Signal tags 1, 4, 5, 6; no concrete payload adapter accepted.",
        "original_llbc_sha256": digest(original),
        "selected_llbc_sha256": digest(selected),
        "selection_script_sha256": digest(selector),
        "exact_reversible_changes": len(changes),
        "retained_declarations_identical": True,
        "unchanged_computational_declarations": computational,
        "semantic_declaration_nodes_scanned": semantic_nodes,
        "actual_call_graph": {str(k): {"regular": v[0], "trait_slots": v[1]} for k, v in expected_call_graph.items()},
        "retained_called_buffer_fields": ["BufMut.put_u8", "BufMut.put_slice", "sealed.BytesAdapter.len", "sealed.BytesAdapter.append_to"],
        "unused_opaque_metadata_retained": [
            "Uncalled default BufMut.put_slice declaration 5 and its trait-default pointer remain identical; only its codegen root is omitted.",
            "UninitSlice type declaration 2 remains identical; only its codegen root is omitted.",
            "All pre-existing type/vtable/global metadata is unchanged; no removed method is used by retained dispatch or function-pointer references.",
        ],
        "official_models": ["RangeInclusive.new", "Range.next / StepI32.forward_checked", "IntoIterator blanket identity", "scalar casts, shifts, comparisons and FromU64U32", "Array.to_slice"],
        "standard_model_files_identical_to_pinned_archive": len(model_hashes),
        "standard_model_sha256": model_hashes,
        "additional_trusted_preprocessing": True,
        "mechanized_selection_correctness": False,
        "source_patches": [],
        "custom_crypto_or_buffer_models_added": [],
        "fresh_kernel_checked_endpoints": len(endpoints),
        "allowed_foundational_axioms": sorted(allowed),
        "custom_axioms": [],
        "kernel_commands": commands,
        "axiom_report_sha256": digest(HERE / "axioms.txt"),
        "unconditional_theorem": "LibSignalReference.Candidate.SignalBytesField.field_eq",
        "conditional_artifact_theorem": "LibSignalReference.Candidate.SignalBytesField.field_refines_artifact_of_payload_contract",
        "conditional_domain": "Arbitrary shared payload contents, fixed public length, tags 1/4/5/6, and buffer.length + payload.length + 11 <= Usize.max.",
        "remaining_obligations": [
            "Discharge actual concrete adapter.len = Vec.len and PayloadAppends against the same selected dictionaries.",
            "Actual Vec BytesAdapter.append_to calls BufMut.put(self.as_slice()); the present reduced BufMut graph and varint Vec.put_slice theorem do not establish that path.",
            "Concrete Vec.put/reserve/as_slice and slice advance, including any separately reviewed translator/model boundary, remain outside this reviewed slice.",
            "Compose the generated SignalMessage encoder and remaining wrappers before claiming complete Signal serialization equivalence.",
        ],
        "concrete_vector_append_refined": False,
        "full_signalmessage_encoder_refined": False,
        "sha256": {str(p.relative_to(ROOT)): digest(p) for p in files},
        "generated_files": authored["generated_files"],
    }
    (HERE / "review.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Passed: 10 reversible changes; all 11 actual bodies unchanged; complete retained semantic scan; 9 kernel endpoints with standard axioms. Concrete adapter remains conditional.")


if __name__ == "__main__":
    main()
