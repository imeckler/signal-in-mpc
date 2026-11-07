#!/usr/bin/env python3
"""Record the reproducible, unaccepted whole-serializer extraction boundaries."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    cases = []
    files = [Path(__file__), HERE / "extract.py", HERE / "extract_optimized_probe.py",
             HERE / "select_metadata.py", HERE / "select_shared_index_probe.py"]
    explanations = {
        "serialize_lookup_baseline": "The Rust type-path pattern resolves actual bodies but Charon's later defining-name filter produces zero ordered roots. Aeneas exit0 and empty outputs do not establish an extracted operation.",
        "serialize_defining_baseline": "The defining-module pattern alone fails Rust item-path resolution. The accepted dual-pattern profile uses start-from plus start-from-if-exists without source changes.",
        "serialize": "The real graph reaches the accepted tool's missing Step.forward_overflowing dictionary metadata; no translation accepted.",
        "serialize_closed": "Including actual core::slice::index bodies retains the shared RangeFull index implementation; Step metadata still needs the separate exact selector.",
        "serialize_mono": "Standard monomorphization does not complete extraction: Aeneas fails at Charon.TypesUtils.as_ident / ExtractBase.ctx_compute_var_basename and emits external templates.",
        "serialize_inline": "Standard optimized MIR with Inline/GVN/SimplifyLocals-final and debug/overflow checks enabled fails Charon on ConstEvalVal at alloc/src/vec/mod.rs:3605. No Rust body or compiler pass was patched.",
    }
    for profile, explanation in explanations.items():
        directory = HERE / "Artifacts" / profile
        inventory = directory / "inventory.json"
        data = json.loads(inventory.read_text())
        files += [inventory, directory / "charon.log"]
        for name in ("spqr.llbc", "aeneas.log", "extract-script.py"):
            if (directory / name).exists():
                files.append(directory / name)
        cases.append({
            "profile": profile,
            "accepted_reference": False,
            "charon_exit_code": data["charon_exit_code"],
            "aeneas_exit_code": data.get("aeneas_exit_code"),
            "ordered_declarations": data.get("counts", {}).get("ordered_decls"),
            "remaining_external_templates": data.get("remaining_external_templates", []),
            "charon_command": data["charon_command"],
            "aeneas_command": data.get("aeneas_command"),
            "rustflags": data.get("rustflags", ""),
            "result": explanation,
        })
    for folder, explanation in (
        ("SelectedBaseline", "Seven dead Step metadata changes permit Aeneas generation but leave six opaque RangeFull method templates. No template is filled or accepted."),
        ("Selected", "Seven dead Step metadata changes retain every actual closed-graph body, but Aeneas rejects the uncalled actual RangeFull get_mut/index_mut at slice/index.rs621 and642: Can't copy a mutable borrow."),
    ):
        directory = HERE / folder
        data = json.loads((directory / "review.json").read_text())
        files += [directory / name for name in ("selected.llbc", "changes.json", "review.json", "aeneas.log")]
        if (directory / "select-script.py").exists():
            files.append(directory / "select-script.py")
        cases.append({"profile": folder, "accepted_reference": False,
                      "aeneas_exit_code": data["aeneas_exit_code"],
                      "exact_reversible_changes": data["reversible_changes"],
                      "computational_declarations_unchanged": data["unchanged_computational_declarations"],
                      "remaining_external_templates": data["remaining_external_templates"],
                      "result": explanation})
    probe = HERE / "SharedIndexProbe"
    command = ["python3", ".deps/run-signal-lean.py", "SpqrReference/SharedIndexProbe/Generated/Types",
               "SpqrReference/SharedIndexProbe/Generated/Funs"]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    output = result.stdout + result.stderr
    assert result.returncode != 0
    assert "Fields missing: `get_mut`, `index_mut`" in output
    (probe / "lean.log").write_text(output)
    data = json.loads((probe / "report.json").read_text())
    assert data["aeneas_exit_code"] == 0 and data["templates"] == []
    assert data["all_computational_declarations_identical"]
    assert data["excluded_computational_roots"] == [116, 120]
    files += [probe / name for name in ("selected.llbc", "changes.json", "report.json", "aeneas.log", "lean.log")]
    files += sorted((probe / "Generated").glob("*.lean"))
    cases.append({
        "profile": "SharedIndexProbe", "accepted_reference": False,
        "aeneas_exit_code": 0, "external_templates": [],
        "lean_exit_code": result.returncode, "lean_command": command,
        "exact_reversible_changes": data["reversible_changes"],
        "all_computational_declarations_identical": True,
        "excluded_computational_roots": [116, 120],
        "result": "Unused mutable dictionary slots/impl pointers and codegen roots can be removed while preserving all original bodies, but the official SliceIndex Lean structure still requires get_mut and index_mut. Lean rejects the incomplete record. No replacement methods or custom model were supplied.",
    })
    report = {
        "full_serializer_refined": False,
        "all_profiles_in_this_report_unaccepted": True,
        "source_patches": [], "tool_patches": [], "custom_models_added": [],
        "spqr_commit": "06959b4708f9b7b1e94d0f8cc835f3958c077e94",
        "cases": cases,
        "completed_separate_slice": "VarintSelected/VarintGenerated and VarintReference/VarintCircuit; see proof-report.json and separate independent selection acceptance.",
        "remaining_composition_obligation": "Obtain a faithful, typechecking actual RangeFull indexing dictionary/wrapper without opaque assumptions, then compose Message.serialize with the proved varints, actual enum conversions, Vec initialization/push/extend and root SpqrMessage.content.",
        "source_sha256": {str(p.relative_to(ROOT)): digest(p) for p in files},
        "historical_output_paths": "The first empty-output and partial-template runs were moved to Generated/serialize_lookup_baseline and GeneratedSelectedBaseline; historical inventory paths retain their original invocation spelling.",
    }
    (HERE / "serializer-boundary-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Recorded nine unaccepted serializer profiles, including the reproducible missing-field Lean failure.")


if __name__ == "__main__":
    main()
