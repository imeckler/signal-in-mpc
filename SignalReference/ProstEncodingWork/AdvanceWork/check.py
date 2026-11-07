#!/usr/bin/env python3
"""Check the pinned actual-source advance reproducer; no proof is accepted."""
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
spec = importlib.util.spec_from_file_location("advance_extract", HERE / "extract.py")
extraction = importlib.util.module_from_spec(spec)
spec.loader.exec_module(extraction)


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
    for path, expected in extraction.SOURCE_HASHES.items():
        assert digest(ROOT / path) == expected, path
    rust = ROOT / ".deps/libsignal-vendor/bytes-1.12.0/src"
    selected_body = """fn advance(&mut self, cnt: usize) {
        if self.len() < cnt {
            panic_advance(&TryGetError {
                requested: cnt,
                available: self.len(),
            });
        }

        *self = &self[cnt..];
    }"""
    panic_body = """fn panic_advance(error_info: &TryGetError) -> ! {
    panic!(
        "advance out of bounds: the len is {} but advancing by {}",
        error_info.available, error_info.requested
    );
}"""
    assert selected_body in (rust / "buf/buf_impl.rs").read_text()
    assert panic_body in (rust / "lib.rs").read_text()
    profiles = {}
    files = [Path(__file__), HERE / "extract.py", HERE / "Interp.ml", HERE / "InterpStatements.ml"]
    for profile, expected_error in (
        ("SliceImplsClosed", "Unexpected result: Cps.Unit"),
        ("SliceInlinePanic", "Arrow types are not supported yet"),
    ):
        directory = HERE / "Artifacts" / profile
        llbc = directory / "slice_advance.llbc"
        inventory = json.loads((directory / "inventory.json").read_text())
        assert inventory["charon_exit_code"] == 0 and not inventory["has_errors"]
        assert inventory["aeneas_exit_code"] != 0
        assert inventory["source_patches"] == [] and inventory["accepted_reference"] is False
        assert inventory["selected_advance_has_body"] is True
        assert inventory["script_sha256"] == digest(HERE / "extract.py")
        assert inventory["rustflags"] == extraction.RUSTFLAGS.get(profile, "")
        tr = json.loads(llbc.read_text())["translated"]
        bodies = [(i, f) for i, f in enumerate(tr["fun_decls"]) if f and f["body"] != "Opaque"]
        assert len(bodies) == 2
        advance = next((i, f) for i, f in bodies if f["item_meta"]["name"][-1] == {"Ident": ["advance", 0]})
        panic = next((i, f) for i, f in bodies if f["item_meta"]["name"][-1] == {"Ident": ["panic_advance", 0]})
        assert advance[1]["item_meta"]["source_text"] == selected_body
        assert panic[1]["item_meta"]["source_text"] == panic_body
        assert panic[1]["signature"]["output"] == {"Untagged": "Never"}
        calls = sorted({node["Regular"] for node in nodes(advance[1]["body"])
                        if isinstance(node, dict) and isinstance(node.get("Regular"), int)})
        assert panic[0] in calls  # The real cold call survives the inlining probe.
        log = (directory / "aeneas.log").read_text()
        assert expected_error in log
        profiles[profile] = {
            "charon_succeeded": True,
            "aeneas_succeeded": False,
            "expected_error": expected_error,
            "actual_computational_declarations": [i for i, _ in bodies],
            "unchanged_actual_source_text": True,
            "actual_panic_call_retained": True,
            "rustflags": inventory["rustflags"],
            "source_patches": [],
            "llbc_preprocessing": [],
            "standard_models_changed": [],
            "charon_command": inventory["charon_command"],
            "aeneas_command": inventory["aeneas_command"],
        }
        files.extend([llbc, directory / "inventory.json", directory / "charon.log", directory / "aeneas.log"])
    interp = (HERE / "Interp.ml").read_text()
    statements = (HERE / "InterpStatements.ml").read_text()
    assert '| Unit | Break _ | Continue _ ->' in interp
    assert '"\\nUnexpected result: "' in interp
    assert 'let ret_spc = mk_fresh_symbolic_value span ctx ret_sv_ty' in statements
    assert '([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ span cc)' in statements
    trace = HERE / "Artifacts/SliceImplsClosed/trace.log"
    trace_text = trace.read_text()
    assert "Unexpected result: Cps.Unit" in trace_text
    assert "_7 : ! ->" in trace_text
    assert "Compiler source: interp/Interp.ml, line 585" in trace_text
    files.append(trace)
    output = {
        "accepted_reference": False,
        "accepted_proof_endpoints": [],
        "diagnostic_checks_passed": True,
        "target": "Actual bytes 1.12.0 Buf for &[u8]::advance",
        "source_package": "bytes@1.12.0 locked by libsignal v0.106.1",
        "profiles": profiles,
        "failure_analysis": {
            "observed": "The out-of-bounds branch returns Cps.Unit from its Never-returning panic_advance call; finishing the caller rejects Cps.Unit.",
            "pinned_call_logic": "InterpStatements.ml:1427-1430 creates a symbolic result for every return type; 1578-1582 assumes successful continuation, including Never.",
            "pinned_rejection": "Interp.ml:583-589 rejects Unit, Break and Continue as function-final results.",
            "inlining_probe": "The actual cold panic_advance call remains; compiler inlining additionally exposes unsupported formatting Arrow types.",
            "next_candidate_fix_unproved": "Support the uninhabited successful-return branch at the translator level while retaining the called Result's failure/divergence. Do not replace arbitrary Never calls with panic.",
        },
        "required_future_equivalence": [
            "For cnt <= self.length, return the exact suffix and updated shared-slice reference.",
            "For cnt > self.length, preserve the actual panic helper's Result behavior.",
            "Compose the concrete Buf dictionary with actual Vec::put and generated length-delimited field encoding.",
        ],
        "diagnostic_generated_lean_not_accepted": "Artifacts/SliceTrace/SliceAdvance.lean contains failed/opaque declarations and is never imported or audited as a proof.",
        "tool_source_urls": {
            name: "https://raw.githubusercontent.com/AeneasVerif/aeneas/5b9dcf33dccdb1560ea7203ac57ea202476b6ed3/src/interp/" + name
            for name in ("Interp.ml", "InterpStatements.ml")
        },
        "sha256": {str(p.relative_to(ROOT)): digest(p) for p in files},
    }
    (HERE / "report.json").write_text(json.dumps(output, indent=2) + "\n")
    print("Confirmed expected actual-source failures; no advance refinement accepted.")


if __name__ == "__main__":
    main()
