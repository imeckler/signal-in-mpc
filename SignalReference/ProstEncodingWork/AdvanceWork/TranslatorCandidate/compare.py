#!/usr/bin/env python3
"""Run isolated baseline/candidate translations; no accepted artifacts change."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[2]
ROOT = REFERENCE.parent
TARGETS = {
    "Regressions": (HERE / "Regressions/calls.llbc", "NeverRegression"),
    "Slice": (HERE / "SliceSelected/slice.llbc", "BytesSliceAdvance"),
    "Varint": (REFERENCE / "ProstEncodingWork/Artifacts/EncodeSelected/selected.llbc", "ProstEncoding"),
    "UInt32": (REFERENCE / "SignalMessageWork/Artifacts/UInt32Selected/selected.llbc", "ProstUInt32"),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("label", choices=["Baseline", "Candidate"])
    args = parser.parse_args()
    binary = HERE / "Bin" / args.label.lower()
    version = subprocess.check_output([str(binary), "-version"], text=True).strip()
    assert "5b9dcf33dccdb1560ea7203ac57ea202476b6ed3" in version
    reports = {}
    for target, (llbc, namespace) in TARGETS.items():
        directory = HERE / "Generated" / args.label / target
        directory.mkdir(parents=True, exist_ok=True)
        for old in directory.glob("*.lean"):
            old.unlink()
        subdir = "/" + str(directory.relative_to(REFERENCE))
        command = [str(binary), "-backend", "lean", str(llbc), "-dest", str(REFERENCE),
                   "-subdir", subdir, "-namespace", namespace, "-split-files",
                   "-warnings-as-errors", "-no-progress-bar"]
        with (directory / "translation.log").open("w") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        report = {"exit_code": result.returncode, "llbc_sha256": digest(llbc),
                  "command": command,
                  "generated_sha256": {p.name: digest(p) for p in directory.glob("*.lean")},
                  "external_templates": [p.name for p in directory.glob("*_Template.lean")],
                  "log_sha256": digest(directory / "translation.log")}
        if args.label == "Baseline":
            expected = 2 if target in ("Regressions", "Slice") else 0
            assert result.returncode == expected, (target, report)
            if expected:
                assert "Unexpected result: Cps.Unit" in (directory / "translation.log").read_text()
        else:
            assert result.returncode == 0, (target, report)
            assert report["external_templates"] == [], (target, report)
            if target in ("Varint", "UInt32"):
                baseline = HERE / "Generated/Baseline" / target
                for path in directory.glob("*.lean"):
                    original = (baseline / path.name).read_text()
                    normalized = path.read_text().replace("Generated.Candidate.", "Generated.Baseline.")
                    assert original == normalized, path
                report["identical_to_baseline_except_import_destination"] = True
        reports[target] = report
        print(f"{args.label} {target}: exit {result.returncode}, templates {report['external_templates']}")
    output = {"candidate_only": True, "accepted_translator": False, "version": version,
              "binary_sha256": digest(binary), "source_commit": "5b9dcf33dccdb1560ea7203ac57ea202476b6ed3",
              "accepted_binary_sha256": digest(ROOT / ".deps/aeneas-2026-08-27/aeneas"),
              "accepted_models_sha256": {"Primitives.lean": digest(ROOT / ".deps/aeneas-2026-08-27/backends/lean/Aeneas/Std/Primitives.lean")},
              "targets": reports, "script_sha256": digest(Path(__file__))}
    (HERE / (args.label.lower() + "-comparison.json")).write_text(json.dumps(output, indent=2) + "\n")


if __name__ == "__main__":
    main()
