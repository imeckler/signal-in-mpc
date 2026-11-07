#!/usr/bin/env python3
"""Audit the actual Rust unpadding to shared receive-result composition proof."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest_path = REFERENCE / "Extraction/pkcs7_unpad_selected.json"
    manifest = json.loads(manifest_path.read_text())
    llbc = REFERENCE / "Extraction/libsignal_pkcs7_unpad_selected.llbc"
    if digest(llbc) != manifest["llbc_sha256"]:
        raise ValueError("The accepted unpadding LLBC differs from its manifest")
    for filename, expected in manifest["generated_files"].items():
        if digest(REFERENCE / filename) != expected:
            raise ValueError(f"The accepted generated reference differs: {filename}")
    own = [HERE / name for name in ["PaddingBridge.lean", "LengthEncoding.lean", "PaddingChecks.lean"]]
    sources = own + [Path(__file__), ROOT / ".deps/run-signal-lean.py", manifest_path, llbc]
    sources += [REFERENCE / name for name in [
        "pins.json", "Extraction/unpad-review.json", "Extraction/unpad-sysroot-provenance.json",
        "LibSignalReference/Proofs/UnpadReference.lean", "LibSignalReference/Proofs/Unpad.lean"]]
    sources += [REFERENCE / name for name in manifest["generated_files"]]
    sources += [ROOT / name for name in ["TlsMpc/Signal/OpenResult.lean", "TlsMpc/Signal/Unpad.lean",
        "TlsMpc/ByteAuth.lean", "TlsMpc/ByteCircuit.lean", "TlsMpc/AigExport.lean", "TlsMpc/BvConstruct.lean"]]
    snapshot = {str(path.relative_to(ROOT)): digest(path) for path in sources}
    for path in own[:2]:
        source = re.sub(r"/\-.*?\-/", "", path.read_text(), flags=re.S)
        source = re.sub(r"--[^\n]*", "", source)
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", source):
            raise ValueError(f"Unaccepted proof command in {path}")
    subprocess.run(["lake", "build", "TlsMpc.Signal.OpenResult"], cwd=ROOT, check=True)
    modules = ["LibSignalReference/Generated/Unpadding/Types", "LibSignalReference/Generated/Unpadding/Funs",
               "LibSignalReference/Proofs/UnpadReference", "LibSignalReference/Proofs/Unpad",
               "AesInverseCircuitWork/PaddingBridge", "AesInverseCircuitWork/LengthEncoding",
               "AesInverseCircuitWork/PaddingChecks"]
    audit = subprocess.run([sys.executable, str(ROOT / ".deps/run-signal-lean.py"), *modules],
                           cwd=ROOT, text=True, capture_output=True)
    (HERE / "padding-axiom-report.txt").write_text(audit.stdout + audit.stderr)
    if audit.returncode:
        print(audit.stdout + audit.stderr)
        raise RuntimeError("Receive-result composition proof build failed")
    names = re.findall(r"^#print axioms (\S+)", (HERE / "PaddingChecks.lean").read_text(), re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit.stdout)
    if [name for name, _ in reports] != names:
        raise ValueError("The axiom audit did not cover exactly the named endpoints")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name, entries in reports:
        if {entry.strip() for entry in entries.split(",") if entry.strip()} - allowed:
            raise ValueError(f"Unaccepted assumptions in {name}")
    if snapshot != {str(path.relative_to(ROOT)): digest(path) for path in sources}:
        raise ValueError("Source changed during the audit")
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "kind": "actual_rust_unpadding_receive_result_composition",
        "source_sha256": snapshot,
        "reference_profile": "SignalReference/Extraction/pkcs7_unpad_selected.json",
        "checked_theorems": len(names), "theorems": names,
        "allowed_foundational_axioms": sorted(allowed), "custom_axioms": [],
        "axiom_report_sha256": digest(HERE / "padding-axiom-report.txt"),
        "domain": {"leading_bytes": "Arbitrary list; includes any public number of full CBC blocks",
                   "final_block_bytes": 16, "authentication_masks": [0, 255],
                   "strict_padding": True, "output_bytes": "9 + leading.length + 16",
                   "accepted_length_encoding": "Eight secret big-endian bytes",
                   "length_lossless_bound": "leading.length + 16 < 2^64",
                   "rejection": "Status, length and all candidate bytes are zero"},
        "numeric_compilation_refinement": True,
        "actual_reference_result_and_errors_preserved": True,
        "trust_boundary": ["Pinned Rust/Charon/Aeneas extraction and accepted official standard models",
                           "Native serialization, generic backend adapter and MPC backend remain unverified"],
        "not_claimed": ["Actual RustCrypto CBC or inverse-AES wrapper equivalence",
                        "Authentication computation correctness from a supplied mask",
                        "Native MPC execution or network performance"],
        "native_mpc_executed": False,
    }
    (HERE / "padding-proof-check.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Checked {len(names)} receive-result theorem endpoints against actual Rust strict unpadding.")


if __name__ == "__main__":
    main()
