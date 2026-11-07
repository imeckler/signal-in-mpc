#!/usr/bin/env python3
"""Public differential fixtures for Lean-generated Signal artifacts.

Python is an independent test oracle only. All circuit construction is in Lean.
These checks do not establish the pending full RustCrypto/Aeneas refinement.
"""

import argparse
import hashlib
import hmac
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes

ADAPTER_PATHS = [ROOT / "backend_adapter/aig.py", ROOT / "backend_adapter/boolean.py",
                 ROOT / "programs/lean_artifact.mpc"]
LOADED_ADAPTER_HASHES = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in ADAPTER_PATHS}


def check_adapter_unchanged():
    current = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in ADAPTER_PATHS}
    if current != LOADED_ADAPTER_HASHES:
        raise RuntimeError("adapter sources changed during the run; refusing mixed-provenance results")


def reference_derive(raw):
    key, salt = raw[:32], raw[32:]
    seed = hmac.digest(key, b"\x01", "sha256")
    next_key = hmac.digest(key, b"\x02", "sha256")
    prk = hmac.digest(salt, seed, "sha256")
    previous, output = b"", b""
    for counter in range(1, 4):
        previous = hmac.digest(prk, previous + b"WhisperMessageKeys" + bytes([counter]), "sha256")
        output += previous
    return next_key + output[:80]


def reference_clamp(raw):
    result = bytearray(raw)
    result[0] &= 248
    result[31] &= 127
    result[31] |= 64
    return bytes(result)


def fixtures():
    # Exact published libsignal keys.rs::test_chain_key_derivation input/output.
    seed = bytes.fromhex("8ab72d6f4cc5ac0d387eaf463378ddb28edd07385b1cb01250c715982e7ad48f")
    raw = [seed + bytes(32), bytes(64), bytes([255]) * 64,
           hashlib.shake_256(b"signal-key-derivation-test").digest(64),
           seed + hashlib.sha256(b"signal-pqr-salt-test").digest()]
    expected = [reference_derive(value) for value in raw]
    assert expected[0][:32].hex() == "28e8f8fee54b801eef7c5cfb2f17f32c7b334485bbb70fac6ec10342a246d15d"
    assert expected[0][32:64].hex() == "bf51e9d75e0e31031051f82a2491ffc084fa298b7793bd9db620056febf45217"
    assert expected[0][64:96].hex() == "c6c77d6a73a354337a56435e34607dfe48e3ace14e77314dc6abc172e7a7030b"
    yield "signal-derive-keys", raw, expected
    raw = [bytes(32), bytes([255]) * 32, bytes(range(32)),
           hashlib.sha256(b"signal-scalar-clamp-test").digest()]
    # Exercise each of the five overwritten bits independently.
    for byte, bit in ((0, 0), (0, 1), (0, 2), (31, 6), (31, 7)):
        value = bytearray(32)
        value[byte] = 1 << bit
        raw.append(bytes(value))
    yield "signal-clamp", raw, [reference_clamp(value) for value in raw]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compile-backend", action="store_true",
                        help="Also compile MP-SPDZ bytecode and clear-interpret its generic adapter")
    parser.add_argument("--skip-build", action="store_true", help="Use the already-built Main exporter")
    parser.add_argument("--only", choices=("signal-derive-keys", "signal-clamp"),
                        help="Run only the selected changed artifact")
    parser.add_argument("--batches", nargs="+", type=int, default=[1, 16], choices=range(1, 129),
                        help="Public packing widths to compile (default: 1 16)")
    args = parser.parse_args()
    if not args.skip_build:
        subprocess.run(["lake", "build", "emit_mpc"], cwd=ROOT, check=True)
    records = []
    with tempfile.TemporaryDirectory(prefix="tls-mpc-lean-signal-") as directory:
        for name, raw, expected in fixtures():
            if args.only and args.only != name:
                continue
            check_adapter_unchanged()
            path = Path(directory) / (name + ".json")
            start = time.perf_counter()
            with path.open("w") as output:
                subprocess.run([str(ROOT / ".lake/build/bin/emit_mpc"), name], cwd=ROOT,
                               stdout=output, check=True, timeout=300)
            export_seconds = time.perf_counter() - start
            image = load(path)
            if evaluate_lanes(image, raw) != expected:
                raise AssertionError(f"Lean Signal artifact differs from the independent oracle: {name}")
            record = {"arguments": [name], "input_bits": image["input_bits"],
                      "output_bits": len(image["outputs"]), "nodes": len(image["nodes"]),
                      "and_gates": sum(node[0] == 2 for node in image["nodes"]),
                      "fixture_lanes": len(raw), "all_outputs_match": True,
                      "native_export_seconds": export_seconds,
                      "artifact_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                      "adapter_statistics": statistics(image),
                      "adapter_source_sha256": dict(LOADED_ADAPTER_HASHES),
                      "exporter_binary_sha256": hashlib.sha256(
                          (ROOT / ".lake/build/bin/emit_mpc").read_bytes()).hexdigest()}
            print(json.dumps(record), flush=True)
            if args.compile_backend:
                record["mpc_compilations"] = []
                for batch in args.batches:
                    check_adapter_unchanged()
                    compiled = compile_and_check(path, raw, expected, batch)
                    check_adapter_unchanged()
                    record["mpc_compilations"].append(compiled)
                print(json.dumps({"arguments": [name], "mpc_compilations": record["mpc_compilations"]}),
                      flush=True)
            records.append(record)
    sources = list((ROOT / "TlsMpc/Signal").glob("*.lean")) + [
        ROOT / "TlsMpc/HmacPrepared.lean", ROOT / "TlsMpc/TlsKdfPrepared.lean",
        ROOT / "TlsMpc/Sha256.lean", ROOT / "TlsMpc/ByteCircuit.lean",
        ROOT / "TlsMpc/BvConstruct.lean", ROOT / "TlsMpc/AigExport.lean",
        *ADAPTER_PATHS, ROOT / "Main.lean", Path(__file__).resolve()]
    report = {"kind": "lean_signal_artifact_checks", "cases": records,
              "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in sources},
              "upstream_commit": "904c8dc8216073b078a5f2f5090e3da8382e6a92",
              "native_mpc_executed": False, "throughput_measured": False,
              "limitations": [
                  "The complete RustCrypto-to-Lean key derivation refinement remains incomplete.",
                  "The checked Rust reference refinements cover key projections/constructors and dalek clamping.",
                  "Counter progression, authenticated state commit, AES-CBC, SignalMessage, SPQR and full sessions remain work.",
                  "AIG gate counts use unoptimized Boolean lowering and are not WAN throughput measurements.",
                  "Any opened test outputs are public synthetic fixtures; production key outputs must remain shared."]}
    check_adapter_unchanged()
    destination = ROOT / "benchmarks/results" / (
        f"lean-{args.only}-checks.json" if args.only else "lean-signal-checks.json")
    destination.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
