#!/usr/bin/env python3
"""Check Lean Signal CBC artifacts using public fixtures and the generic backend."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def openssl_cbc(key, iv, plaintext):
    return subprocess.check_output(["openssl", "enc", "-aes-256-cbc", "-K", key.hex(),
                                    "-iv", iv.hex()], input=plaintext)


def fixtures():
    for length in (0, 1, 10, 15, 16, 17, 31, 32, 64):
        inputs, expected = [], []
        for lane in range(3):
            material = hashlib.shake_256(f"public-signal-cbc-{length}-{lane}".encode()).digest(48 + length)
            key, iv, message = material[:32], material[32:48], material[48:]
            if length == 10 and lane == 0:
                key = bytes.fromhex("4e22eb16d964779994222e82192ce9f747da72dc4abe49dfdeeb71d0ffe3796e")
                iv = bytes.fromhex("6f8a557ddc0a140c878063a6d5f31d3d")
                message = bytes.fromhex("30736294a124482a4159")
            result = openssl_cbc(key, iv, message)
            if length == 10 and lane == 0:
                assert result.hex() == "dd3f573ab4508b9ed0e45e0baf5608f3"
            inputs.append(key + iv + message)
            expected.append(result)
        yield ["signal-cbc-encrypt", str(length)], inputs, expected, "lean_lowering_only_rustcrypto_pending"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    options = parser.parse_args()
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    exporter = ROOT / ".lake/build/bin/emit_mpc"
    paths = [exporter, ROOT / "Main.lean", ROOT / "TlsMpc/AigExport.lean",
             ROOT / "TlsMpc/ByteCircuit.lean", ROOT / "TlsMpc/BvConstruct.lean",
             ROOT / "TlsMpc/Aes.lean", ROOT / "TlsMpc/AesSbox.lean",
             ROOT / "backend_adapter/aig.py", ROOT / "backend_adapter/boolean.py",
             ROOT / "programs/lean_artifact.mpc", ROOT / "TlsMpc/Signal/Cbc.lean",
             ROOT / "scripts/check_lean_crypto.py", Path(__file__).resolve()]
    before = {str(p.relative_to(ROOT)): digest(p) for p in paths}
    destination = ROOT / ".deps/signal-cbc-artifacts"
    destination.mkdir(parents=True, exist_ok=True)
    records = []
    for args, fields, expected, proof_scope in fixtures():
        path = destination / ("-".join(args) + ".json")
        start = time.perf_counter()
        with path.open("w") as output:
            subprocess.run([str(exporter), *args], stdout=output, cwd=ROOT, check=True, timeout=300)
        elapsed = time.perf_counter() - start
        image = load(path)
        observed = evaluate_lanes(image, fields)
        if observed != expected:
            raise AssertionError(f"Signal artifact mismatch: {args}")
        record = {"arguments": args, "input_bits": image["input_bits"],
                  "input_widths": image["input_widths"], "output_bits": len(image["outputs"]),
                  "fixture_lanes": len(fields), "all_outputs_match": True,
                  "proof_scope": proof_scope, "artifact_sha256": digest(path),
                  "native_export_seconds": elapsed, "adapter_statistics": statistics(image)}
        records.append(record)
        print(json.dumps(record), flush=True)
        if not options.skip_backend and args[1] in ('0', '16', '64'):
            record['mpc_compilations'] = []
            for batch in (1, 16):
                result = compile_and_check(path, fields, expected, batch)
                if result['bit_triples'] != record['adapter_statistics']['executed_and_gates'] * batch:
                    raise AssertionError(f'Unexpected AND cost: {args}, batch {batch}')
                record['mpc_compilations'].append(result)
            print(json.dumps({'arguments': args, 'mpc_compilations': record['mpc_compilations']}), flush=True)
    after = {str(p.relative_to(ROOT)): digest(p) for p in paths}
    if before != after:
        raise RuntimeError("sources or exporter changed during checks; refusing mixed provenance")
    report = {"kind": "lean_signal_cbc_checks", "cases": records, "source_sha256": before,
              "native_mpc_executed": False, "backend_bytecode_compiled": not options.skip_backend,
              "throughput_measured": False,
              "upstream_commit": "904c8dc8216073b078a5f2f5090e3da8382e6a92",
              "cbc_rustcrypto_equivalence_established": False,
              "note": "Synthetic public inputs only; CBC vectors do not establish RustCrypto refinement."}
    output = ROOT / "benchmarks/results/lean-signal-cbc-checks.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Wrote {output.relative_to(ROOT)}", flush=True)


if __name__ == "__main__":
    main()
