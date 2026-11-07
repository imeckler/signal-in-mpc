#!/usr/bin/env python3
"""Check benchmark source/circuits against native crypto and record static costs.

Does not execute MP-SPDZ bytecode or any MPC/network protocol.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

from run_benchmark import ROOT, fixtures, input_tokens
from clear_circuit import execute


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batches', type=int, nargs='+', default=[1, 16])
    parser.add_argument('--kernels', nargs='+', default=['aes128', 'aes256', 'hmac_sha256_1'],
                        choices=['aes128', 'aes256', 'hmac_sha256_1'])
    args = parser.parse_args()
    if any(x <= 0 for x in args.batches):
        parser.error('batches must be positive')
    backend = ROOT / '.deps/MP-SPDZ'
    shutil.copy2(ROOT / 'benchmarks/programs/crypto.mpc', backend / 'Programs/Source/crypto.mpc')
    records = []
    for kernel in args.kernels:
        for batch in args.batches:
            parties = 5
            name = f'crypto-{kernel}-{batch}-{parties}'
            directory = ROOT / 'benchmarks/results/raw' / f'correctness-{name}'
            directory.mkdir(parents=True, exist_ok=True)
            inputs, expected = fixtures(kernel, parties, batch)
            tokens = [input_tokens(player, kernel, batch) for player in inputs]
            compile_command = ['python3', './compile.py', '-M', '-B', '128', 'crypto',
                               kernel, str(batch), str(parties)]
            compiled = subprocess.run(compile_command, cwd=backend, check=True,
                                      capture_output=True, text=True, timeout=300)
            compile_log = compiled.stdout + compiled.stderr
            (directory / 'compile.log').write_text(compile_log)
            observed = execute(ROOT / 'benchmarks/programs/crypto.mpc', backend / 'Programs/Circuits',
                               ['crypto', kernel, str(batch), str(parties)], tokens)
            if observed != expected:
                raise RuntimeError(f'{name}: output mismatch ({len(observed)} outputs, expected {len(expected)}); {directory}')
            costs = {}
            for label, pattern in [('bit_triples', r'(\d+) bit triples'),
                                   ('vm_rounds', r'(\d+) virtual machine rounds')]:
                values = re.findall(pattern, compile_log)
                costs[label] = int(values[-1]) if values else None
            record = {'kernel': kernel, 'batch': batch, 'all_outputs_match': True,
                      'oracle': 'OpenSSL AES ECB' if kernel.startswith('aes') else 'Python hmac/hashlib',
                      'public_fixture_fragment_count_per_key': parties,
                      'input_owners_preserved_in_cleartext_model': True,
                      'compiled_costs': costs,
                      'compile_command': compile_command,
                      'bytecode_sha256': hashlib.sha256(
                          (backend / f'Programs/Bytecode/{name}-0.bc').read_bytes()).hexdigest()}
            records.append(record)
            print(json.dumps(record), flush=True)
    report = {
        'schema_version': 1, 'kind': 'cleartext_differential_correctness_and_static_costs',
        'backend_version': 'MP-SPDZ v0.4.4',
        'source_sha256': hashlib.sha256((ROOT / 'benchmarks/programs/crypto.mpc').read_bytes()).hexdigest(),
        'cases': records,
        'limitations': [
            'Source/circuit interpretation exercises no MPC protocol or networking.',
            'MP-SPDZ bytecode is compiled for costs but not executed by this check.',
            'VM rounds are compiler statistics, not measured network round trips.',
            'No timing or throughput claim is made.',
            'The cleartext circuit interpreter and benchmark programs are unverified.',
            'These primitive checks do not test TLS or Signal state machines.',
        ],
    }
    (ROOT / 'benchmarks/results/kernel-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
