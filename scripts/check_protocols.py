#!/usr/bin/env python3
"""Compile MPC protocol programs and compare their source/circuits to oracles.

No native MPC execution or throughput measurement. Only public synthetic inputs.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from scripts.clear_circuit import execute
from test_support.circuit import input_tokens
from test_support.reference import mac, signal_reference


def fixtures(mode, batch, size):
    fields = [('key', 16), ('iv', 12)]
    if mode in ('signal-tls-send', 'signal-open-check'):
        fields += [('chain', 32), ('ratchet', 33), ('sender', 33), ('recipient', 33),
                   ('addresses', 36), ('pq_key', 32), ('pq_message', 16)]
    fields += [('text', size)]
    inputs = {name: [hashlib.shake_256(f'public-test-{name}-{lane}'.encode()).digest(length)
                     for lane in range(batch)] for name, length in fields}
    if mode in ('signal-tls-send', 'signal-open-check'):
        for name in ('ratchet', 'sender', 'recipient'):
            inputs[name] = [b'\x05' + value[1:] for value in inputs[name]]
        inputs['addresses'] = [b'\x00' + x[1:17] + b'\x01\x00' + x[19:35] + b'\x02'
                               for x in inputs['addresses']]
    records, signal_messages, next_chains = [], [], []
    for lane in range(batch):
        x = {name: values[lane] for name, values in inputs.items()}
        payload = x['text']
        if mode in ('signal-tls-send', 'signal-open-check'):
            padded = payload + b'\x80' + bytes((-len(payload) - 1) % 80)
            payload = signal_reference(x['chain'], padded, x['pq_key'], x['pq_message'], x['addresses'],
                                       x['ratchet'], x['sender'], x['recipient'])
            signal_messages.append(payload)
            next_chains.append(mac(x['chain'], b'\x02'))
        inner = payload + b'\x17'
        header = b'\x17\x03\x03' + (len(inner) + 16).to_bytes(2, 'big')
        records.append(header + AESGCM(x['key']).encrypt(x['iv'], inner, header))
    if mode.endswith('check'):
        wires = [record[5:] for record in records] if mode == 'tls-open-check' else signal_messages
        expected = [1] * batch
        if batch > 1:
            wires[-1] = wires[-1][:-1] + bytes([wires[-1][-1] ^ 1])
            expected[-1] = 0
        inputs['incoming'] = wires
        if mode == 'signal-open-check':
            inputs['expected_next'] = next_chains
        return inputs, expected, len(records[0]) if mode == 'tls-open-check' else None
    expected = [int.from_bytes(record[offset:offset + 8], 'big')
                for offset in range(0, len(records[0]), 8) for record in records]
    return inputs, expected, len(records[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--modes', nargs='+', choices=['tls-seal', 'signal-tls-send', 'tls-open-check', 'signal-open-check'],
                        default=['tls-seal', 'signal-tls-send', 'tls-open-check', 'signal-open-check'])
    parser.add_argument('--batches', nargs='+', type=int, default=[1, 16])
    parser.add_argument('--message-bytes', type=int, default=80)
    args = parser.parse_args()
    if any(not 1 <= x <= 64 for x in args.batches) or not 0 <= args.message_bytes <= 4096:
        parser.error('batches must be 1..64; message size must be 0..4096')
    backend = ROOT / '.deps/MP-SPDZ'
    source = ROOT / 'programs/protocol.mpc'
    shutil.copy2(source, backend / 'Programs/Source/protocol.mpc')
    environment = os.environ.copy()
    environment['PYTHONPATH'] = str(ROOT) + os.pathsep + environment.get('PYTHONPATH', '')
    reports = []
    for mode in args.modes:
        for batch in args.batches:
            arguments = [mode, str(batch), '5', str(args.message_bytes)]
            name = 'protocol-' + '-'.join(arguments)
            directory = ROOT / 'benchmarks/results/raw' / name
            directory.mkdir(parents=True, exist_ok=True)
            command = [sys.executable, './compile.py', '-M', '-B', '128', 'protocol'] + arguments
            result = subprocess.run(command, cwd=backend, env=environment, text=True,
                                    capture_output=True, timeout=600)
            log = result.stdout + result.stderr
            (directory / 'compile.log').write_text(log)
            if result.returncode:
                raise RuntimeError(f'compile failed; see {directory / "compile.log"}:\n{log[-4000:]}')
            inputs, expected, record_bytes = fixtures(mode, batch, args.message_bytes)
            observed = execute(source, backend / 'Programs/Circuits', ['protocol'] + arguments, input_tokens(inputs))
            if observed != expected:
                raise AssertionError(f'{name}: source/circuit output mismatch')
            costs = {}
            for label, pattern in [('bit_triples', r'(\d+) bit triples'), ('vm_rounds', r'(\d+) virtual machine rounds')]:
                matches = re.findall(pattern, log)
                costs[label] = int(matches[-1]) if matches else None
            report = {'mode': mode, 'batch': batch, 'message_bytes': args.message_bytes,
                      'tls_record_bytes': record_bytes, 'all_outputs_match': True,
                      'output_chunks_checked': len(expected), 'compiled_costs': costs,
                      'bytecode_sha256': hashlib.sha256((backend / f'Programs/Bytecode/{name}-0.bc').read_bytes()).hexdigest()}
            reports.append(report)
            print(json.dumps(report), flush=True)
    sources = [source, ROOT / 'scripts/clear_circuit.py', ROOT / 'test_support/reference.py',
               ROOT / 'test_support/circuit.py', Path(__file__).resolve()] + sorted((ROOT / 'tls_mpc').glob('*.py'))
    output = {'kind': 'cleartext_protocol_differential_checks_and_static_costs',
              'mp_spdz': '0.4.4', 'signal_reference': '0.106.1',
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
              'cases': reports,
              'limitations': ['No native MPC execution, network timings, or live Signal interoperability tested.',
                              'Composed send wraps SignalMessage directly in TLS; sealed sender and server API are pending.',
                              'SPQR message/key are supplied as shared inputs, not generated by an SPQR implementation.',
                              'The Python compiler and cryptographic circuits are not covered by Lean proofs.']}
    (ROOT / 'benchmarks/results/protocol-checks.json').write_text(json.dumps(output, indent=2) + '\n')


if __name__ == '__main__':
    main()
