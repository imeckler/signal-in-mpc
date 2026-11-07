#!/usr/bin/env python3
"""Run actual malicious MPC processes locally with reproducible test inputs.

This measures a kernel or protocol circuit on loopback, with live preprocessing.
It does not measure a Signal send, WAN performance, or an online-only phase.
Never reads production keys or credentials. The deterministic fixture fragments
are public test data, even though imported through the runtime's private inputs.
"""

import argparse
import hashlib
import hmac
import json
import os
from pathlib import Path
import platform
import re
import shutil
import socket
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def fragment(kernel, parties, lane, party, purpose, size):
    domain = f'tls-mpc-public-test-fixture-v1/{kernel}/{parties}/{lane}/{party}/{purpose}'
    return int.from_bytes(hashlib.sha256(domain.encode()).digest()[:size], 'big')


def fixtures(kernel, parties, batch):
    key_size = 16 if kernel == 'aes128' else 32
    inputs = [[] for _ in range(parties)]
    keys, blocks = [0] * batch, [0] * batch
    for party in range(parties):
        for lane in range(batch):
            part = fragment(kernel, parties, lane, party, 'key', key_size)
            inputs[party].append(part)
            keys[lane] ^= part
    if kernel.startswith('aes'):
        for party in range(parties):
            for lane in range(batch):
                part = fragment(kernel, parties, lane, party, 'block', 16)
                inputs[party].append(part)
                blocks[lane] ^= part
    expected = []
    for key, block in zip(keys, blocks):
        key_bytes = key.to_bytes(key_size, 'big')
        if kernel == 'hmac_sha256_1':
            result = hmac.digest(key_bytes, b'\x01', 'sha256')
        else:
            result = subprocess.run(
                ['openssl', 'enc', f'-aes-{key_size * 8}-ecb', '-K', key_bytes.hex(),
                 '-nopad', '-nosalt'], input=block.to_bytes(16, 'big'),
                check=True, capture_output=True).stdout
        expected.append(int.from_bytes(result, 'big'))
    return inputs, expected


def input_tokens(values, kernel, batch):
    key_bits = 128 if kernel == 'aes128' else 256
    return [(value >> shift) & ((1 << 64) - 1)
            for index, value in enumerate(values)
            for shift in range(0, key_bits if index < batch else 128, 64)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend', choices=['shamir5', 'rep3'], default='shamir5')
    operation = parser.add_mutually_exclusive_group()
    operation.add_argument('--kernel', choices=['aes128', 'aes256', 'hmac_sha256_1'])
    operation.add_argument('--protocol', choices=['tls-seal', 'signal-tls-send', 'tls-open-check', 'signal-open-check'])
    parser.add_argument('--message-bytes', type=int, default=80)
    parser.add_argument('--batch', type=int, default=1)
    parser.add_argument('--security-bits', type=int, default=64,
                        help='statistical parameter, recorded explicitly; not a production choice')
    parser.add_argument('--port', type=int, default=18200)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--mp-spdz', type=Path, default=ROOT / '.deps/MP-SPDZ')
    args = parser.parse_args()
    if args.kernel is None and args.protocol is None:
        args.kernel = 'aes128'
    if args.batch < 1 or args.timeout < 1 or args.security_bits < 1:
        parser.error('batch, timeout, and security bits must be positive')
    if args.protocol and (args.batch > 64 or not 0 <= args.message_bytes <= 4096):
        parser.error('protocol batches must be 1..64; message size must be 0..4096')
    parties, threshold, binary = {
        'shamir5': (5, 2, 'malicious-ccd-party.x'),
        'rep3': (3, 1, 'malicious-rep-bin-party.x'),
    }[args.backend]
    backend = args.mp_spdz.resolve()
    if not (backend / binary).is_file():
        parser.error(f'build {backend / binary} first')
    try:
        with socket.socket() as probe:
            probe.bind(('127.0.0.1', 0))
    except OSError as error:
        parser.error(f'local sockets unavailable ({error}); run on a host that permits '
                     'localhost networking. No MPC timing was measured.')
    stem = 'protocol' if args.protocol else 'crypto'
    program_arguments = [args.protocol or args.kernel, str(args.batch), str(parties)]
    if args.protocol:
        program_arguments.append(str(args.message_bytes))
    name = stem + '-' + '-'.join(program_arguments)
    stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()) + f'-{time.time_ns() % 1_000_000_000:09d}'
    run_dir = ROOT / 'benchmarks/results/raw' / f'{stamp}-{args.backend}-{name}'
    run_dir.mkdir(parents=True)
    program_file = backend / f'Programs/Source/{stem}.mpc'
    source_file = ROOT / ('programs/protocol.mpc' if args.protocol else 'benchmarks/programs/crypto.mpc')
    shutil.copy2(source_file, program_file)
    if args.protocol:
        from check_protocols import fixtures as protocol_fixtures
        from test_support.circuit import input_tokens as protocol_input_tokens
        fixture_inputs, expected, _ = protocol_fixtures(args.protocol, args.batch, args.message_bytes)
        tokens_by_party = protocol_input_tokens(fixture_inputs, parties)
    else:
        fixture_inputs, expected = fixtures(args.kernel, parties, args.batch)
        tokens_by_party = [input_tokens(values, args.kernel, args.batch) for values in fixture_inputs]
    player_data = backend / 'Player-Data'
    player_data.mkdir(exist_ok=True)
    # A unique prefix avoids overwriting unrelated Player-Data input files.
    input_prefix = str(run_dir / 'fixture')
    for party, tokens in enumerate(tokens_by_party):
        Path(f'{input_prefix}-P{party}-0').write_text('\n'.join(map(str, tokens)) + '\n')
    compile_command = [sys.executable, './compile.py', '-M', '-B', '128', stem] + program_arguments
    environment = os.environ.copy()
    environment['PYTHONPATH'] = str(ROOT) + os.pathsep + environment.get('PYTHONPATH', '')
    with (run_dir / 'compile.log').open('w') as log:
        subprocess.run(compile_command, cwd=backend, env=environment, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=args.timeout)
    processes, logs, commands = [], [], []
    started = time.monotonic()
    try:
        for party in range(parties):
            command = [str(backend / binary), str(party), name, '-h', 'localhost',
                       '-pn', str(args.port), '-S', str(args.security_bits),
                       '-IF', input_prefix]
            if args.backend == 'shamir5':
                command += ['-N', str(parties), '-T', str(threshold)]
            log = (run_dir / f'party-{party}.log').open('w')
            logs.append(log)
            commands.append(command)
            processes.append(subprocess.Popen(command, cwd=backend, stdout=log,
                                              stderr=subprocess.STDOUT))
        for process in processes:
            remaining = args.timeout - (time.monotonic() - started)
            status = process.wait(timeout=max(0.01, remaining))
            if status:
                raise RuntimeError(f'MPC party exited with {status}; inspect {run_dir}')
    finally:
        for process in processes:
            if process.poll() is None:
                process.terminate()
        for process in processes:
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
        for log in logs:
            log.close()
    elapsed = time.monotonic() - started
    party0 = (run_dir / 'party-0.log').read_text()
    observed = [int(x, 16) for x in re.findall(r'Reg\[\d+\]\s*=\s*0x([0-9a-fA-F]+)', party0)]
    if observed != expected:
        raise RuntimeError(f'circuit output mismatch ({len(observed)} outputs, expected {len(expected)}); {run_dir}')
    vm_times = [float(x) for x in re.findall(r'^Time\s*=\s*([0-9.eE+-]+)', party0, re.MULTILINE)]
    report = {
        'schema_version': 1,
        'measurement_kind': 'local_loopback_circuit_with_live_preprocessing',
        'timestamp_utc': stamp, 'backend': args.backend, 'parties': parties,
        'malicious_collusion_limit': threshold, 'statistical_security_bits': args.security_bits,
        'kernel': args.kernel, 'batch': args.batch, 'correct_outputs': len(observed),
        'protocol': args.protocol, 'message_bytes': args.message_bytes if args.protocol else None,
        'wall_seconds_including_process_startup': elapsed,
        'circuit_evaluations_per_wall_second': args.batch / elapsed,
        'party0_vm_seconds': vm_times,
        'host': {'system': platform.system(), 'release': platform.release(),
                 'machine': platform.machine(), 'cpu_count': os.cpu_count()},
        'source_sha256': hashlib.sha256(program_file.read_bytes()).hexdigest(),
        'backend_binary_sha256': hashlib.sha256((backend / binary).read_bytes()).hexdigest(),
        'compile_command': compile_command, 'party_commands': commands,
        'logs_relative_to_repo': str(run_dir.relative_to(ROOT)),
        'limitations': [
            'All parties share one host; no WAN latency or bandwidth emulation.',
            'Synthetic public test fixtures, imported as private input fragments.',
            'Includes live preprocessing; no fake or reused preprocessing.',
            'AES benchmark includes key expansion per block.',
            'Not a complete Signal client or server-delivery benchmark.',
            'Protocol composition uses supplied PQ inputs; sealed sender and server API are pending.',
            'No machine-checked correctness claim for this benchmark program or backend.',
            'The statistical parameter is a benchmark setting, not a production security decision.',
        ],
    }
    if args.protocol:
        report['library_source_sha256'] = {
            str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted((ROOT / 'tls_mpc').glob('*.py'))}
    result = ROOT / 'benchmarks/results' / f'{stamp}-{args.backend}-{name}.json'
    result.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': str(result.relative_to(ROOT)),
                      'correct_outputs': len(observed), 'wall_seconds': elapsed,
                      'circuit_evaluations_per_second': args.batch / elapsed}))


if __name__ == '__main__':
    main()
