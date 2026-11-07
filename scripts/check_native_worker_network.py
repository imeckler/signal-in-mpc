#!/usr/bin/env python3
"""Run five real workers on loopback using fresh, disposable test keys.

Optional synthetic-peer fixtures check ECDH, TLS key derivation, record opening,
Finished verification and ciphertext creation. Certificate authentication is a
fixture decision; this is not a full TLS handshake or an erasure/WAN test.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import secrets
import selectors
import subprocess
import sys
import time
from datetime import datetime, timezone

from pin_tls_worker import build

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def exchange(processes, sequence, opcode, payload, size, timeout, status=0):
    started = time.monotonic()
    buffers = [bytearray() for _ in processes]
    with selectors.DefaultSelector() as selector:
        for party, p in enumerate(processes):
            selector.register(p.stdout, selectors.EVENT_READ, party)
            p.stdin.write(bytes([opcode]) + sequence.to_bytes(8, 'big') +
                          len(payload).to_bytes(4, 'big') + payload)
            p.stdin.flush()
        completed = set()
        while len(completed) < len(processes):
            remaining = timeout - (time.monotonic() - started)
            if remaining <= 0:
                raise TimeoutError(f'native opcode {opcode} timed out')
            for key, _ in selector.select(min(remaining, 1)):
                party = key.data
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    raise RuntimeError(f'party {party} closed RPC at opcode {opcode}')
                buffers[party].extend(chunk)
                buf = buffers[party]
                if len(buf) >= 5:
                    actual_size = int.from_bytes(buf[1:5], 'big')
                    if buf[0] != status or actual_size != size:
                        raise RuntimeError(f'party {party} unexpected reply at opcode {opcode}')
                    if len(buf) >= 5 + size:
                        if len(buf) != 5 + size:
                            raise RuntimeError('extra RPC bytes')
                        completed.add(party)
                        selector.unregister(key.fileobj)
        if any(buf != buffers[0] for buf in buffers):
            raise RuntimeError('public outputs differ across workers')
    return bytes(buffers[0][5:]), time.monotonic() - started


def check_stages(processes, public_key, timeout, report):
    from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from scripts.check_lean_crypto import label, handshake, mac
    # Disposable synthetic server. Its key is deliberately public test data.
    server = X25519PrivateKey.from_private_bytes(bytes(range(32)))
    hello_hash = hashlib.sha256(b'native fixture hello transcript').digest()
    expected = handshake(server.exchange(X25519PublicKey.from_public_bytes(public_key)), hello_hash)
    client_secret, server_secret = expected[32:64], expected[64:96]
    _, report['derive_seconds'] = exchange(processes, 1, 2,
        server.public_key().public_bytes_raw() + hello_hash, 0, timeout)
    print('native ECDH/TLS derivation returned', flush=True)
    # 36 bytes of public handshake payload -> existing pinned 58-byte shape.
    content = bytes(range(36))
    header = bytes.fromhex('1703030035')
    record = header + AESGCM(label(server_secret, 'key', b'', 16)).encrypt(
        label(server_secret, 'iv', b'', 12), content + b'\x16', header)
    opened, report['open_seconds'] = exchange(processes, 2, 3, bytes(8) + record, 41, timeout)
    if opened != b'\xff\x16\x00\x24' + content + b'\x00':
        raise RuntimeError('handshake record differs from independent AES-GCM fixture')
    report['ecdh_kdf_aes_record_match'] = True
    # Stub public metadata/decision, not actual certificate validation.
    auth = b'\x00\x01x\x00\x01\x00\x00\x01c\x08\x07' + bytes(32) + b'\x00\x01s\x01'
    exchange(processes, 3, 4, auth, 0, timeout)
    finished_hash = hashlib.sha256(b'native fixture before server Finished').digest()
    finished = b'\x14\x00\x00\x20' + mac(label(server_secret, 'finished', b'', 32), finished_hash)
    accepted, report['verify_seconds'] = exchange(processes, 4, 5, finished_hash + finished, 1, timeout)
    if accepted != b'\xff':
        raise RuntimeError('server Finished rejected')
    server_hash = hashlib.sha256(b'native fixture through server Finished').digest()
    wire, report['finish_seconds'] = exchange(processes, 5, 6, server_hash + server_hash, 58, timeout)
    client_finished = b'\x14\x00\x00\x20' + mac(label(client_secret, 'finished', b'', 32), server_hash)
    expected_wire = header + AESGCM(label(client_secret, 'key', b'', 16)).encrypt(
        label(client_secret, 'iv', b'', 12), client_finished + b'\x16', header)
    if wire != expected_wire:
        raise RuntimeError('client Finished ciphertext differs from independent fixture')
    report['finished_ciphertext_match'] = True
    # Native retirement must still fail until complete VM erasure is implemented.
    exchange(processes, 6, 7, b'', 0, timeout, status=1)
    report['unimplemented_retirement_rejected'] = True


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--timeout', type=float, default=300)
    ap.add_argument('--port', type=int, default=19300)
    ap.add_argument('--stages', action='store_true')
    args = ap.parse_args()
    backend = ROOT / '.deps/sharing-refresh/MP-SPDZ'
    executable = backend.parent / 'tls-worker'
    output = ROOT / 'benchmarks/results/raw/native-worker-network' / secrets.token_hex(8)
    output.mkdir(parents=True)
    hosts = output / 'hosts'
    hosts.write_text('127.0.0.1\n' * 5)
    manifest = output / 'programs.manifest'
    functions = ['tls_begin-s:[256]-sbv:[256x1]']
    if args.stages:
        functions += [p.name for p in (backend / 'Programs/Functions').iterdir()
                      if p.is_file() and p.name.startswith(('tls_binary_', 'tls_agreement-'))]
    manifest.write_text(build(backend, functions))
    session_id = secrets.token_hex(32)
    processes, logs = [], []
    report = dict(checked_utc=datetime.now(timezone.utc).isoformat(), parties=5,
                  threshold=2, binary_field_degree=128, runtime_security_parameter=128,
                  native_mpc_executed=False, full_handshake_tested=False,
                  synthetic_peer_stages_requested=args.stages, certificate_validation_tested=False,
                  expected_exit_code=1 if args.stages else 0,
                  full_vm_erasure_implemented=False, wan_throughput_tested=False,
                  executable_sha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
                  manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest(),
                  logs=str(output.relative_to(ROOT)))
    started = time.monotonic()
    try:
        for party in range(5):
            log = open(output / f'party-{party}.log', 'wb')
            logs.append(log)
            p = subprocess.Popen([str(executable), str(party), str(hosts),
                                  str(args.port), str(manifest), session_id],
                                 cwd=backend, stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=log)
            processes.append(p)
        begun, duration = exchange(processes, 0, 1, b'', 64, args.timeout)
        public_key = begun[:32]
        if not any(public_key) or public_key[31] & 128:
            raise RuntimeError('invalid X25519 public output')
        report.update(native_mpc_executed=True, joint_public_key_agreement=True,
                      begin_seconds=duration)
        if args.stages:
            check_stages(processes, public_key, args.timeout, report)
        for p in processes:
            p.stdin.close()
        for p in processes:
            if p.wait(timeout=30) != (1 if args.stages else 0):
                raise RuntimeError('unexpected worker exit after fixture completion')
        report['passed'] = True
    except Exception as error:
        report.update(passed=False, error=str(error))
    finally:
        for p in processes:
            if p.poll() is None:
                p.kill()
        for p in processes:
            p.wait()
        for log in logs:
            log.close()
        report['exit_codes'] = [p.returncode for p in processes]
        report['elapsed_seconds'] = time.monotonic() - started
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        (ROOT / 'benchmarks/results/tls-native-worker-network.json').write_text(
            json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=2), flush=True)
    if not report['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
