#!/usr/bin/env python3
"""Five Lean controllers/native MPC parties against a real OpenSSL test server.

Only public disposable fixtures are used; no TLS client secret is reconstructed.
The isolated lifecycle worker must complete handshake retirement. Repeated
application records and KeyUpdate are a subsequent check.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import secrets
import signal
import socket
import subprocess
import threading
import time

from check_full_handshake import certificates, OPENSSL
from pin_tls_worker import build

ROOT = Path(__file__).resolve().parents[1]


def serve(listener, server, result):
    """Bridge public TLS ciphertext to the existing OpenSSL memory-BIO server."""
    try:
        with listener:
            connection, _ = listener.accept()
        with connection:
            connection.settimeout(2400)

            def exact(size):
                out = bytearray()
                while len(out) < size:
                    chunk = connection.recv(size-len(out))
                    if not chunk:
                        raise EOFError('client closed before server accepted Finished')
                    out.extend(chunk)
                return bytes(out)

            while True:
                header = exact(5)
                size = int.from_bytes(header[3:5], 'big')
                if size > 16640:
                    raise ValueError('oversize fixture record')
                record = header + exact(size)
                server.stdin.write(record.hex() + '\n')
                server.stdin.flush()
                line = server.stdout.readline().strip()
                status, text = line.split(' ', 1)
                if status not in ('ready', 'waiting'):
                    raise ValueError('invalid OpenSSL fixture response')
                wire = bytes.fromhex(text) if text != '-' else b''
                offset = 0
                while offset < len(wire):
                    if len(wire)-offset < 5:
                        raise ValueError('truncated OpenSSL record header')
                    length = 5 + int.from_bytes(wire[offset+3:offset+5], 'big')
                    if offset+length > len(wire):
                        raise ValueError('truncated OpenSSL record')
                    result['outgoing_records'].append({'type': wire[offset], 'wire_bytes': length})
                    offset += length
                if status == 'ready':
                    # SSL_is_init_finished proves the server checked Finished.
                    # No application exchange is attempted past client retirement.
                    result['client_finished_accepted'] = True
                    break
                connection.sendall(wire)
    except Exception as error:
        result['error'] = str(error)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--timeout', type=int, default=2400)
    ap.add_argument('--port', type=int, default=19300)
    args = ap.parse_args()
    backend = ROOT / '.deps/tls-session-runtime/MP-SPDZ'
    output = ROOT / 'benchmarks/results/raw/native-session-lifecycle' / secrets.token_hex(8)
    output.mkdir(parents=True)
    # Use the existing compiled Lean dependencies; this independent fixture
    # does not modify the global lake targets or Main files.

    for name in ('public_auth', 'fixture_server'):
        subprocess.run(['c++', '-std=c++20', '-O2', '-I'+str(OPENSSL/'include'),
                        str(ROOT/f'handshake_backend/{name}.cpp'), '-L'+str(OPENSSL/'lib'),
                        '-lssl', '-lcrypto', '-o', str(output/name)], check=True)
    profiles, trust = certificates(output)
    cert, key = profiles['ed25519']
    hosts = output/'hosts'
    hosts.write_text('127.0.0.1\n'*5)
    manifest = output/'programs.manifest'
    functions = [p.name for p in (backend/'Programs/Functions').iterdir()
                 if p.is_file() and p.name.startswith(('tls_binary_', 'tls_begin-', 'tls_agreement-'))]
    manifest.write_text(build(backend, functions, ['Worker-Public/tls-shape-compiler',
                                                  'Worker-Public/tls-shape-toolchain.json']))
    session = secrets.token_hex(32)
    listener = socket.socket()
    listener.bind(('127.0.0.1', 0))
    listener.listen(1)
    listener.settimeout(args.timeout)
    server_port = listener.getsockname()[1]
    server_log = open(output/'server.log', 'w')
    server = subprocess.Popen([str(output/'fixture_server'), str(cert), str(key), '512', 'no', 'h2'],
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=server_log, text=True)
    server_result = {'client_finished_accepted': False, 'outgoing_records': []}
    bridge = threading.Thread(target=serve, args=(listener, server, server_result), daemon=True)
    bridge.start()
    processes, logs = [], []
    started = time.monotonic()
    report = dict(checked_utc=datetime.now(timezone.utc).isoformat(), passed=False,
                  parties=5, threshold=2, native_mpc_attempted=True, native_mpc_executed=False,
                  full_application_session_accepted=False, full_vm_erasure_implemented=False,
                  lifecycle_handshake_retirement_tested=True,persistent_application_records_tested=False,
                  wan_throughput_tested=False, logs=str(output.relative_to(ROOT)),
                  manifest_sha256=hashlib.sha256(manifest.read_bytes()).hexdigest())
    names = ['handshake_backend/SessionWork/NativeHandshakeFixture.lean', 'TlsMpc/TlsWorkerProcess.lean', 'TlsMpc/TlsWorkerPipe.lean',
             'TlsMpc/TlsWorker.lean', 'TlsMpc/TlsClient.lean', 'TlsMpc/TlsWire.lean',
             'handshake_backend/public_auth.cpp', 'handshake_backend/fixture_server.cpp',
             'scripts/check_native_session_lifecycle.py', '.deps/tls-session-runtime/tls-worker',
             'handshake_backend/SessionWork/worker_main.cpp']
    names += [str(p.relative_to(ROOT)) for p in (ROOT/'handshake_backend').glob('*.h')]
    names += [str(p.relative_to(ROOT)) for p in (ROOT/'handshake_backend/SessionWork').glob('*.h')]
    names += ['.deps/tls-session-runtime/MP-SPDZ/libSPDZ.so','handshake_backend/LifecycleWork/SecureGmp.h','handshake_backend/SessionWork/session-epoch.patch','handshake_backend/SessionWork/patch-provenance.json']
    report['source_and_executable_sha256'] = {
        name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in names}
    try:
        for party in range(5):
            log = open(output/f'party-{party}.log', 'w')
            logs.append(log)
            command = ['lake','env','lean','--run',str(ROOT/'handshake_backend/SessionWork/NativeHandshakeFixture.lean'), str(backend.parent/'tls-worker'),
                       str(backend), str(party), str(hosts), str(args.port), str(manifest), session,
                       '127.0.0.1', str(server_port), 'server.example', str(output/'public_auth'), str(trust)]
            processes.append(subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE, stderr=log,
                                              text=True, start_new_session=True))
        cases = []
        for party, p in enumerate(processes):
            stdout, _ = p.communicate(timeout=max(1, args.timeout-(time.monotonic()-started)))
            (output/f'party-{party}.json').write_text(stdout)
            if p.returncode:
                raise RuntimeError(f'controller {party} failed; inspect its public fixture log')
            case = json.loads(stdout)
            if not case['passed']:
                raise RuntimeError('controller failed to reach required boundary')
            cases.append(case)
        bridge.join(timeout=10)
        if bridge.is_alive() or not server_result['client_finished_accepted'] or 'error' in server_result:
            raise RuntimeError('OpenSSL server did not accept client Finished')
        report.update(passed=True, native_mpc_executed=True, controllers=cases,
                      application_gate_activated=True)
    except Exception as error:
        report['error'] = str(error)
    finally:
        for p in processes:
            try:
                os.killpg(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        for p in processes:
            p.wait()
        # Kill the isolated controller/worker groups on timeout as well as on
        # normal completion; process teardown is not an erasure receipt.
        listener.close()
        if server.poll() is None:
            server.kill()
        server.wait()
        for log in logs:
            log.close()
        server_log.close()
        report.update(server=server_result, elapsed_seconds=time.monotonic()-started,
                      controller_exit_codes=[p.returncode for p in processes])
        (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
        (ROOT/'benchmarks/results/tls-native-session-lifecycle.json').write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(report, indent=2), flush=True)
    if not report['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
