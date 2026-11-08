#!/usr/bin/env python3
"""Five-party synthetic router/memory-I/O fixture, not a TLS application session."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import secrets
import subprocess
import time
from pin_tls_worker import build
from prepare_tls_shape import Shape, digest

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend', required=True, type=Path)
    parser.add_argument('--capacity', type=int, default=16385)
    parser.add_argument('--port', type=int, default=19400)
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    backend = args.backend.resolve()
    shape = Shape(['tls-route-application', args.capacity])
    if args.capacity < 6:
        parser.error('fixture requires capacity at least6')
    executable = ROOT/'.deps/sharing-refresh/tls-application-shape-fixture'
    output = ROOT/'benchmarks/results/raw/tls-application-shape-native'/secrets.token_hex(8)
    output.mkdir(parents=True)
    hosts = output/'hosts';hosts.write_text('127.0.0.1\n'*5)
    manifest = output/'programs.manifest'
    manifest.write_text(build(backend, [], ['Worker-Public/tls-shape-compiler', 'Worker-Public/tls-shape-toolchain.json']))
    session_id = secrets.token_hex(32)
    names = ['handshake_backend/application_shape_fixture.cpp', 'handshake_backend/NativeWorker.h',
             'handshake_backend/OwnedSecrets.h', 'handshake_backend/LongFieldBit.h',
             'handshake_backend/StrongShamirShare.h', 'handshake_backend/NativeCollective.h',
             'handshake_backend/ShapeCompiler.h', 'handshake_backend/KernelShape.h',
             'handshake_backend/binary_io.py', 'scripts/check_tls_application_shape_native.py']
    snapshot = {name: digest(ROOT/name) for name in names}
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'passed': False,
              'parties': 5, 'threshold': 2, 'statistical_security_parameter': 128,
              'binary_field_degree': 128, 'capacity': args.capacity,
              'fixture': 'public synthetic full-length application router input; actual output shares reused as inputs; bad-authentication rejection',
              'source_sha256': snapshot, 'executable_sha256': digest(executable),
              'manifest_sha256': digest(manifest), 'backend': str(backend.relative_to(ROOT)),
              'program_extension_sha256': digest(backend/'Worker-Public'/f'tls-shape-{shape.key}.manifest'),
              'logs': str(output.relative_to(ROOT)), 'native_mpc_executed': False,
              'tls_application_session_executed': False, 'full_vm_erasure_implemented': False,
              'wan_throughput_measured': False}
    processes, logs = [], []
    started = time.monotonic()
    try:
        for party in range(5):
            log = (output/f'party-{party}.log').open('wb');logs.append(log)
            processes.append(subprocess.Popen([str(executable), str(party), str(hosts), str(args.port),
                                               str(manifest), str(args.capacity), session_id], cwd=backend,
                                              stdout=log, stderr=subprocess.STDOUT))
        for process in processes:
            process.wait(timeout=max(1, args.timeout-(time.monotonic()-started)))
        assert [p.returncode for p in processes] == [0]*5
        for log in logs:log.flush()
        for party in range(5):
            assert f'public router fixture passed: capacity={args.capacity}; three calls; no application activation' in (output/f'party-{party}.log').read_text()
        assert snapshot == {name: digest(ROOT/name) for name in names}
        report.update(passed=True, native_mpc_executed=True, checked_calls_per_party=3,
                      protocol_produced_shares_reused=True, collective_program_agreement_executed=True)
    except Exception as error:
        report['error'] = str(error)
    finally:
        for process in processes:
            if process.poll() is None:process.kill()
        for process in processes:process.wait()
        for log in logs:log.close()
        report['exit_codes'] = [p.returncode for p in processes]
        report['elapsed_seconds'] = time.monotonic()-started
        report['log_sha256'] = {str(p.relative_to(ROOT)): digest(p) for p in sorted(output.glob('party-*.log'))}
        text = json.dumps(report, indent=2)+'\n'
        (output/'report.json').write_text(text)
        (ROOT/'benchmarks/results/tls-application-shape-native.json').write_text(text)
        print(text, flush=True)
    if not report['passed']:raise SystemExit(1)


if __name__ == '__main__':
    main()
