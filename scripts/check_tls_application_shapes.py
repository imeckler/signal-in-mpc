#!/usr/bin/env python3
"""Public TLS shape integration: actual Lean emitter, compiler and native spawn.

All data is synthetic. Numeric circuit checks use independent AES-GCM/framing
oracles. This does not execute MPC or enable the retirement-gated application.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.prepare_tls_shape import Shape, digest, sources, validate_manifest
from scripts.pin_tls_worker import build
from scripts.check_lean_tls_receive import open_record, parse_inner, protect, sample
from scripts.check_tls_post_handshake import numeric, Framer, parsed
from backend_adapter.aig import statistics

BACKEND = ROOT/'.deps/sharing-refresh/MP-SPDZ'
CACHE = ROOT/'.deps/sharing-refresh/tls-application-shapes-v2'
PROBE = BACKEND.parent/'tls-shape-probe'
REPORT = ROOT/'benchmarks/results/tls-application-shape-checks.json'


def run(command, **kwargs):
    result = subprocess.run(list(map(str, command)), capture_output=True,
                            text=True, timeout=1900, **kwargs)
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}): {command}\n{result.stdout}\n{result.stderr}')
    return result


def fixtures(shape):
    prefix = sample('application-shape-key-iv', 28)+(2**64-1).to_bytes(8, 'big')
    if shape.mode == 'tls-seal-record':
        kind, size, padding = map(int, shape.arguments[1:])
        content = sample('application-shape-plaintext', size)
        return [prefix+content], [protect(prefix, content+bytes([kind])+bytes(padding))[36:]]
    if shape.mode == 'tls-open-record':
        capacity = shape.output_bytes-4
        raw = protect(prefix, sample('application-shape-plaintext', capacity-4)+b'\x17\x00\x00\x00')
        inputs = [raw]
        for offset in (0, 36, len(raw)-1):
            altered = bytearray(raw); altered[offset] ^= 1; inputs.append(bytes(altered))
        return inputs, [open_record(value) for value in inputs]
    if shape.mode == 'tls-route-application':
        capacity = shape.output_bytes-15
        inputs, expected = [], []
        for kind, data, auth in [(23, b'', 255), (23, sample('full-record', capacity-1), 255),
                                  (21, b'\x01\x00', 255), (23, b'bad', 0),
                                  (22, b'\x18\x00\x00\x01\x01', 255)]:
            state = bytes(11)
            inputs.append(state+parsed(capacity, kind, data, auth))
            if kind == 22:
                expected.append(b'\x05'+bytes(shape.output_bytes-1))
            else:
                framer = Framer(); event = bytes(framer.record(kind, data, auth))
                payload = len(data).to_bytes(2, 'big')+data+bytes(capacity-len(data)) if event[0] == 1 else bytes(capacity+2)
                expected.append(event+framer.state()+payload)
        return inputs, expected
    if shape.mode == 'tls-post-handshake':
        capacity = shape.output_bytes-15
        inputs, expected = [], []
        framer = Framer()
        for kind, data in [(22, b'\x04\x00\x00\x03a'), (22, b'bc'),
                           (22, b'\x18\x00\x00\x01\x01'), (23, b'secret')]:
            data = data[:capacity]
            inputs.append(framer.state()+parsed(capacity, kind, data))
            event = bytes(framer.record(kind, data))
            payload = len(data).to_bytes(2, 'big')+data+bytes(capacity-len(data)) if event[0] == 1 else bytes(capacity+2)
            expected.append(event+framer.state()+payload)
        return inputs, expected
    # Legacy handshake shape: accepted metadata is public in this fixture.
    capacity = shape.output_bytes-4
    inner = bytes(range(capacity-1))+b'\x16'
    return [protect(prefix, inner)], [parse_inner(inner)]


def main():
    names = ['Main.lean', 'scripts/prepare_tls_shape.py', 'scripts/check_tls_application_shapes.py',
             'handshake_backend/KernelShape.h', 'handshake_backend/ShapeCompiler.h',
             'handshake_backend/PinnedPrograms.h', 'handshake_backend/NativeCollective.h',
             'handshake_backend/NativeSession.h', 'handshake_backend/worker_main.cpp',
             'handshake_backend/shape_compiler_probe.cpp', 'handshake_backend/kernel_shape_checks.cpp',
             'programs/tls_export.mpc', 'backend_adapter/aig_packed.py',
             'handshake_backend/binary_io.py']
    snapshot = {name: digest(ROOT/name) for name in names}
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'complete': False,
              'native_mpc_executed': False, 'collective_network_agreement_executed': False,
              'application_execution_enabled': False, 'full_vm_erasure_implemented': False,
              'source_sha256': snapshot, 'cases': []}
    REPORT.write_text(json.dumps(report, indent=2)+'\n')
    CACHE.mkdir(exist_ok=True)
    if not (CACHE/'Compiler').exists():
        (CACHE/'Compiler').symlink_to(BACKEND/'Compiler', target_is_directory=True)
    shutil.copy2(BACKEND/'compile.py', CACHE/'compile.py')
    for folder in ('Source', 'Functions', 'Schedules', 'Bytecode'):
        (CACHE/'Programs'/folder).mkdir(parents=True, exist_ok=True)
    python = json.loads((BACKEND/'Worker-Public/tls-shape-toolchain.json').read_text())['python']['path']
    if not (CACHE/'Worker-Public/tls-shape-toolchain.json').exists():
        run([python, ROOT/'scripts/prepare_tls_shape.py', '--install', CACHE,
             '--emitter', ROOT/'.lake/build/bin/emit_mpc'])
    config = json.loads((CACHE/'Worker-Public/tls-shape-toolchain.json').read_text())
    assert config['files'] == sources(CACHE)
    assert digest(CACHE/'Worker-Public/tls-shape-compiler') == digest(ROOT/'scripts/prepare_tls_shape.py')
    assert digest(CACHE/'Worker-Public/tls-shape-emitter') == digest(ROOT/'.lake/build/bin/emit_mpc')
    boot = CACHE/'boot.manifest'
    boot.write_text(build(CACHE, [], ['Worker-Public/tls-shape-compiler', 'Worker-Public/tls-shape-toolchain.json']))
    checker = CACHE/'kernel-shape-checks'
    run(['c++', '-std=c++20', '-O2', '-fsanitize=address,undefined',
         ROOT/'handshake_backend/kernel_shape_checks.cpp', '-o', checker])
    checks = run([checker])
    for line in checks.stdout.splitlines():
        arguments, key, descriptor, size = line.split('|')
        shape = Shape(arguments.split())
        assert (shape.key, 'Programs/Functions/'+shape.descriptor, shape.output_bytes) == (key, descriptor, int(size))
    report['cpp_python_shape_checks'] = checks.stderr.strip()
    rejected = [['tls-open-record', '16407'], ['tls-route-application', '16386'],
                ['tls-post-handshake', '0'], ['tls-seal-record', '23', '16384', '1'],
                ['tls-seal-record', '22', '0', '0'], ['tls-seal-record', '20', '1', '0'],
                ['tls-open-record', '-1'], ['tls-open-record', '38junk'],
                ['tls-open-record', '٣٨'], ['../program', '38']]
    for arguments in rejected:
        try:
            Shape(arguments)
        except ValueError:
            pass
        else:
            raise AssertionError(('invalid shape accepted', arguments))
    report['invalid_python_shapes'] = rejected
    for arguments in [('38',), ('tls-seal-record', '23', '1025', '3'),
                      ('tls-open-record', '1050'), ('tls-route-application', '1029'),
                      ('tls-route-application', '6'),
                      ('tls-post-handshake', '5'), ('tls-seal-record', '22', '5', '0'),
                      ('tls-seal-record', '21', '2', '0'), ('tls-seal-record', '23', '0', '0'),
                      ('tls-route-application', '16385')]:
        shape = Shape(arguments)
        manifest = CACHE/'Worker-Public'/f'tls-shape-{shape.key}.manifest'
        cache_preexisting = manifest.exists()
        started = time.monotonic()
        # The REAL native spawn creates the artifact/bytecode cache and registers
        # it only after its agreement callback. The callback is local, not MPC.
        try:
            accepted = run([PROBE, boot, *arguments, 'accept'], cwd=CACHE)
        except Exception as error:
            report['failed_shape'] = shape.arguments
            report['failure'] = str(error)
            REPORT.write_text(json.dumps(report, indent=2)+'\n')
            raise
        assert accepted.stdout.strip() == '1 agreements'
        elapsed = time.monotonic()-started
        validate_manifest(CACHE, manifest.read_text())
        receipt = manifest.with_name(f'tls-shape-{shape.key}.receipt.json')
        before = receipt.read_bytes()
        rejected_run = subprocess.run([str(PROBE), str(boot), *arguments, 'reject'], cwd=CACHE,
                                      capture_output=True, text=True, timeout=60)
        assert rejected_run.returncode == 1 and 'simulated party disagreement' in rejected_run.stderr
        assert receipt.read_bytes() == before
        artifact = CACHE/'Worker-Public'/f'{shape.stem}.json'
        with artifact.open('wb') as output:
            subprocess.run([str(CACHE/'Worker-Public/tls-shape-emitter'), *shape.arguments],
                           stdout=output, check=True, timeout=900)
        image = json.loads(artifact.read_bytes())
        inputs, expected = fixtures(shape)
        assert numeric(image, inputs) == expected, shape.key
        row = {'shape': shape.arguments, 'compiler_spawn_seconds': elapsed,
               'cache_preexisting': cache_preexisting,
               'numeric_fixture_lanes': len(inputs), 'all_outputs_match': True,
               'registration_after_agreement_checked': True, 'disagreement_rejected': True,
               'cache_receipt_unchanged': True, 'artifact_sha256': digest(artifact),
               'manifest_sha256': digest(manifest), 'statistics': statistics(image)}
        report['cases'].append(row)
        REPORT.write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps({k:v for k,v in row.items() if k != 'statistics'}), flush=True)
    for arguments in [('tls-route-application', '16386'), ('tls-post-handshake', '16386'),
                      ('tls-open-record', '16407'), ('tls-open-application-record', '16407'),
                      ('tls-parse-inner', '16386'), ('tls-open-inner', '16386'),
                      ('tls-seal-record', '23', '16385', '0')]:
        bad = subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'), *arguments],
                             capture_output=True, timeout=10)
        assert bad.returncode != 0 and not bad.stdout, arguments
    assert snapshot == {name: digest(ROOT/name) for name in names}
    report.update(complete=True, invalid_lean_shapes_rejected=7,
                  emitter_sha256=digest(ROOT/'.lake/build/bin/emit_mpc'),
                  native_probe_sha256=digest(PROBE),
                  toolchain_sha256=digest(CACHE/'Worker-Public/tls-shape-toolchain.json'),
                  max_aes_record_executed=False)
    REPORT.write_text(json.dumps(report, indent=2)+'\n')
    print('TLS application shape checks passed', flush=True)


if __name__ == '__main__':
    main()
