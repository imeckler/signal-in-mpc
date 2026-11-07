#!/usr/bin/env python3
"""Check Lean-generated cryptography against hashlib/HMAC and RFC vectors.

All fixtures are public synthetic test data. No Python crypto circuit builder
is imported. Native MPC execution, WAN timing, and live TLS are not tested.
"""

import argparse
import hashlib
import hmac
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import execute, load
from backend_adapter.aig import statistics
from scripts.clear_circuit import execute as execute_mpc_source
from test_support.circuit import input_tokens


def mac(key, message):
    return hmac.digest(key, message, 'sha256')


def expand(prk, info, size):
    previous, output = b'', b''
    for counter in range(1, (size + 31) // 32 + 1):
        previous = mac(prk, previous + info + bytes([counter]))
        output += previous
    return output[:size]


def label(secret, name, context, size):
    name = b'tls13 ' + name.encode('ascii')
    info = size.to_bytes(2, 'big') + bytes([len(name)]) + name + bytes([len(context)]) + context
    return expand(secret, info, size)


def handshake(ecdhe, hello_hash):
    empty_hash = hashlib.sha256(b'').digest()
    early = mac(bytes(32), bytes(32))
    hs = mac(label(early, 'derived', empty_hash, 32), ecdhe)
    return (hs + label(hs, 'c hs traffic', hello_hash, 32)
            + label(hs, 's hs traffic', hello_hash, 32)
            + mac(label(hs, 'derived', empty_hash, 32), bytes(32)))


def sample(seed, length):
    return hashlib.shake_256(seed.encode()).digest(length)


def cases():
    for size in (0, 3, 55, 56, 63, 64, 119, 120, 137):
        data = [sample(f'hash-{lane}', size) for lane in range(4)]
        if size == 3:
            data[0] = b'abc'
        yield ('sha256', str(size)), data, [hashlib.sha256(x).digest() for x in data]
    for key_size, msg_size in ((0, 0), (32, 1), (64, 55), (65, 56), (97, 133)):
        keys = [sample(f'key-{lane}', key_size) for lane in range(4)]
        msgs = [sample(f'msg-{lane}', msg_size) for lane in range(4)]
        yield ('hmac-sha256', str(key_size), str(msg_size)), [k + m for k, m in zip(keys, msgs)], [
            mac(k, m) for k, m in zip(keys, msgs)]
    for salt, info, expected_hex in (
        (bytes(range(13)), bytes(range(0xf0, 0xfa)),
         '3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865'),
        (b'', b'', '8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8')):
        ikm = b'\x0b' * 22
        prk = mac(salt or bytes(32), ikm)
        okm = expand(prk, info, 42)
        assert okm.hex() == expected_hex
        yield ('hkdf-sha256', str(len(salt)), '22', str(len(info)), '42'), [salt + ikm + info], [prk + okm]
    for name, ctx_size, size in (('exporter', 32, 33), ('key', 0, 0)):
        raw = [sample(f'label-{lane}', 32 + ctx_size) for lane in range(4)]
        yield ('tls-expand-label', name, str(ctx_size), str(size)), raw, [
            label(x[:32], name, x[32:], size) for x in raw]
    dhe = bytes.fromhex('8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d')
    hello = bytes.fromhex('860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8')
    hs = bytes.fromhex('1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac')
    client = bytes.fromhex('b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21')
    server = bytes.fromhex('b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38')
    main = bytes.fromhex('18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919')
    assert handshake(dhe, hello) == hs + client + server + main
    raw = [dhe + hello, sample('handshake', 64)]
    yield ('tls-handshake-secrets',), raw, [handshake(x[:32], x[32:]) for x in raw]
    raw = [server, sample('traffic', 32)]
    expected = [label(x, 'key', b'', 16) + label(x, 'iv', b'', 12) for x in raw]
    assert expected[0].hex() == '3fce516009c21727d0f2e4e86ee403bc5d313eb2671276ee13000b30'
    yield ('tls-traffic-keys',), raw, expected
    transcript = bytes.fromhex('9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13')
    raw = [main + transcript, sample('application', 64)]
    expected = [label(x[:32], 'c ap traffic', x[32:], 32) + label(x[:32], 's ap traffic', x[32:], 32) for x in raw]
    assert expected[0].hex() == ('9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5'
                                  'a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643')
    yield ('tls-application-secrets',), raw, expected
    raw = [client + transcript, sample('finished', 64)]
    expected = [mac(label(x[:32], 'finished', b'', 32), x[32:]) for x in raw]
    assert expected[0].hex() == 'a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61'
    yield ('tls-finished',), raw, expected
    raw = [client, sample('update', 32)]
    yield ('tls-update-traffic',), raw, [label(x, 'traffic upd', b'', 32) for x in raw]


def evaluate_lanes(image, fixtures):
    width = image['input_bits']
    assert all(len(x) * 8 == width for x in fixtures)
    shared = [sum(((x[i // 8] >> (7 - i % 8)) & 1) << lane for lane, x in enumerate(fixtures))
              for i in range(width)]
    bits = execute(image, shared, 0, (1 << len(fixtures)) - 1)
    return [bytes(sum(((bits[i + j] >> lane) & 1) << (7 - j) for j in range(8))
                  for i in range(0, len(bits), 8)) for lane in range(len(fixtures))]


def compile_and_check(path, raw, expected, batch):
    backend = ROOT / '.deps/MP-SPDZ'
    copied = backend / 'Programs/Source/lean-artifacts'
    copied.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, copied / path.name)
    source = ROOT / 'programs/lean_artifact.mpc'
    shutil.copy2(source, backend / 'Programs/Source/lean_artifact.mpc')
    args = [path.stem, str(batch), '5']
    program = 'lean_artifact-' + '-'.join(args)
    environment = os.environ.copy()
    environment['PYTHONPATH'] = str(ROOT) + os.pathsep + environment.get('PYTHONPATH', '')
    compiled = subprocess.run([sys.executable, './compile.py', '-M', '-B', '128', 'lean_artifact', *args],
                              cwd=backend, env=environment, capture_output=True, text=True, timeout=600)
    logs = ROOT / 'benchmarks/results/raw' / program
    logs.mkdir(parents=True, exist_ok=True)
    log = compiled.stdout + compiled.stderr
    (logs / 'compile.log').write_text(log)
    if compiled.returncode:
        raise RuntimeError(log[-4000:])
    inputs = [raw[i % len(raw)] for i in range(batch)]
    outputs = [expected[i % len(expected)] for i in range(batch)]
    values = [int.from_bytes(x[offset:offset + 8], 'big')
              for offset in range(0, len(outputs[0]), 8) for x in outputs]
    previous = Path.cwd()
    try:
        os.chdir(backend)
        observed = execute_mpc_source(source, backend / 'Programs/Circuits', ['lean_artifact', *args],
                                      input_tokens({'raw': inputs}))
    finally:
        os.chdir(previous)
    if observed != values:
        raise AssertionError(f'MPC-source fixture mismatch: {program}')
    triples = re.findall(r'(\d+) bit triples', log)
    return {'batch': batch, 'parties': 5, 'bit_triples': int(triples[-1]) if triples else 0,
            'fixture_output_values_checked': len(values),
            'bytecode_sha256': hashlib.sha256((backend / f'Programs/Bytecode/{program}-0.bc').read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true',
                        help='Check exported circuits only; do not use shared MP-SPDZ compiler paths')
    options = parser.parse_args()
    fixtures = list(cases())
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    records = []
    with tempfile.TemporaryDirectory(prefix='tls-mpc-lean-crypto-') as directory:
        for args, raw, expected in fixtures:
            path = Path(directory) / ('-'.join(args) + '.json')
            with path.open('w') as output:
                subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *args], stdout=output,
                               cwd=ROOT, check=True, timeout=300)
            image = load(path)
            if evaluate_lanes(image, raw) != expected:
                raise AssertionError(f'Lean circuit mismatch: {args}')
            record = {'arguments': args, 'input_bits': image['input_bits'], 'output_bits': len(image['outputs']),
                      'nodes': len(image['nodes']), 'and_gates': sum(x[0] == 2 for x in image['nodes']),
                      'adapter_operations': statistics(image),
                      'fixture_lanes': len(raw), 'all_outputs_match': True,
                      'artifact_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            print(json.dumps(record), flush=True)
            if not options.skip_backend and args in (('sha256', '3'), ('tls-traffic-keys',)):
                record['mpc_compilations'] = [compile_and_check(path, raw, expected, batch) for batch in (1, 16)]
                print(json.dumps({'arguments': args, 'mpc_compilations': record['mpc_compilations']}), flush=True)
            records.append(record)
            path.unlink()
    paths = list((ROOT / 'TlsMpc').glob('*.lean')) + [ROOT / 'Main.lean', ROOT / 'backend_adapter/aig.py',
            ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc', Path(__file__).resolve()]
    report = {'kind': 'lean_crypto_export_checks', 'cases': records,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'references': ['https://www.rfc-editor.org/rfc/rfc5869', 'https://www.rfc-editor.org/rfc/rfc8448',
                             'https://www.rfc-editor.org/rfc/rfc9846'],
              'native_mpc_executed': False, 'throughput_measured': False,
              'backend_compilation_tested': not options.skip_backend,
              'limitations': ['The normative prose-to-Lean correspondence remains a human audit obligation.',
                              'JSON, native exporter execution, adapter, and MPC backend are unverified.',
                              'The unverified adapter recovers XOR operations; addition/depth remain unoptimized and no WAN performance is measured.',
                              'AES-GCM, handshake authentication, and live TLS are not implemented in the proved Lean path.']}
    (ROOT / 'benchmarks/results/lean-crypto-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
