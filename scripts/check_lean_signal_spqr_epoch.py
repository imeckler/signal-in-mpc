#!/usr/bin/env python3
"""Independent HKDF/direction/state-selection checks for SPQR epoch records."""
from datetime import datetime, timezone
import argparse
import hashlib
import hmac
import json
from pathlib import Path
import random
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes, compile_and_check


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def hkdf(root, secret, label):
    prk = hmac.digest(root, secret, 'sha256')
    last, output = b'', b''
    for counter in range(1, 4):
        last = hmac.digest(prk, last + label + bytes([counter]), 'sha256')
        output += last
    return output


def record(direction, root, secret, epoch, adding):
    label = b'Signal PQ Ratchet V1 Chain Add Epoch' if adding else b'Signal PQ Ratchet V1 Chain  Start'
    material = hkdf(root, secret, label)
    ab, ba = material[32:64], material[64:96]
    send, recv = (ab, ba) if direction == 0 else (ba, ab)
    return b'\xff' + material[:32] + epoch.to_bytes(8, 'big') + send + bytes(4) + recv + bytes(4)


def reference(mode, raw):
    direction = raw[0]
    if mode == 'new':
        return record(direction, bytes(32), raw[1:], 0, False) if direction in (0, 1) else bytes(113)
    root, epoch, proposed, secret = raw[1:33], int.from_bytes(raw[33:41], 'big'), int.from_bytes(raw[41:49], 'big'), raw[49:]
    if direction not in (0, 1) or epoch == 2**64-1 or proposed != epoch + 1:
        return b'\0' + root + epoch.to_bytes(8, 'big') + bytes(72)
    return record(direction, root, secret, proposed, True)


def cases(mode):
    rng = random.Random(0x45504f4348)
    values = []
    root, secret = rng.randbytes(32), rng.randbytes(32)
    def add(label, direction, epoch=0, proposed=1, r=root, k=secret):
        raw = bytes([direction]) + (k if mode == 'new' else r + epoch.to_bytes(8, 'big') + proposed.to_bytes(8, 'big') + k)
        values.append((label, raw, reference(mode, raw)))
    for direction in (0, 1):
        add(f'accepted-direction-{direction}', direction)
    for direction in range(2, 256):
        add(f'invalid-direction-{direction}', direction)
    for i in range(16):
        add(f'random-{i}', i % 2, r=rng.randbytes(32), k=rng.randbytes(32))
    for b in (0, 1, 255):
        add(f'uniform-{b}', b % 2, r=bytes([b])*32, k=bytes([b])*32)
    if mode == 'add':
        for epoch in (0, 1, 127, 128, 255, 256, 65535, 2**32-1, 2**32, 2**63-1, 2**63, 2**64-2, 2**64-1):
            for delta in (0, 1, 2):
                for direction in (0, 1):
                    add(f'epoch-{epoch}-delta-{delta}-direction-{direction}', direction, epoch, (epoch + delta) % 2**64)
    return values


def sources():
    found = set()
    def visit(module):
        if not module.startswith('TlsMpc'):
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        if path in found:
            return
        found.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(imported)
    visit('TlsMpc.Signal.SpqrEpoch')
    found |= {Path(__file__), ROOT/'lean-toolchain', ROOT/'SignalReference/SpqrEpochExport.lean',
              ROOT/'SignalReference/SpqrEpochChecks.lean', ROOT/'scripts/check_lean_crypto.py',
              ROOT/'scripts/clear_circuit.py', ROOT/'test_support/circuit.py', ROOT/'backend_adapter/aig.py',
              ROOT/'backend_adapter/boolean.py', ROOT/'programs/lean_artifact.mpc',
              ROOT/'.deps/libsignal-vendor/spqr/src/chain.rs', ROOT/'.deps/libsignal-vendor/spqr/src/kdf.rs'}
    return found


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--compile-backend', action='store_true')
    args = cli.parse_args()
    files = sources()
    if args.compile_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        files |= {backend/'compile.py', *sorted((backend/'Compiler').rglob('*.py'))}
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sorted(files)}
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.SpqrEpoch'], cwd=ROOT, check=True)
    checks = ROOT/'SignalReference/SpqrEpochChecks.lean'
    checked = subprocess.run(['lake', 'env', 'lean', str(checks)], cwd=ROOT, text=True, capture_output=True, check=True)
    endpoints = re.findall(r'^#print axioms (\S+)', checks.read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", checked.stdout)
    assert [name for name, _ in found] == endpoints
    allowed = {'propext','Classical.choice','Quot.sound'}
    for name, axioms in found:
        assert not ({a.strip() for a in axioms.split(',') if a.strip()} - allowed), name
    directory = ROOT/'.deps/signal-spqr-epoch-artifacts'
    directory.mkdir(exist_ok=True)
    command = ['lake','env','lean','--run','SignalReference/SpqrEpochExport.lean']
    results, artifacts = [], {}
    for mode in ('new','add'):
        path = directory/f'signal-spqr-epoch-{mode}.json'
        with path.open('w') as output:
            subprocess.run([*command, 'signal-spqr-epoch-'+mode], cwd=ROOT, stdout=output, check=True, timeout=600)
        artifact = load(path)
        artifacts[mode] = artifact
        fixtures = cases(mode)
        labels, raw, expected = map(list,zip(*fixtures))
        observed = evaluate_lanes(artifact,raw)
        assert observed == expected, (mode,[l for l,g,w in zip(labels,observed,expected) if g != w])
        # Both peers derive the same root and complementary send/receive keys.
        assert observed[0][1:41] == observed[1][1:41]
        assert observed[0][41:73] == observed[1][77:109] and observed[1][41:73] == observed[0][77:109]
        fixture_file = path.with_name(path.stem+'-fixtures.json')
        fixture_file.write_text(json.dumps([{'label':l,'input':i.hex(),'output':o.hex()} for l,i,o in fixtures],indent=2)+'\n')
        row = {'operation':mode,'artifact_sha256':digest(path),'fixture_sha256':digest(fixture_file),
               'fixture_lanes':len(raw),'input_bits':artifact['input_bits'],'output_bits':len(artifact['outputs']),
               'adapter_operations':statistics(artifact),'all_outputs_match':True}
        if args.compile_backend:
            row['mpc_compilations'] = [compile_and_check(path,raw,expected,batch) for batch in (1,16)]
        results.append(row)
        print(json.dumps(row),flush=True)
    # Feed actual numeric artifact records forward through four additions.
    key = hashlib.sha256(b'public chained SPQR epoch fixture').digest()
    state = evaluate_lanes(artifacts['new'],[bytes([d])+key for d in (0,1)])
    for epoch in range(1,5):
        secret = hashlib.sha256(b'public epoch '+bytes([epoch])).digest()
        raw = [bytes([d])+state[d][1:41]+epoch.to_bytes(8,'big')+secret for d in (0,1)]
        state = evaluate_lanes(artifacts['add'],raw)
        assert state == [reference('add',x) for x in raw]
        assert state[0][1:41] == state[1][1:41]
        assert state[0][41:73] == state[1][77:109] and state[1][41:73] == state[0][77:109]
    assert snapshot == {str(p.relative_to(ROOT)):digest(p) for p in sorted(files)},'Sources changed during epoch check'
    report = {'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(found),
              'source_sha256':snapshot,'cases':results,'artifact_to_artifact_consecutive_additions_per_direction':4,
              'all_inputs_and_outputs_secret':True,'backend_bytecode_compiled':args.compile_backend,
              'native_mpc_executed':False,'throughput_measured':False,'full_actual_rust_refinement':False,
              'full_link_table_or_kem_state_transition':False,'atomic_persistence':False,
              'scope':'32-byte initial/epoch secrets; derive candidate epoch root/send/receive keys and zero counters; consecutive nonoverflowing secret uint64 check.'}
    (ROOT/'benchmarks/results/lean-signal-spqr-epoch-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    axioms = ROOT/'SignalReference/spqr-epoch-axioms.txt'; axioms.write_text(checked.stdout)
    proof = {'checked_at_utc':report['checked_at_utc'],'checked_endpoints':len(found),'theorems':endpoints,
             'allowed_foundational_axioms':sorted(allowed),'custom_axioms':[],
             'source_sha256':snapshot,'axiom_report_sha256':digest(axioms),
             'actual_rust_hkdf_wrapper_refinement':False,'native_mpc_executed':False}
    (ROOT/'SignalReference/spqr-epoch-proof-check.json').write_text(json.dumps(proof,indent=2)+'\n')
    print(f'Passed {sum(r["fixture_lanes"] for r in results)} epoch fixtures,8 composed additions,and {len(found)} theorem endpoints.')


if __name__=='__main__':
    main()
