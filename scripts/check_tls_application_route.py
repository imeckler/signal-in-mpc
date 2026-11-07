#!/usr/bin/env python3
"""Check the two-stage private record dispatcher using actual numeric artifacts.

Public fixtures only. DEFER never commits its placeholder state: the original
shared input is fed to the complete control parser. No native MPC execution.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

from check_tls_post_handshake import ROOT, Framer, numeric, parsed, sequences
from backend_adapter.aig import statistics


def main():
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    capacity = 64
    images = {}
    hashes = {}
    for mode in ('tls-route-application', 'tls-post-handshake'):
        run = subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'), mode, str(capacity)],
                             cwd=ROOT, capture_output=True, check=True, timeout=180)
        images[mode] = json.loads(run.stdout)
        hashes[mode] = hashlib.sha256(run.stdout).hexdigest()
    inputs = []
    for sequence in sequences():
        reference = Framer()
        for kind, data, auth in sequence:
            inputs.append(reference.state()+parsed(capacity, kind, data, auth))
            reference.record(kind, data, auth)
    # Private malformed lengths must not bypass the full parser or its rejection.
    for length in (0, capacity+1, 16385, 65535):
        for kind in (21, 22, 23):
            inputs.append(bytes(11)+bytes([255, kind])+length.to_bytes(2, 'big')+bytes(capacity))
    fast = numeric(images['tls-route-application'], inputs)
    full = numeric(images['tls-post-handshake'], inputs)
    deferred = 0
    for index, (source, routed, complete) in enumerate(zip(inputs, fast, full)):
        expected_defer = source[11] == 255 and source[10] == 0 and source[12] == 22
        assert (routed[0] == 5) == expected_defer, (index, 'defer predicate')
        if expected_defer:
            deferred += 1
            assert routed == bytes([5])+bytes(len(routed)-1), (index, 'defer release')
        elif source[12] != 22:
            assert routed == complete, (index, 'non-handshake equivalence')
        else:
            assert routed[:2] == complete[:2] == bytes(2), (index, 'rejection')
            assert routed[12] == complete[12] == 255, (index, 'sticky failure')
            assert routed[13:] == complete[13:] == bytes(capacity+2), (index, 'release')
    # Exercise adaptive execution with actual artifact-produced state, including
    # a ticket fragmented across records, a requested KeyUpdate, data and close.
    state, reference = bytes(11), Framer()
    stream = [(22,b'\x04\x00\x00\x09abc'), (22,b'defghi'),
              (22,b'\x18\x00'), (22,b'\x00\x01\x01'),
              (23,b'private recipient'), (21,b'\x01\x00')]
    for kind, data in stream:
        original = state+parsed(capacity, kind, data)
        result = numeric(images['tls-route-application'], [original])[0]
        if result[0] == 5:
            result = numeric(images['tls-post-handshake'], [original])[0]
        assert tuple(result[:2]) == reference.record(kind, data)
        state = result[2:13]
        assert state == reference.state()
    paths = [ROOT/'TlsMpc/TlsApplicationRoute.lean', ROOT/'TlsMpc/TlsPostHandshake.lean',
             ROOT/'Main.lean', Path(__file__).resolve(),
             ROOT/'scripts/check_tls_post_handshake.py']
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'numeric_lanes': len(inputs), 'deferred_lanes': deferred,
              'chained_records': len(stream), 'native_mpc_executed': False,
              'artifact_sha256': hashes,
              'statistics': {name: statistics(image) for name, image in images.items()},
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in paths}}
    (ROOT/'benchmarks/results/tls-application-route-checks.json').write_text(
        json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
