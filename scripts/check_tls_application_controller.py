#!/usr/bin/env python3
"""Public Lean controller checks; no MPC, cryptography, or erasure claim."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    subprocess.run(['lake', 'build', 'TlsMpc.TlsApplication'], cwd=ROOT, check=True)
    run = subprocess.run(['lake', 'env', 'lean', '--run', 'ApplicationFixture.lean'],
                         cwd=ROOT, capture_output=True, text=True, timeout=60, check=True)
    assert run.stdout.startswith('PASS: 305 policy boundary checks;'), run.stdout
    sources = ['TlsMpc/TlsApplication.lean', 'TlsMpc/TlsApplicationPolicy.lean',
               'TlsMpc/TlsClient.lean', 'TlsMpc/TlsWire.lean', 'ApplicationFixture.lean',
               'scripts/check_tls_application_controller.py']
    report = {
        'kind': 'lean_tls_application_controller_public_fixtures',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'policy_boundary_checks': 305,
        'checks': ['old-key update sealed and sent before new-key installation',
                   'crossed requested updates, response flag and receive counter reset',
                   'automatic sending record budget update; unrestricted receive epoch',
                   'half-close and preserved initial sequence counters',
                   'protocol and I/O exceptions during seal/send/control/rotate/open/receive',
                   'terminal failures; explicit cleanup failure reporting',
                   'actual handshake run cleanup for begin and transport I/O exceptions',
                   'blocked receive permits send; 32 concurrent sends use distinct sequences',
                   'malformed framing rejected before private open; authenticated rejection terminal'],
        'source_sha256': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in sources},
        'output': run.stdout.strip(),
        'native_mpc_executed': False,
        'limitations': ['Mock public Nat handles; no TLS cryptography in this fixture.',
                        'Native application backend, private post-handshake parser and erasure are separate unfinished obligations.',
                        'No controller I/O refinement proof or durable recovery claim.']}
    destination = ROOT/'benchmarks/results/tls-application-controller-checks.json'
    destination.write_text(json.dumps(report, indent=2)+'\n')
    print(run.stdout.strip())
    print(destination.relative_to(ROOT))


if __name__ == '__main__':
    main()
