#!/usr/bin/env python3
"""Audit bounded Signal receive lowering and direct acceptance semantics."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    result = {}

    def visit(module):
        name = module.replace('.', '/') + '.lean'
        if name in result or not module.startswith('TlsMpc'):
            return
        path = ROOT / name
        result[name] = digest(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(imported)

    visit('TlsMpc.Signal.ReceiveSpec')
    return result


def main():
    snapshot = sources()
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.ReceiveSpec'], cwd=ROOT, check=True)
    checks = HERE / 'ReceiveCircuitChecks.lean'
    result = subprocess.run(['lake', 'env', 'lean', str(checks)], cwd=ROOT,
                            capture_output=True, text=True, check=True)
    expected = re.findall(r'^#print axioms (\S+)', checks.read_text(), re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if [name for name, _ in reports] != expected:
        raise ValueError('Missing or unexpected receive theorem report')
    for name, assumptions in reports:
        if {value.strip() for value in assumptions.split(',') if value.strip()} - allowed:
            raise ValueError(f'Unexpected receive theorem assumption: {name}')
    if snapshot != sources():
        raise ValueError('Receive proof sources changed during the audit')
    axiom_path = HERE / 'receive-circuit-axioms.txt'
    axiom_path.write_text(result.stdout)
    upstream = ROOT / '.deps/libsignal-v0.106.1'
    reference = ['rust/crypto/src/aes_cbc.rs', 'rust/protocol/src/protocol.rs',
                 'rust/protocol/src/proto/wire.proto', 'rust/core/src/address.rs', 'rust/core/src/curve.rs']
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'source_sha256': snapshot, 'checked_endpoints': len(reports), 'theorems': expected,
              'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
              'axiom_report_sha256': digest(axiom_path), 'checks_source_sha256': digest(checks),
              'harness_source_sha256': digest(Path(__file__)),
              'direct_specification_theorem': 'TlsMpc.Signal.Receive.compiled_openCore_spec',
              'shared_output': 'acceptance byte || uint64 big-endian retained length || fixed-size zero-padded plaintext buffer; all bytes zero on rejection',
              'source_reference_commit': '904c8dc8216073b078a5f2f5090e3da8382e6a92',
              'human_reference_sources_sha256': {name: digest(upstream / name) for name in reference},
              'actual_rustcrypto_aes_cbc_hmac_wrapper_equivalence': False,
              'actual_strict_pkcs7_final_block_refinement': 'Previously established in canonical LibSignalReference.Proofs.Unpad; receive composition audited separately.',
              'public_boundary': 'Nonzero block-aligned ciphertext and optional36-byte address spans within one shared serialized content; span offsets/presence must be established by an in-MPC protobuf parser.',
              'pending': ['Full actual RustCrypto wrapper equivalence', 'Complete protobuf parsing',
                          'Session/ratchet state transitions and replay handling', 'Secret-state persistence and proactive refresh composition'],
              'native_mpc_executed': False}
    (HERE / 'receive-circuit-proof-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(reports)} Signal receive endpoints; standard foundational axioms only.')


if __name__ == '__main__':
    main()
