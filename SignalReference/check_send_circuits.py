#!/usr/bin/env python3
"""Audit Signal send composition and lowering; reference gaps stay explicit."""
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
    visit('TlsMpc.Signal.Send')
    return result


def main():
    snapshot = sources()
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.Send'], cwd=ROOT, check=True)
    checks = HERE / 'SendCircuitChecks.lean'
    result = subprocess.run(['lake', 'env', 'lean', str(checks)], cwd=ROOT,
                            capture_output=True, text=True, check=True)
    expected = re.findall(r'^#print axioms (\S+)', checks.read_text(), re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert [name for name, _ in reports] == expected
    for name, assumptions in reports:
        assert not ({value.strip() for value in assumptions.split(',') if value.strip()} - allowed), name
    assert snapshot == sources(), 'Send proof sources changed during audit'
    axiom_path = HERE / 'send-circuit-axioms.txt'
    axiom_path.write_text(result.stdout)
    references = ['.deps/libsignal-v0.106.1/rust/crypto/src/aes_cbc.rs',
                  '.deps/libsignal-v0.106.1/rust/protocol/src/protocol.rs',
                  '.deps/libsignal-v0.106.1/rust/protocol/src/proto/wire.proto',
                  '.deps/libsignal-vendor/prost-0.14.4/src/encoding.rs',
                  '.deps/libsignal-vendor/prost-0.14.4/src/encoding/varint.rs',
                  '.deps/libsignal-vendor/prost-derive-0.14.4/src/lib.rs']
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'source_sha256': snapshot, 'checked_endpoints': len(reports), 'theorems': expected,
              'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
              'axiom_report_sha256': digest(axiom_path), 'checks_source_sha256': digest(checks),
              'harness_source_sha256': digest(Path(__file__)),
              'compiled_operations': ['TlsMpc.Signal.Serialization.compiled_encodeCore_correct',
                                      'TlsMpc.Signal.Send.compiled_sealCore_correct'],
              'direct_acceptance_specification': ['TlsMpc.Signal.Serialization.encodeCore_concrete_correct',
                                                 'TlsMpc.Signal.Send.sealCore_concrete_correct'],
              'shared_output': 'acceptance byte || serialized content, or complete serialized Signal wire including MAC; all bytes zero on rejection',
              'source_reference_commit': '904c8dc8216073b078a5f2f5090e3da8382e6a92',
              'human_reference_sources_sha256': {name: digest(ROOT / name) for name in references},
              'actual_signalmessage_constructor_equivalence': False,
              'actual_rustcrypto_aes_cbc_hmac_wrapper_equivalence': False,
              'public_boundary': 'Plaintext/ciphertext and PQ lengths, address presence, and canonical counter varint widths1..5; counters are four big-endian secret input bytes.',
              'version_policy': 'Constructor exactly masks input low nibble, shifts left4 and ORs current version4; parser acceptance is a separate operation.',
              'pending': ['Full actual SignalMessage/prost constructor composition', 'Full actual RustCrypto wrapper equivalence',
                          'Session/ratchet state transitions and persistence', 'Secret-state proactive refresh composition'],
              'native_mpc_executed': False}
    (HERE / 'send-circuit-proof-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(reports)} Signal send endpoints; standard foundational axioms only.')


if __name__ == '__main__':
    main()
