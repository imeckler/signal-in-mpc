#!/usr/bin/env python3
"""Kernel axiom audit for the bounded active-SPQR established send circuit."""
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
    visit('TlsMpc.Signal.SpqrSend')
    return result


def main():
    snapshot = sources()
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.SpqrSend'], cwd=ROOT, check=True)
    checks = HERE / 'SpqrSendChecks.lean'
    result = subprocess.run(['lake', 'env', 'lean', str(checks)], cwd=ROOT,
                            capture_output=True, text=True, check=True)
    expected = re.findall(r'^#print axioms (\S+)', checks.read_text(), re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert [name for name, _ in reports] == expected
    for name, assumptions in reports:
        assert not ({value.strip() for value in assumptions.split(',') if value.strip()} - allowed), name
    assert snapshot == sources(), 'Proof sources changed during audit'
    axiom_path = HERE / 'spqr-send-axioms.txt'
    axiom_path.write_text(result.stdout)
    references = ['.deps/libsignal-vendor/spqr/src/chain.rs',
                  '.deps/libsignal-vendor/spqr/src/v1/chunked/states/serialize.rs',
                  '.deps/libsignal-vendor/spqr/src/lib.rs',
                  '.deps/libsignal-v0.106.1/rust/protocol/src/ratchet/keys.rs',
                  '.deps/libsignal-v0.106.1/rust/protocol/src/triple_ratchet.rs',
                  '.deps/libsignal-v0.106.1/rust/protocol/src/protocol.rs',
                  '.deps/libsignal-v0.106.1/Cargo.lock']
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'source_sha256': snapshot, 'checked_endpoints': len(reports), 'theorems': expected,
              'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
              'axiom_report_sha256': digest(axiom_path), 'checks_source_sha256': digest(checks),
              'harness_source_sha256': digest(Path(__file__)),
              'compiled_operations': ['TlsMpc.Signal.SpqrSend.compiled_sealCore_correct',
                                      'TlsMpc.Signal.SpqrSend.compiled_sealCore_spec'],
              'direct_acceptance_specification': ['TlsMpc.Signal.SpqrSend.sealCore_concrete_correct',
                                                 'TlsMpc.Signal.SpqrSend.reject_preserves_both_states'],
              'shared_output': 'status1 || candidate Signal chain32 || Signal counterBE4 || candidate SPQR chain32 || SPQR counterBE4 || Signal wire; reject preserves both old states and zeros wire',
              'human_reference_sources_sha256': {name: digest(ROOT / name) for name in references},
              'actual_full_spqr_signal_send_equivalence': False,
              'counter_policy': 'SPQR counter increments before both HKDF and serialization; Signal counter increments in candidate state. Reject either maximum counter and zero epoch.',
              'atomic_state_commit': False,
              'public_boundary': 'Plaintext size, both Signal varint widths, SPQR epoch/index/chunk widths, chunk/address presence. All other inputs, outputs and acceptance remain shared.',
              'required_call_precondition': 'Caller has selected the active SPQR chain for message epoch minus one and the outgoing payload from the SPQR state machine.',
              'pending': ['Full translated RustCrypto/prost/Signal/SPQR composition',
                          'Active epoch selection, KEM/chunk state transitions, optional inactive SPQR branch',
                          'Atomic persistence, rollback protection and proactive refresh'],
              'native_mpc_executed': False}
    (HERE / 'spqr-send-proof-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(reports)} SPQR send endpoints; standard foundational axioms only.')


if __name__ == '__main__':
    main()
