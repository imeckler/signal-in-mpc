#!/usr/bin/env python3
"""Audit SPQR symmetric chain derivation and state selection; reference gaps stay explicit."""
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
    visit('TlsMpc.Signal.SpqrChain')
    return result


def main():
    snapshot = sources()
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.SpqrChain'], cwd=ROOT, check=True)
    checks = HERE / 'SpqrChainChecks.lean'
    result = subprocess.run(['lake', 'env', 'lean', str(checks)], cwd=ROOT,
                            capture_output=True, text=True, check=True)
    expected = re.findall(r'^#print axioms (\S+)', checks.read_text(), re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert [name for name, _ in reports] == expected
    for name, assumptions in reports:
        assert not ({value.strip() for value in assumptions.split(',') if value.strip()} - allowed), name
    assert snapshot == sources(), 'Send proof sources changed during audit'
    axiom_path = HERE / 'spqr-chain-axioms.txt'
    axiom_path.write_text(result.stdout)
    references = ['.deps/libsignal-vendor/spqr/src/chain.rs',
                  '.deps/libsignal-vendor/spqr/src/kdf.rs',
                  '.deps/libsignal-v0.106.1/Cargo.lock']
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
              'source_sha256': snapshot, 'checked_endpoints': len(reports), 'theorems': expected,
              'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
              'axiom_report_sha256': digest(axiom_path), 'checks_source_sha256': digest(checks),
              'harness_source_sha256': digest(Path(__file__)),
              'compiled_operations': ['TlsMpc.Signal.SpqrChain.compiled_stepCore_correct',
                                      'TlsMpc.Signal.SpqrChain.compiled_stepCore_spec'],
              'direct_acceptance_specification': ['TlsMpc.Signal.SpqrChain.stepCore_concrete_correct',
                                                 'TlsMpc.Signal.SpqrChain.exhausted_preserves_state'],
              'shared_output': 'acceptance byte || candidate next SPQR chain key32 || candidate next counterBE4 || SPQR message key32; rejection preserves old state and zeros message key',
              'source_reference_commit': '06959b4708f9b7b1e94d0f8cc835f3958c077e94',
              'human_reference_sources_sha256': {name: digest(ROOT / name) for name in references},
              'actual_spqr_hkdf_wrapper_equivalence': False,
              'counter_policy': 'Increment before HKDF info; reject max uint32 and preserve old state. This is a bounded-profile policy outside the Rust precondition.',
              'atomic_state_commit': False,
              'public_boundary': 'Fixed32byte chain key and4byte BE counter; all values, status, message key and next state remain shared.',
              'pending': ['Actual HKDF/SPQR implementation-reference composition',
                          'Epoch selection and ratchet/KEM/chunk transitions',
                          'SPQR message serialization and full Signal send composition',
                          'Atomic persistence and proactive refresh'],
              'native_mpc_executed': False}
    (HERE / 'spqr-chain-proof-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(reports)} Signal SPQR-chain endpoints; standard foundational axioms only.')


if __name__ == '__main__':
    main()
