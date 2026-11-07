#!/usr/bin/env python3
"""Build the Lean target and audit every theorem listed in Checks.lean."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}


def main():
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    source = ROOT / 'Checks.lean'
    expected = re.findall(r'^#print axioms (\S+)$', source.read_text(), re.M)
    if not expected or len(expected) != len(set(expected)):
        raise RuntimeError('empty or duplicate theorem audit')
    result = subprocess.run(['lake', 'env', 'lean', source.name], cwd=ROOT,
                            capture_output=True, text=True, check=True)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",
                       result.stdout)
    observed = {name: sorted(x.strip() for x in assumptions.split(',') if x.strip())
                for name, assumptions in found}
    if set(observed) != set(expected) or len(found) != len(expected):
        raise RuntimeError('incomplete theorem audit:\n' + result.stdout)
    used = {x for assumptions in observed.values() for x in assumptions}
    if used - ALLOWED:
        raise RuntimeError('unexpected proof axioms: ' + repr(sorted(used - ALLOWED)))
    paths = [source, ROOT / 'TlsMpc.lean', Path(__file__).resolve(),
             *sorted((ROOT / 'TlsMpc').rglob('*.lean'))]
    report = {'kind': 'lean_theorem_axiom_audit', 'checked_utc': datetime.now(timezone.utc).isoformat(),
              'theorems': observed,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in paths},
              'scope': 'Functional specifications, refinement and compiler proofs. No MPC security or native execution claim.'}
    destination = ROOT / 'benchmarks/results/lean-proof-checks.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'audited': len(observed), 'axioms': sorted(used),
                      'report': str(destination.relative_to(ROOT))}))


if __name__ == '__main__':
    main()
