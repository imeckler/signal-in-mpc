#!/usr/bin/env python3
"""Audit actual protobuf counter fields through the numeric circuit compiler."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    base_report_path = REFERENCE / 'ProstEncodingWork/check-report.json'
    base_report = json.loads(base_report_path.read_text())
    for name, sha in base_report['source_sha256'].items():
        assert digest(ROOT / name) == sha, f'Frozen varint reference changed: {name}'
    independent = REFERENCE / 'ProstEncodingWork/UInt32SelectionReview/review.json'
    review = json.loads(independent.read_text())
    assert review['independent_review'] and review['checks_passed']
    for name, sha in review['sha256'].items():
        assert digest(ROOT / name) == sha, f'Independent selection review changed: {name}'
    selected_report_path = HERE / 'Artifacts/UInt32Selected/review.json'
    selected_report = json.loads(selected_report_path.read_text())
    assert selected_report['aeneas_exit_code'] == 0 and not selected_report['remaining_external_templates']
    selected_dir = selected_report_path.parent
    assert digest(selected_dir / 'selected.llbc') == selected_report['selected_sha256']
    assert digest(selected_dir / 'changes.json') == selected_report['changes_sha256']
    assert digest(HERE / 'select_uint32.py') == selected_report['script_sha256']
    for name, sha in selected_report['generated_files'].items():
        assert digest(REFERENCE / name) == sha
    assert review['selected_llbc_sha256'] == selected_report['selected_sha256']
    sources = [base_report_path, independent, REFERENCE / 'ProstEncodingWork/UInt32SelectionReview/check.py', selected_report_path, selected_dir / 'selected.llbc',
               selected_dir / 'changes.json', HERE / 'Artifacts/UInt32Field/signal_message.llbc',
               HERE / 'Artifacts/UInt32Field/inventory.json', HERE / 'select_uint32.py', HERE / 'extract.py',
               HERE / 'UInt32Reference.lean', HERE / 'UInt32Checks.lean', Path(__file__),
               *sorted((HERE / 'Generated/UInt32Selected').glob('*.lean')),
               ROOT / '.deps/libsignal-vendor/prost-0.14.4/src/encoding/wire_type.rs']
    sources += sorted((ROOT / '.deps/aeneas-2026-08-27/backends/lean/Aeneas/Std').rglob('*.lean'))
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    modules = ['SignalMessageWork/Generated/UInt32Selected/Types',
               'SignalMessageWork/Generated/UInt32Selected/Funs', 'SignalMessageWork/UInt32Reference']
    subprocess.run(['python3', '.deps/run-signal-lean.py', *modules], cwd=ROOT, check=True)
    cache = Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
    paths = [REFERENCE / '.lake/build/lib/lean', ROOT / '.lake/build/lib/lean',
             ROOT / '.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']
    paths += [p / '.lake/build/lib/lean' for p in cache.iterdir() if (p / '.lake/build/lib/lean').is_dir()]
    env = os.environ.copy(); env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths)
    result = subprocess.run(['lean', 'SignalMessageWork/UInt32Checks.lean'], cwd=REFERENCE, env=env,
                            capture_output=True, text=True, check=True)
    checks = (HERE / 'UInt32Checks.lean').read_text()
    expected = re.findall(r'^#print axioms (\S+)', checks, re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert [name for name, _ in reports] == expected
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, assumptions in reports:
        assert not ({a.strip() for a in assumptions.split(',') if a.strip()} - allowed), name
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sources}
    axioms = HERE / 'uint32-axioms.txt'
    axioms.write_text(result.stdout)
    accepted = True
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'checked_endpoints': len(reports), 'theorems': expected,
              'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
              'source_sha256': snapshot, 'base_reference_report_sha256': digest(base_report_path),
              'axiom_report_sha256': digest(axioms),
              'independent_selection_review': str(independent.relative_to(ROOT)) if accepted else 'pending',
              'independent_review_sha256': digest(independent) if accepted else None,
              'accepted_reference': accepted,
              'reference_scope': 'Actual Prost uint32::encode for SignalMessage tags2 and3, including actual encode_key, debug tag-range check, wire discriminant and generic varint; concrete selected Vec buffer methods.',
              'main_theorem': 'LibSignalReference.Candidate.SignalField.field_refines_artifact',
              'domain': 'All uint32 values with canonical public widths1..5; buffer.length+11≤Usize.max; arbitrary prior buffer contents.',
              'standard_model_boundary': 'Official pinned Aeneas scalar/Vec/RangeInclusive.new models. Selecting the actual constructor body together with its existing model caused a pure/Result signature mismatch; this reviewed profile uses the unchanged official model.',
              'selection_correctness_mechanized': False,
              'full_signalmessage_encoder_refined': False,
              'native_mpc_executed': False}
    (HERE / 'uint32-proof-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(reports)} actual uint32 field endpoints; standard axioms only. Selection review: {"present" if accepted else "pending"}.')


if __name__ == '__main__':
    main()
