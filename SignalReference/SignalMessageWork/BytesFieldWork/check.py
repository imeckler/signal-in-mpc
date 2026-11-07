#!/usr/bin/env python3
"""Audit conditional actual generic protobuf byte-field composition; unresolved adapters stay explicit."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[1]
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    base_report_path = REFERENCE / 'ProstEncodingWork/check-report.json'
    base_report = json.loads(base_report_path.read_text())
    for name, sha in base_report['source_sha256'].items():
        assert digest(ROOT / name) == sha, f'Frozen varint reference changed: {name}'
    selected_report_path = HERE / 'Selected/review.json'
    selected_report = json.loads(selected_report_path.read_text())
    assert selected_report['aeneas_exit_code'] == 0 and not selected_report['remaining_external_templates']
    selected_dir = selected_report_path.parent
    assert digest(selected_dir / 'selected.llbc') == selected_report['selected_sha256']
    assert digest(selected_dir / 'changes.json') == selected_report['changes_sha256']
    assert digest(HERE / 'select_bytes.py') == selected_report['script_sha256']
    assert digest(HERE / 'Artifacts/bytes_field.llbc') == selected_report['original_sha256']
    extraction = json.loads((HERE / 'Artifacts/inventory.json').read_text())
    assert extraction['charon_exit_code'] == 0 and not extraction['has_errors']
    assert digest(HERE / 'extract.py') == extraction['script_sha256']
    for name, sha in extraction['source_sha256'].items():
        assert digest(ROOT / name) == sha, f'Original extracted source changed: {name}'
    for name, sha in selected_report['generated_files'].items():
        assert digest(REFERENCE / name) == sha
    sources = [base_report_path, selected_report_path, selected_dir / 'selected.llbc',
               selected_dir / 'changes.json', HERE / 'Artifacts/bytes_field.llbc',
               HERE / 'Artifacts/inventory.json', HERE / 'select_bytes.py', HERE / 'extract.py',
               HERE / 'Reference.lean', HERE / 'Checks.lean', Path(__file__),
               *sorted((HERE / 'GeneratedSelected').glob('*.lean')),
               ROOT / '.deps/libsignal-vendor/prost-0.14.4/src/encoding/wire_type.rs']
    sources += [ROOT / name for name in extraction['source_sha256']]
    sources += [ROOT / '.deps/run-signal-lean.py']
    root_sources = set()
    def visit(module):
        if not module.startswith('TlsMpc'):
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        if path in root_sources:
            return
        root_sources.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(imported)
    visit('TlsMpc.Signal.Serialization')
    sources += sorted(root_sources)
    sources += sorted((ROOT / '.deps/aeneas-2026-08-27/backends/lean/Aeneas/Std').rglob('*.lean'))
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    modules = ['SignalMessageWork/BytesFieldWork/GeneratedSelected/Types',
               'SignalMessageWork/BytesFieldWork/GeneratedSelected/Funs', 'SignalMessageWork/BytesFieldWork/Reference']
    subprocess.run(['python3', '.deps/run-signal-lean.py', *modules], cwd=ROOT, check=True)
    cache = Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
    paths = [REFERENCE / '.lake/build/lib/lean', ROOT / '.lake/build/lib/lean',
             ROOT / '.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']
    paths += [p / '.lake/build/lib/lean' for p in cache.iterdir() if (p / '.lake/build/lib/lean').is_dir()]
    env = os.environ.copy(); env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths)
    result = subprocess.run(['lean', 'SignalMessageWork/BytesFieldWork/Checks.lean'], cwd=REFERENCE, env=env,
                            capture_output=True, text=True, check=True)
    checks = (HERE / 'Checks.lean').read_text()
    expected = re.findall(r'^#print axioms (\S+)', checks, re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert [name for name, _ in reports] == expected
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, assumptions in reports:
        assert not ({a.strip() for a in assumptions.split(',') if a.strip()} - allowed), name
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sources}
    axioms = HERE / 'axioms.txt'
    axioms.write_text(result.stdout)
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'checked_endpoints': len(reports), 'theorems': expected,
              'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
              'source_sha256': snapshot, 'base_reference_report_sha256': digest(base_report_path),
              'axiom_report_sha256': digest(axioms),
              'accepted_reference': False, 'independent_selection_review': 'pending',
              'reference_scope': 'Actual generic Prost bytes::encode for Signal field tags1,4,5,6; exact generic dictionary decomposition retains every supplied failure/divergence.',
              'unconditional_operation_theorem': 'LibSignalReference.Candidate.SignalBytesField.field_eq',
              'conditional_circuit_theorem': 'LibSignalReference.Candidate.SignalBytesField.field_refines_artifact_of_payload_contract',
              'undischarged_hypotheses': ['Actual concrete adapter.len equals Vec.len', 'Actual concrete adapter.append_to appends its payload within the capacity bound'],
              'domain': 'Arbitrary secret payload contents; fixed public length; buffer.length+payload.length+11<=Usize.max; one of four Signal byte-field tags.',
              'concrete_vector_append_refined': False,
              'standard_model_boundary': 'Unchanged pinned Aeneas scalar/Vec/RangeInclusive.new models. No custom model is registered.',
              'selection_correctness_mechanized': False,
              'full_signalmessage_encoder_refined': False, 'native_mpc_executed': False}
    (HERE / 'proof-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(reports)} byte-field endpoints; conditional payload contract remains explicit; selection review pending.')



if __name__ == '__main__':
    main()
