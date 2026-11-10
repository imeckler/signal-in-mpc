#!/usr/bin/env python3
"""Freeze this scoped reference checkpoint after successful local verification."""
import hashlib,json
from datetime import datetime,timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    report=json.loads((HERE/'report.json').read_text())
    assert report['standard_axioms_only'] and report['actual_native_constructor_presence_cases']==2048
    assert report['differential_cases_sha256']==sha(HERE/'differential-cases.json')
    assert report['axiom_audit_sha256']==sha(HERE/'axioms.txt')
    inventory=json.loads((HERE/'Artifacts/ContentModels/inventory.json').read_text())
    assert inventory['script_sha256']==sha(HERE/'extract.py')
    files={str(p.relative_to(ROOT)):sha(p) for p in sorted(HERE.rglob('*')) if p.is_file()
        and not any(x in {'Build','.lake','__pycache__'} for x in p.relative_to(HERE).parts)
        and p.name!='completion.json'}
    result={'frozen_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_only':True,
        'accepted_reference':False,'files':files,'proof_endpoints':report['proof_endpoints'],
        'actual_native_constructor_presence_cases':2048,'new_circuit_gate_count':0,
        'full_actual_aeneas_refinement':False,'external_model_boundaries':report['external_model_boundaries']}
    (HERE/'completion.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'Frozen {len(files)} files; completion sha256 '+sha(HERE/'completion.json'))
if __name__=='__main__':main()
