#!/usr/bin/env python3
"""Validate and freeze this candidate; independent acceptance is deliberately separate."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];KEY=HERE.parent/'KeyReferenceWork'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    proof=json.loads((HERE/'kernel-check-report.json').read_text())
    assert proof['full_rebuild_in_this_invocation'] and proof['new_audit_endpoints']==27
    for name,expected in proof['source_sha256'].items():assert digest(ROOT/name)==expected,name
    assert digest(HERE/'axioms-current.txt')==proof['axiom_audit_sha256']
    build=json.loads((HERE/'candidate-build-report.json').read_text())
    source=HERE/'Source/aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3'
    for name,expected in build['original_source_sha256'].items():
        if name=='src/PrePasses.ml':expected=build['changed_source_sha256']
        assert digest(source/name)==expected,name
    assert digest(HERE/'continuation-pass.diff')==build['diff_sha256']
    assert digest(HERE/'Bin/candidate')==build['binary_sha256']
    comparison=json.loads((HERE/'candidate-comparison.json').read_text())
    inputs={'key':KEY/'Artifacts/key-step/selected.llbc','skip':KEY/'Artifacts/skip-step/selected.llbc','regressions':HERE/'Regressions/regressions.llbc','negative':HERE/'Regressions/negative.llbc'}
    for kind,item in comparison['profiles'].items():
        assert digest(inputs[kind])==item['input_sha256'],kind
        for name,expected in item['generated_files'].items():assert digest(HERE/'Trees/candidate'/name)==expected,name
    accepted=json.loads((KEY/'proof-report.json').read_text())
    for section in ('source_sha256','rebuilt_olean_sha256','model_shadow_olean_sha256'):
        for name,expected in accepted[section].items():assert digest(ROOT/name)==expected,name
    paths=[HERE/x for x in ['README.txt','assessment.json','continuation-pass.diff','candidate-build-report.json','candidate-comparison.json','replay-report.json','kernel-check-report.json','axioms-current.txt','result-map.rs','result-map-provenance.json','build.py','compare.py','extract_regressions.py','freeze.py']]
    paths += [KEY/x for x in ['root-review.json','proof-report.json','Artifacts/skip-step/review.json','Artifacts/skip-step/changes.json','select_step_metadata.py']]
    paths += list(inputs.values())
    report={'candidate_only':True,'accepted_reference':False,'source_and_receipt_sha256':{str(p.relative_to(ROOT)):digest(p)for p in paths},'candidate_proof_sources_verified':len(proof['source_sha256']),'accepted_dependency_sources_verified':len(accepted['source_sha256']),'rebuilt_olean_sha256':{str(p.relative_to(ROOT)):digest(p)for p in sorted((HERE/'Build').rglob('*.olean'))},'scope':proof['scope'],'trust_boundary':proof['trust_boundary']}
    (HERE/'freeze-manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Frozen candidate:',report['candidate_proof_sources_verified'],'proof sources,',len(report['rebuilt_olean_sha256']),'objects; accepted dependencies verified.')
if __name__=='__main__':main()
