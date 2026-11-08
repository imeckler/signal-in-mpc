#!/usr/bin/env python3
"""Rebuild actual uint32 merge and all replayed accepted varint proofs."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];KEY=HERE.parent/'KeyReferenceWork'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    inventory=json.loads((HERE/'Artifacts/uint32/inventory.json').read_text())
    for name,expected in inventory['source_sha256'].items():assert digest(ROOT/name)==expected,name
    subprocess.run([sys.executable,str(HERE/'replay.py')],check=True)
    run=subprocess.run([sys.executable,str(HERE/'check.py')],capture_output=True,text=True,check=True)
    log=HERE/'uint32-audit.log';log.write_text(run.stdout+run.stderr)
    modules=[*sorted((HERE/'Modules/FieldReferenceWork/Replayed').glob('*.lean')),HERE/'Modules/FieldReferenceWork/Uint32Reference.lean']
    expected=sum(p.read_text().count('#print axioms ')for p in modules)
    entries=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log.read_text(),re.S)
    empty=re.findall(r"'([^']+)' does not depend on any axioms",log.read_text())
    assert len(entries)+len(empty)==expected,(len(entries),len(empty),expected)
    for name,axioms in entries:assert set(a.strip()for a in axioms.split(','))<={'propext','Classical.choice','Quot.sound'},(name,axioms)
    sources=[*modules,*sorted((HERE/'Generated/uint32_step').glob('*.lean')),HERE/'Modules/ProtoParseWork/FieldReferenceWork/Generated/uint32_step/FunsExternal.lean',HERE/'check.py',HERE/'replay.py',Path(__file__),HERE/'extract.py',HERE/'select_uint32_metadata.py',HERE/'replay-report.json',HERE/'Artifacts/uint32/inventory.json',HERE/'Artifacts/uint32/prost.llbc',HERE/'Artifacts/uint32-step/selected.llbc',HERE/'Artifacts/uint32-step/changes.json',HERE/'Artifacts/uint32-step/review.json',KEY/'root-review.json',KEY/'proof-report.json']
    inherited=json.loads((KEY/'proof-report.json').read_text())
    for name,expected_hash in inherited['source_sha256'].items():assert digest(ROOT/name)==expected_hash,name
    report={'candidate_only':True,'accepted_reference':False,'checked_endpoints':expected,'new_uint32_endpoints':8,'allowed_foundational_axioms':['propext','Classical.choice','Quot.sound'],'source_sha256':{str(p.relative_to(ROOT)):digest(p)for p in sources},'rebuilt_olean_sha256':{str(p.relative_to(ROOT)):digest(p)for p in sorted((HERE/'Build').rglob('*.olean'))},'audit_log_sha256':digest(log),'new_external_models':[],'scope':'Actual unchanged Prost uint32::merge for every contiguous byte slice: wire-type-first rejection without consuming input, uint64 decoding with exact suffix/error behavior, modulo2^32 truncation, old-value retention on error, last successful duplicate overwrites. Accepted full-varint models/proofs replayed under namespace/import substitutions after exact common-body comparison.','translation_boundary':'Pinned release Aeneas, no translator patch; seven explicitly recorded unused Step metadata removals with exact fingerprint, reversible delta and identical retained computational bodies.','not_established':['Whole generated SignalMessage merge/parser','Bytes merge model/reference (extracted separately, not included)','Whole numeric parser/artifact agreement']}
    (HERE/'uint32-proof-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Passed',expected,'endpoints, including8new uint32 endpoints.')
if __name__=='__main__':main()
