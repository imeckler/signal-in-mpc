#!/usr/bin/env python3
"""Replay the candidate contiguous Prost bytes/actual Vec content reference."""
import hashlib,json,re,subprocess,sys,copy
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];REFERENCE=HERE.parent.parent;FIELD=HERE.parent/'FieldReferenceWork';KEY=HERE.parent/'KeyReferenceWork'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(mapping,base=ROOT):
 for name,expected in mapping.items():assert sha(base/name)==expected,name
def main():
 inherited=json.loads((KEY/'proof-report.json').read_text());verify(inherited['source_sha256'])
 scalar=json.loads((FIELD/'uint32-proof-report.json').read_text());verify(scalar['source_sha256'])
 merge=json.loads((FIELD/'Artifacts/bytes/inventory.json').read_text());verify(merge['source_sha256'])
 adapter=json.loads((HERE/'Artifacts/vec_replace_put_body/inventory.json').read_text());verify(adapter['source_sha256']);verify(adapter['generated_files'],REFERENCE)
 assert adapter['charon_exit_code']==adapter['aeneas_exit_code']==0 and not adapter['llbc_preprocessing']
 step=FIELD/'Artifacts/bytes-step';review=json.loads((step/'review.json').read_text())
 assert sha(FIELD/'Artifacts/bytes/prost.llbc')==review['original_sha256']
 assert sha(step/'selected.llbc')==review['selected_sha256'] and sha(step/'changes.json')==review['changes_sha256']
 verify(review['generated_files'],REFERENCE)
 original=json.loads((FIELD/'Artifacts/bytes/prost.llbc').read_text());selected=json.loads((step/'selected.llbc').read_text())
 changes=json.loads((step/'changes.json').read_text());assert len(changes)==7
 for change in reversed(changes):
  node=selected
  for key in change['path'][:-1]:node=node[key]
  key=change['path'][-1];assert node[key]==change['after'];node[key]=change['before']
 assert selected==original
 oracle=json.loads((HERE/'oracle-report.json').read_text());verify(oracle['source_sha256'])
 assert oracle['all_cases_passed'] and sum(oracle['cases'].values())==5638
 assert sha(HERE/'oracle-output.txt')==oracle['output_sha256']
 subprocess.run([sys.executable,str(HERE/'replay.py')],check=True)
 subprocess.run([sys.executable,str(HERE/'model_provenance.py')],check=True)
 run=subprocess.run([sys.executable,str(HERE/'check.py')],capture_output=True,text=True,check=True)
 log=HERE/'audit.log';log.write_text(run.stdout+run.stderr)
 modules=sorted((HERE/'Modules').rglob('*.lean'))
 expected=sum(p.read_text().count('#print axioms ')for p in modules)
 entries=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log.read_text(),re.S)
 empty=re.findall(r"'([^']+)' does not depend on any axioms",log.read_text())
 assert len(entries)+len(empty)==expected,(len(entries),len(empty),expected)
 for name,axioms in entries:assert {a.strip()for a in axioms.split(',')}<={'propext','Classical.choice','Quot.sound'},(name,axioms)
 own=[*modules,*sorted((HERE/'Generated/vec_replace_put_body').glob('*.lean')),*sorted((FIELD/'Generated/bytes_step').glob('*.lean')),
 *[HERE/n for n in ['check.py','replay.py','replay-report.json','buf-copy-slot.diff','model_provenance.py','model-provenance.json','model-diff.patch','README.txt','audit.py','extract_adapters.py','oracle-report.json','check_oracle.py','oracle-output.txt','Artifacts/vec_replace_put_body/inventory.json','Artifacts/vec_replace_put_body/prost.llbc']],
 *[FIELD/n for n in ['Artifacts/bytes/inventory.json','Artifacts/bytes/prost.llbc','Artifacts/bytes-step/selected.llbc','Artifacts/bytes-step/review.json','Artifacts/bytes-step/changes.json','select_bytes_metadata.py','uint32-root-review.json','uint32-proof-report.json']],KEY/'root-review.json',KEY/'proof-report.json']
 source={**inherited['source_sha256'],**scalar['source_sha256'],**merge['source_sha256'],**adapter['source_sha256'],**oracle['source_sha256']}
 source.update({str(p.relative_to(ROOT)):sha(p)for p in own})
 source.update(json.loads((HERE/'model-provenance.json').read_text())['source_sha256'])
 report={'candidate_only':True,'accepted_reference':False,'checked_endpoints':expected,'new_content_endpoints':26,
 'rebuilt_modules':len(list((HERE/'Build').rglob('*.olean'))),'allowed_foundational_axioms':['propext','Classical.choice','Quot.sound'],
 'source_sha256':source,'rebuilt_olean_sha256':{str(p.relative_to(ROOT)):sha(p)for p in sorted((HERE/'Build').rglob('*.olean'))},'audit_log_sha256':sha(log),
 'native_public_cases':oracle['cases'],'metadata_edits_reversed_to_original':True,
 'scope':'Actual extracted bytes::merge and Vec<u8>::replace_with/put, with new contiguous content models. Exact bounds/errors, suffix, old-value retention, success replacement, total modeled field behavior and last duplicate wins.',
 'trusted_model_boundary':json.loads((HERE/'model-provenance.json').read_text())['new_trusted_assumptions'],
 'not_established':['Arbitrary Buf','Allocation/isize-capacity failure equivalence','Generic destructor behavior','Numeric parser table/scan agreement','Whole SignalMessage parser or artifact agreement','Erasure']}
 (HERE/'proof-report.json').write_text(json.dumps(report,indent=2)+'\n')
 print('Passed',expected,'endpoints;',report['rebuilt_modules'],'modules;',sum(oracle['cases'].values()),'native fixtures.')
if __name__=='__main__':main()
