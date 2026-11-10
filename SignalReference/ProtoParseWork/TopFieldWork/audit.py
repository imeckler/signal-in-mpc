#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];PLAN=HERE.parent/'SkipPlanWork'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 inherited=json.loads((PLAN/'proof-report.json').read_text())
 for name,expected in inherited['source_sha256'].items():assert sha(ROOT/name)==expected,name
 run=subprocess.run([sys.executable,str(HERE/'check.py')],capture_output=True,text=True,check=True)
 log=HERE/'audit.log';log.write_text(run.stdout+run.stderr)
 modules=sorted((HERE/'Modules').rglob('*.lean'))
 expected=sum(p.read_text().count('#print axioms ')for p in modules)
 entries=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log.read_text(),re.S)
 empty=re.findall(r"'([^']+)' does not depend on any axioms",log.read_text())
 assert len(entries)+len(empty)==expected,(len(entries),len(empty),expected)
 for name,axs in entries:assert {a.strip()for a in axs.split(',')}<={'propext','Classical.choice','Quot.sound'},(name,axs)
 sources={**inherited['source_sha256'],**{str(p.relative_to(ROOT)):sha(p)for p in [*modules,HERE/'check.py',HERE/'audit.py',HERE/'README.txt',PLAN/'proof-report.json',PLAN/'root-review.json']}}
 report={'candidate_only':True,'accepted_reference':False,'checked_endpoints':expected,'rebuilt_modules':len(modules),'source_sha256':sources,
 'rebuilt_olean_sha256':{str(p.relative_to(ROOT)):sha(p)for p in sorted((HERE/'Build').rglob('*.olean'))},'audit_log_sha256':sha(log),'allowed_foundational_axioms':['propext','Classical.choice','Quot.sound'],'new_external_models':[],
 'scope':'Top-level field masks/overwrite; bounded shared decoder table and payload-window correspondence to actual accepted varint/key calls; inactive and rejected scan-state preservation.',
 'not_established':['Whole parser/group trace','Complete cursor/group stack preservation','Numeric metadata composition with actual scalar/bytes field mergers','Whole successful SignalMessage/AIG parser agreement']}
 (HERE/'proof-report.json').write_text(json.dumps(report,indent=2)+'\n');print('Passed',expected,'endpoints in',len(modules),'modules.')
if __name__=='__main__':main()
