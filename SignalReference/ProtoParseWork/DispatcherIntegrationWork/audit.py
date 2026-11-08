#!/usr/bin/env python3
"""Check generated reproducibility hashes and all new kernel endpoint axioms."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
translation=json.loads((H/'translation.json').read_text())
assert translation['exit_code']==0 and translation['manual_generated_edits'] is False
for name,digest in translation['generated_sha256'].items():assert sha(H/'Generated'/name)==digest,name
r=subprocess.run([sys.executable,str(H/'check.py')],capture_output=True,text=True)
log=r.stdout+r.stderr;(H/'audit.log').write_text(log);r.check_returncode()
entries=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log,re.S)
new=[entry for entry in entries if entry[0].startswith('DispatcherIntegration.')]
assert len(new)==30,len(new)
for name,axs in entries:
 assert {a.strip() for a in axs.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'},(name,axs)
files=[p for p in H.rglob('*') if p.suffix in ['.lean','.py','.json','.sh'] and 'Build' not in p.parts and p.name!='proof-report.json']
(H/'proof-report.json').write_text(json.dumps({'candidate_only':True,'accepted_reference':False,'kernel_exit_code':r.returncode,'audited_endpoints':len(new),'total_log_endpoints':len(entries),'allowed_axioms':['propext','Classical.choice','Quot.sound'],'generated_manual_corrections':False,'log_sha256':sha(H/'audit.log'),'source_sha256':{str(p.relative_to(H)):sha(p) for p in sorted(files)}},indent=2)+'\n')
print(f'{len(new)} new kernel endpoints passed; foundational axioms only')
