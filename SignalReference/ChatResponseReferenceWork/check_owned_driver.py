#!/usr/bin/env python3
"""Actual default merge extraction + key/owned-wrapper composition checkpoint."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for script,arg in [('extract.py','owned_driver'),('translate.py','owned_driver')]:subprocess.run(['python3',str(H/script),arg],check=True,timeout=240)
output=Path(os.environ.get('CHAT_RESPONSE_OUTPUT_ROOT',str(H/'Revisions/owned-driver-audit'))).resolve();env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
mods=['GeneratedOwnedDriver.TypesExternal','GeneratedOwnedDriver.Types','GeneratedOwnedDriver.FunsExternal','GeneratedOwnedDriver.Funs','OwnedDriverReference']
with (H/'owned-driver-audit.log').open('w') as f:subprocess.run(['python3',str(H/'check.py'),*mods],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=180)
log=(H/'owned-driver-audit.log').read_text();assert 'sorryAx' not in log
for name in ['key_total','decode_actual_merge']:assert "ChatResponseOwnedDriver."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
files=[H/'check_owned_driver.py',H/'extract.py',H/'translate.py',H/'OwnedDriverReference.lean']+sorted((H/'GeneratedOwnedDriver').glob('*.lean'))
report={'candidate_only':True,'scope':'Actual default Prost merge body and actual contiguous key totality; owned control composition. No assumed key correctness. Full chat dispatch/scan termination/refinement remains open.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'object_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in mods},'extraction':json.loads((H/'Artifacts/owned_driver/inventory.json').read_text()),'translation':json.loads((H/'owned_driver-translation.json').read_text()),'lean_log':log,'models':'Same accepted contiguous safe-index decoder and exact error/suffix adapters; successful bounded allocation content. No SignalMessage schema equivalence is reused for Chat schema.'}
(H/'owned-driver-audit.json').write_text(json.dumps(report,indent=2)+'\n');print('actual owned driver/key checkpoint PASS')
