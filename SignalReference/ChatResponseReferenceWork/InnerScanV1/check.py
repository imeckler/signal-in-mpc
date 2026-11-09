#!/usr/bin/env python3
"""Focused actual-driver replay check, not a total schema/streaming theorem."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[CHAT/'InnerResponseV1/audit.json']
receipts += [ROOT/n for n in json.loads(receipts[0].read_text())['inherited_receipts_sha256']]
objects={};sources={}
for receipt in receipts:
 data=json.loads(receipt.read_text())
 for name,digest in data['source_sha256'].items():
  assert sha(ROOT/name)==digest,name;sources[name]=digest
 for name,digest in data.get('objects_sha256',data.get('object_sha256',{})).items():
  p=Path(name);assert sha(p)==digest,name
  module=name.rsplit('ChatResponseReferenceWork/',1)[1]
  if module in objects:assert objects[module][1]==digest,module
  objects[module]=(p,digest)
out=H/'Build/final'
for module,(p,digest) in objects.items():
 target=out/'ChatResponseReferenceWork'/module
 if target.exists():assert sha(target)==digest,target
 else:target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
subprocess.run(['python3',str(H/'replay.py')],check=True,timeout=30)
modules=['Replayed.Types','Replayed.FunsExternal','Replayed.Funs','DriverReference']
files=[H/Path(*m.split('.')).with_suffix('.lean') for m in modules]+[H/n for n in ['check.py','replay.py','replay.json','README.md']]
before={str(p.relative_to(ROOT)):sha(p) for p in files}
env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with (H/'audit.log').open('w') as f:
 subprocess.run(['python3',str(CHAT/'check.py'),*['InnerScanV1.'+m for m in modules]],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=180)
log=(H/'audit.log').read_text();assert 'sorryAx' not in log
for name in ['trace_actual_loop','key_total','actual_fields','owned_decode']:assert name+"' depends on axioms:" in log
for name,digest in {**sources,**before}.items():assert sha(ROOT/name)==digest,name
for p,digest in objects.values():assert sha(p)==digest,p
(H/'audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Actual owned inner response merge driver with generated field dispatcher; strict key consumption, finite ordinary-success/error traces, exact owned-error projection. Trace existence/totality, outer schema and streaming composition remain open.','source_sha256':before,'inherited_receipts_sha256':{str(p.relative_to(ROOT)):sha(p) for p in receipts},'inherited_source_count':len(sources),'inherited_object_count':len(objects),'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/InnerScanV1'/Path(*m.split('.')).with_suffix('.olean')):sha(out/'ChatResponseReferenceWork/InnerScanV1'/Path(*m.split('.')).with_suffix('.olean')) for m in modules}},indent=2)+'\n')
print('Four-module owned inner driver PASS; total scan and outer/streaming composition OPEN')
