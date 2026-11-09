#!/usr/bin/env python3
"""Focused reproduction of the committed three-module streaming milestone."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=['VarintReference','ScalarProjection','VarintPrefix'];parent=CHAT/'OuterEnvelopeV1/audit.json'
queue=[parent];seen=set();objects={}
while queue:
 p=queue.pop()
 if p in seen:continue
 seen.add(p);data=json.loads(p.read_text())
 for name,digest in data.get('inherited_receipts_sha256',{}).items():assert sha(ROOT/name)==digest,name;queue.append(ROOT/name)
 for name,digest in data.get('objects_sha256',data.get('object_sha256',{})).items():
  path=Path(name);assert sha(path)==digest,name;module=name.rsplit('ChatResponseReferenceWork/',1)[1]
  if module in objects:assert objects[module][1]==digest,module
  objects[module]=(path,digest)
out=H/'Build/final'
for module,(p,digest) in objects.items():
 target=out/'ChatResponseReferenceWork'/module
 if target.exists():assert sha(target)==digest,target
 else:target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
files=[H/(m+'.lean') for m in modules]+[H/n for n in ['README.md','check.py','record.py']];before={str(p.relative_to(ROOT)):sha(p) for p in files}
env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with (H/'audit.log').open('w') as log:subprocess.run(['python3',str(CHAT/'check.py'),*['StreamingV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
log=(H/'audit.log').read_text();assert 'sorryAx' not in log and '_native.' not in log
for name,digest in before.items():assert sha(ROOT/name)==digest,name
print('Three-module numeric varint/prefix/native scalar projection reproduction PASS; complete streaming composition OPEN')
