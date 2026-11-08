#!/usr/bin/env python3
"""Reproduce generated declarations; require byte-identical checked-in computation."""
from pathlib import Path
import subprocess,json,hashlib
H=Path(__file__).resolve().parent;ROOT=H.parents[3];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
raw=H/'Artifacts/one-step/put.llbc';named=raw.with_name('named.llbc')
assert sha(raw)==json.loads((H/'extraction.json').read_text())['llbc_sha256']
subprocess.run(['python3',str(ROOT/'SignalReference/ChatResponseReferenceWork/PartialMonoCandidate/name_specializations.py'),str(raw),str(named)],check=True,timeout=30)
binary=ROOT/'SignalReference/ProtoParseWork/SkipTranslatorWork/Bin/candidate';assert sha(binary)=='5ea6276549fac0be5c55ac6608ae8b4efa1dd1b147c15a988543871d8094bbec'
out=H/'Build/replay';args=[str(binary),'-backend','lean',str(named),'-dest',str(out),'-subdir','/ChatResponseReferenceWork/StringContentV3/ContiguousPut/GeneratedOneStep','-namespace','ContiguousPutOneStep','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'replay-translation.log').open('w') as f:subprocess.run(args,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=30)
for n in ['Types.lean','Funs.lean','FunsExternal_Template.lean']:
 assert (out/'ChatResponseReferenceWork/StringContentV3/ContiguousPut/GeneratedOneStep'/n).read_bytes()==(H/'GeneratedOneStep'/n).read_bytes(),n
(H/'translation.json').write_text(json.dumps({'scope':'Byte-identical generated declarations, declaration-name repair only; handwritten external models separate','command':args,'translator_sha256':sha(binary),'llbc_sha256':sha(raw),'named_llbc_sha256':sha(named),'script_sha256':sha(Path(__file__)),'generated_sha256':{n:sha(H/'GeneratedOneStep'/n) for n in ['Types.lean','Funs.lean','FunsExternal_Template.lean']}},indent=2)+'\n');print('3 unchanged generated files reproduce byte-for-byte')
