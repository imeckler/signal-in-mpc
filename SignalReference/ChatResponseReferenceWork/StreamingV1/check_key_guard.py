#!/usr/bin/env python3
"""Required combined span check: new modules only, immutable log, clean aggregate."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
queue=[H/'key-transition-audit.json'];seen={};objects={};sources={}
while queue:
 p=queue.pop()
 if str(p) in seen:continue
 seen[str(p)]=sha(p);data=json.loads(p.read_text())
 for name,digest in data['source_sha256'].items():assert sha(ROOT/name)==digest,name;sources[name]=digest
 for name,digest in data.get('core_source_sha256',{}).items():assert sha(ROOT/name)==digest,name
 for name,digest in data.get('core_object_sha256',{}).items():assert sha(Path(name))==digest,name
 for name,digest in data.get('inherited_receipts_sha256',{}).items():assert sha(ROOT/name)==digest,name;queue.append(ROOT/name)
 for name,digest in data.get('objects_sha256',data.get('object_sha256',{})).items():
  path=Path(name);assert sha(path)==digest,name;module=name.rsplit('ChatResponseReferenceWork/',1)[1]
  if module in objects:assert objects[module][1]==digest,module
  objects[module]=(path,digest)
out=H/'Build/key-guard-v1-final'
for module,(p,digest) in objects.items():
 target=out/'ChatResponseReferenceWork'/module
 if target.exists():assert sha(target)==digest,target
 else:target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
modules=['KeyGuard','CoreKeyGuard'];files=[H/(m+'.lean') for m in modules]+[H/n for n in ['check_key_guard.py','KEY_GUARD.md']];keySource=ROOT/'SignalReference/ProtoParseWork/FullParserV3Work/KeyCircuit.lean';files.append(keySource);assert sha(keySource)=='7364b8347064a819e6bdd1d5b6849999b880aadcf52b69b98d76e0a948ce02cb';before={str(p.relative_to(ROOT)):sha(p) for p in files}
token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12];logpath=H/f'key-guard-{token}-{os.getpid()}.log'
env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with logpath.open('x') as log:
 # Recheck the newly used accepted key-circuit lemma in the isolated output.
 cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
 ref=CHAT.parent
 paths=[out,ref/'ProtoParseWork/ModelCandidate/Build',ROOT/'.lake/build/lib/lean',CHAT/'Build',ref/'ProtoParseWork/FullParserV3Work/Build',ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
 leanenv=env.copy();leanenv['LEAN_PATH']=os.pathsep.join(map(str,paths))
 for src in (ref/'ProtoParseWork/FullParserV3Work/Build').rglob('*.olean'):
  dst=out/src.relative_to(ref/'ProtoParseWork/FullParserV3Work/Build')
  if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve())
 keyObject=out/'ProtoParseWork/FullParserV3Work/KeyCircuit.olean';keyObject.parent.mkdir(parents=True,exist_ok=True)
 if keyObject.is_symlink():keyObject.unlink()
 subprocess.run(['lean','-o',str(keyObject),str(keySource)],cwd=ref,env=leanenv,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=120)
 subprocess.run(['python3',str(CHAT/'check.py'),*['StreamingV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
log=logpath.read_text();assert 'sorryAx' not in log and '_native.' not in log
for name in ['common_key_exact','native_key_rejected_common','core_common_key_reject','native_key_failure_core','native_key_failure_tail']:assert name+"' depends on axioms:" in log
for name,digest in {**sources,**before}.items():assert sha(ROOT/name)==digest,name
for p,digest in objects.values():assert sha(p)==digest,p
(H/'key-guard-audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Actual native key validation failures reject in actual Core common-key guard and stay rejected through arbitrary tail/finalization. Component checkpoint, not complete schema/streaming refinement.','aggregate_exit_code':0,'source_sha256':before,'inherited_receipts_sha256':{str(Path(p).relative_to(ROOT)):digest for p,digest in seen.items()},'inherited_source_count':len(sources),'inherited_object_count':len(objects),'kernel_log_path':str(logpath),'kernel_log_sha256':sha(logpath),'kernel_log':log,'new_dependency_object_sha256':{str(keyObject):sha(keyObject)},'objects_sha256':{str(out/'ChatResponseReferenceWork/StreamingV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/StreamingV1'/(m+'.olean')) for m in modules}},indent=2)+'\n')
print(f'Two key-guard modules PASS aggregate0; immutable log {logpath.name}; no unrelated native rerun')
