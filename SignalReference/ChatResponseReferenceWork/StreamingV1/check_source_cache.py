#!/usr/bin/env python3
"""Required combined span check: new modules only, immutable log, clean aggregate."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
queue=[H/'known-resume-audit.json'];seen={};objects={};sources={};external={}
while queue:
 p=queue.pop()
 if str(p) in seen:continue
 seen[str(p)]=sha(p);data=json.loads(p.read_text())
 for name,digest in data['source_sha256'].items():assert sha(ROOT/name)==digest,name;sources[name]=digest
 for name,digest in data.get('core_source_sha256',{}).items():assert sha(ROOT/name)==digest,name
 for name,digest in data.get('core_object_sha256',{}).items():assert sha(Path(name))==digest,name
 for name,digest in data.get('inherited_receipts_sha256',{}).items():assert sha(ROOT/name)==digest,name;queue.append(ROOT/name)
 for name,digest in data.get('new_dependency_object_sha256',{}).items():assert sha(Path(name))==digest,name;external[name]=digest
 for name,digest in data.get('objects_sha256',data.get('object_sha256',{})).items():
  path=Path(name);assert sha(path)==digest,name;module=name.rsplit('ChatResponseReferenceWork/',1)[1]
  if module in objects:assert objects[module][1]==digest,module
  objects[module]=(path,digest)
out=H/'Build/source-cache-v1-final'
for module,(p,digest) in objects.items():
 target=out/'ChatResponseReferenceWork'/module
 if target.exists():assert sha(target)==digest,target
 else:target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
for name,digest in external.items():
 assert sha(Path(name))==digest,name
 for src in (ROOT/'SignalReference/ProtoParseWork/FullParserV3Work/Build').rglob('*.olean'):
  dst=out/src.relative_to(ROOT/'SignalReference/ProtoParseWork/FullParserV3Work/Build')
  if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve())
 module=name.rsplit('/ProtoParseWork/',1)[1];target=out/'ProtoParseWork'/module
 if target.is_symlink():target.unlink()
 target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(Path(name).resolve())
modules=['SourceCache','ScalarCacheResume','BodyCacheResume','MessageCacheResume','KnownKeyCacheReady'];files=[H/(m+'.lean') for m in modules]+[H/n for n in ['check_source_cache.py','SOURCE_CACHE.md']];before={str(p.relative_to(ROOT)):sha(p) for p in files}
token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12];logpath=H/f'source-cache-{token}-{os.getpid()}.log'
env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with logpath.open('x') as log:
 subprocess.run(['python3',str(CHAT/'check.py'),*['StreamingV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
log=logpath.read_text();assert 'sorryAx' not in log and '_native.' not in log
for name in ['actual_default_cache','source_cache_id','source_cache_status','source_cache_message','source_cache_body','source_cache_headers','actual_scalar_cache_resumes','actual_body_cache_resumes','actual_message_cache_resumes','actual_known_key_cache_ready']:assert name+"' depends on axioms:" in log
for name,digest in {**sources,**before}.items():assert sha(ROOT/name)==digest,name
for p,digest in objects.values():assert sha(p)==digest,p
(H/'source-cache-audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Executable actual source-cache projection/defaults and actual generated known key/scalar/body/accepted String loop steps preserve CacheAgrees plus complete child-loop boundaries, retaining source content/suffix/body events. Full scan/error/header/group/outer/HTTP/compiler composition remains open.','aggregate_exit_code':0,'source_sha256':before,'inherited_receipts_sha256':{str(Path(p).relative_to(ROOT)):digest for p,digest in seen.items()},'inherited_source_count':len(sources),'inherited_object_count':len(objects),'kernel_log_path':str(logpath),'kernel_log_sha256':sha(logpath),'kernel_log':log,'new_dependency_object_sha256':external,'objects_sha256':{str(out/'ChatResponseReferenceWork/StreamingV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/StreamingV1'/(m+'.olean')) for m in modules}},indent=2)+'\n')
print(f'Five actual source-cache modules PASS aggregate0; immutable log {logpath.name}; no unrelated native rerun')
