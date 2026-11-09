#!/usr/bin/env python3
"""Isolated exported-AIG attribution only; no runtime/native MPC activation."""
from pathlib import Path
from array import array
import os,sys,json,hashlib,subprocess,time,resource
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];REF=ROOT/'SignalReference'
sys.path.insert(0,str(ROOT))
from backend_adapter.aig import statistics,_plan,_xor_sources
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
paths=[H/'Build/admission-export-v1-final',REF/'ProtoParseWork/ModelCandidate/Build',ROOT/'.lake/build/lib/lean',CHAT/'Build',REF/'ProtoParseWork/FullParserV3Work/Build',ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths))
def depth(image):
 nodes=image['nodes'];kinds=_plan(nodes,image['outputs'],True);levels=array('I',[0])*len(nodes)
 for index,node in enumerate(nodes):
  if not kinds[index] or node[0]!=2:continue
  left,_,right,_=_xor_sources(nodes,node) if kinds[index]==2 else node[1:]
  levels[index]=max(levels[left],levels[right])+(kinds[index]==1)
 return max((levels[node] for node,_ in image['outputs']),default=0)
files=[H/n for n in ['Stack32Codec.lean','AdmissionProgram.lean','AdmissionExportBridge.lean','EmitAdmission.lean','profile_admission.py','mixed-feed-audit.json']]+[ROOT/n for n in ['TlsMpc/TlsChatResponse.lean','TlsMpc/TlsChatResponseMux.lean','TlsMpc/Signal/Word64.lean','backend_adapter/aig.py']]
before={str(p.relative_to(ROOT)):sha(p)for p in files};rows=[];out=H/'Build/profile-admission-released-v1';out.mkdir(parents=True,exist_ok=True)
for mode in ['baseline-admit','candidate-admit']:
 path=out/(mode+'.json');log=out/(mode+'.log');start=time.monotonic()
 print('Exporting '+mode,flush=True)
 with path.open('w')as dst,log.open('w')as err:
  subprocess.run(['lean','-M2048','--run',str(H/'EmitAdmission.lean'),mode],cwd=REF,env=env,stdout=dst,stderr=err,check=True,timeout=45)
 image=json.loads(path.read_text());row={'mode':mode,'artifact_sha256':sha(path),'artifact_path':str(path),'input_bits':image['input_bits'],'output_bits':len(image['outputs']),**statistics(image),'and_dependency_depth':depth(image),'export_seconds':time.monotonic()-start}
 rows.append(row);print(json.dumps(row),flush=True)
assert before=={str(p.relative_to(ROOT)):sha(p)for p in files},'source changed during export'
report={'candidate_only':True,'runtime_promoted':False,'native_mpc_executed':False,'scope':'Admission-only exact exported AIG resource counts for original992B→982B versus compact592B→582B. Mixed admit/feed exported correctness proved separately. No byte re-export, native execution, timing comparison or runtime promotion.', 'lean_memory_limit_mb':2048,'cases':rows,'source_sha256':before,'child_peak_rss':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}
assert resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss < 2*1024**3,'RSS exceeded coordinated post-Kyber2GiB ceiling'
(H/'profile-admission-audit.json').write_text(json.dumps(report,indent=2)+'\n')
