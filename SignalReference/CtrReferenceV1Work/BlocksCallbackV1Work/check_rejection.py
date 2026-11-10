#!/usr/bin/env python3
"""Preserve the exact rejected whole-callback typing boundary; NOT a proof pass."""
import hashlib,importlib.util,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];REF=ROOT/'SignalReference'
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 rec=json.loads((HERE/'get-selection-report.json').read_text());assert rec['aeneas_exit']==0
 for n,w in rec['generated_sha256'].items():assert sha(ROOT/n)==w,n
 extraction=json.loads((HERE/'get-extraction-report.json').read_text())
 for n,w in extraction['source_sha256'].items():assert sha(ROOT/n)==w,n
 modules=['GeneratedGetSelected/Types','GeneratedGetSelected/FunsExternal','GeneratedGetSelected/Funs'];results=[]
 for i,m in enumerate(modules):
  module='CtrReferenceV1Work/BlocksCallbackV1Work/'+m;out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60)
  results.append(dict(module=module,exit=r.returncode))
  if i<2:assert r.returncode==0,r.stdout+r.stderr
  else:
   assert r.returncode!=0
   text=r.stdout+r.stderr
   for expected in ['29:10: error: Type mismatch','74:4: error: Type mismatch','235:34: error: Application type mismatch']:
    assert expected in text, text
   (HERE/'typing-rejection.log').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract.py',HERE/'extract_opaque_get.py',HERE/'select_metadata.py',HERE/'select_get_metadata.py',HERE/'get-extraction-report.json',HERE/'get-selection-report.json',HERE/'ArtifactsGet/model.rs',HERE/'ArtifactsGet/selected-method.rs',*[HERE/(m+'.lean')for m in modules]]
 (HERE/'typing-rejection-report.json').write_text(json.dumps(dict(candidate_only=True,whole_callback_proved=False,passed_expected_rejection=True,generated_computational_bodies_unchanged=True,primitive_adapter_module_typechecked=True,whole_callback_generated_graph_does_not_typecheck=True,reason='mutable Iterator/IntoIterator trait signatures and higher-order loop owner-exit continuation mismatch',results=results,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},rejection_log_sha256=sha(HERE/'typing-rejection.log')),indent=2)+'\n')
 print('EXPECTED REJECTION: whole callback borrow/trait signatures; no proof claim')
if __name__=='__main__':main()
