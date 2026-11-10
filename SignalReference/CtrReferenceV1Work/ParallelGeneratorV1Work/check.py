#!/usr/bin/env python3
"""Actual callback composition: computed key -> counter/AES -> source XOR -> compiler."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipt=json.loads((HERE/'value-extraction-report.json').read_text());assert receipt['charon_exit']==0 and receipt['aeneas_exit']==0 and not receipt['has_errors']
 for n,w in receipt['source_sha256'].items():assert sha(ROOT/n)==w,n
 inherited=[HERE.parent/'FixedGeneratorV1Work/proof-report.json']
 for p in inherited:
  rec=json.loads(p.read_text());assert rec['passed']
  for n,w in rec['source_sha256'].items():assert sha(ROOT/n)==w,n
 modules=['GeneratedValue/Types','GeneratedValue/FunsExternal','GeneratedValue/Funs','Reference'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/ParallelGeneratorV1Work/'+suffix;path=REF/(module+'.lean');text=path.read_text();assert not any(t in text for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',text,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'ParallelCtr4Axioms.lean';audit.write_text('import CtrReferenceV1Work.ParallelGeneratorV1Work.Reference\n'+''.join('#print axioms LibSignalReference.Candidate.ParallelCtr4.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract_value.py',HERE/'value-extraction-report.json',HERE/'ArtifactsValue/model.rs',HERE/'ArtifactsValue/selected-method.rs',*inherited,*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,backend_independent=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,actual_parallel_loop_retained=True,owned_layout_and_fixed_content_dispatch_trusted=True,actual_counter_and_AES_links_are_definitions=True,iterator_owner_writeback_proved=True,unchecked_parallel_core_only=True,full_buffered_wrapper_HMAC_KDF_open=True,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS',len(names),'foundation-only parallel CTR source endpoints')
if __name__=='__main__':main()
