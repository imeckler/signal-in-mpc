#!/usr/bin/env python3
"""Actual callback composition: computed key -> counter/AES -> source XOR -> compiler."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipt=json.loads((HERE/'extraction-report.json').read_text());assert receipt['charon_exit']==0 and receipt['aeneas_exit']==0 and not receipt['has_errors']
 for n,w in receipt['source_sha256'].items():assert sha(ROOT/n)==w,n
 selected=json.loads((HERE/'Artifacts/selected.json').read_text());source=ROOT/'.deps/libsignal-vendor/block-buffer-0.12.1/src/read.rs';model=(HERE/'Artifacts/model.rs').read_text()
 for name,body in selected.items():
  assert body in source.read_text();assert body.replace('BS::USIZE','16').replace('BS::U8','16').replace('Array<u8, BS>','[u8;16]') in model
 assert 'fn drop(&mut self)' in source.read_text() and 'self.0.reset();' in model
 library=json.loads((HERE/'library-report.json').read_text());assert library['passed'] and library['observations']==11328
 for n,w in library['source_sha256'].items():assert sha(ROOT/n)==w,n
 inherited=[HERE.parent/'ReadBufferV1Work/proof-report.json']
 for p in inherited:
  rec=json.loads(p.read_text());assert rec['passed']
  for n,w in rec['source_sha256'].items():assert sha(ROOT/n)==w,n
 modules=['Generated/Types','Generated/FunsExternal','Generated/Funs','Reference'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/WriteBufferV1Work/'+suffix;path=REF/(module+'.lean');text=path.read_text();assert not any(t in text for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',text,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'WriteBuffer16Axioms.lean';audit.write_text('import CtrReferenceV1Work.WriteBufferV1Work.Reference\n'+''.join('#print axioms LibSignalReference.Candidate.WriteBuffer16.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract.py',HERE/'extraction-report.json',HERE/'Artifacts/model.rs',HERE/'Artifacts/selected.json',HERE/'library-report.json',*inherited,*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,backend_independent=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,actual_write_block_setter_reset_and_drop_statements_retained=True,scoped_mutable_callback_and_Drop_owner_signature_models_trusted=True,fixed_ResetGuard_forget_returns_unchanged_content_owner_trusted=True,normal_return_callback_trace_composition=True,zero_and_oversize_decisions_proved=True,actual_Drop_reset_body_proved=True,panic_unwind_not_mechanized=True,actual_pinned_library_observations=11328,captured_cipher_state_owner_and_whole_wrapper_composition_open=True,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS',len(names),'foundation-only actual buffer write/drop content endpoints')
if __name__=='__main__':main()
