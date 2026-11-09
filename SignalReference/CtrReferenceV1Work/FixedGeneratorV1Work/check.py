#!/usr/bin/env python3
"""Audit selected actual CTR/AES generator composition and backend-independent XOR compiler."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 rec=json.loads((HERE/'direct-extraction-report.json').read_text());assert rec['charon_exit']==0 and rec['aeneas_exit']==0 and not rec['has_errors']
 for name,want in rec['source_sha256'].items():assert sha(ROOT/name)==want,name
 source=(ROOT/'.deps/libsignal-vendor/ctr-0.10.1/src/ctr_core.rs').read_text();selected=(HERE/'ArtifactsDirect/selected-method.rs').read_text();assert selected in source
 instantiated=selected.replace('fn gen_ks_block','pub fn gen_ks_block',1).replace('Block<Self>','Block').replace('F::next_block','next_block').replace('((&tmp, block).into())','(make_inout((&tmp, block)))')
 assert (HERE/'ArtifactsDirect/model.rs').read_text().endswith("impl CtrBackend<'_,'_> {\n"+instantiated+'\n}\n')
 modules=['GeneratedDirect/Types','GeneratedDirect/FunsExternal','GeneratedDirect/Funs','GeneratorReference','DriverReference','BufferedReference','Circuit'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/FixedGeneratorV1Work/'+suffix;path=REF/(module+'.lean');body=path.read_text();assert not any(t in body for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',body,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'FixedCtrAxioms.lean';audit.write_text('import CtrReferenceV1Work.FixedGeneratorV1Work.Circuit\n'+''.join('#print axioms LibSignalReference.Candidate.FixedCtr.'+n+'\n'for n in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract_direct.py',HERE/'direct-extraction-report.json',HERE/'ArtifactsDirect/model.rs',HERE/'ArtifactsDirect/selected-method.rs',*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,backend_independent=True,source_counter_and_AES_def_linkage=True,scoped_dispatch_InOut_constructor_trusted=True,actual_generator_to_AES_and_counter_proved=True,actual_remaining_authorizes_no_wrap_driver=True,actual_key_schedule_to_generator_driver_to_compiled_XOR=True,logical_buffer_failure_preserves_state_and_old_output=True,logical_cache_bounds_and_consumption_proved=True,fresh_plaintext_bound_bytes=8192,full_Rust_generic_StreamCipherCoreWrapper_and_parallel_dispatch_proved=False,physical_ReadBuffer_cursor_and_InOutBuf_pointer_model_proved=False,source_XOR_iterator_loop_refinement_proved=False,HMAC_KDF_composition_proved=False,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str((base.BUILD/('CtrReferenceV1Work/FixedGeneratorV1Work/'+m+'.olean')).relative_to(ROOT)):sha(base.BUILD/('CtrReferenceV1Work/FixedGeneratorV1Work/'+m+'.olean'))for m in modules}),indent=2)+'\n');print('PASS',len(names),'foundation-only actual CTR/AES generator, bounded buffer and compiled XOR endpoints')
if __name__=='__main__':main()
