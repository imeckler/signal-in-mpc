#!/usr/bin/env python3
"""Check scoped source-preserving dispatch/content model and actual AES/compiler composition."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipt=json.loads((HERE/'complete-extraction-report.json').read_text());assert receipt['charon_exit']==0 and receipt['aeneas_exit']==0 and not receipt['has_errors']
 for name,want in receipt['source_sha256'].items():assert sha(ROOT/name)==want,name
 source=(ROOT/'.deps/libsignal-vendor/aes-0.9.1/src/soft.rs').read_text();selected=(HERE/'ArtifactsComplete/selected-methods.rs').read_text();assert selected in source
 methods=(HERE/'ArtifactsComplete/instantiated-methods.rs').read_text();assert methods.count('aes256_encrypt(')==2
 transformed=selected.replace('$fixslice_encrypt','aes256_encrypt');single=transformed[:transformed.index('\n\n            #[inline(always)]')];parallel=transformed[transformed.index('            fn encrypt_par_blocks'):]
 assert methods=="impl Backend<'_> {\n"+single.replace('            fn ','            pub fn ',1)+'\n'+parallel.replace('            fn ','            pub fn ',1)+'\n}\n'
 assert (ROOT/'.deps/reference-aes-fixed-dispatch-complete-v1/src/lib.rs').read_text()==(HERE/'Model/prefix.rs').read_text()+methods
 modules=['GeneratedComplete/Types','GeneratedComplete/FunsExternal','GeneratedComplete/Funs','WrapperReference'];names=[]
 for suffix in modules:
  module='AesCtrBlockWork/FixedDispatchV1Work/'+suffix;path=REF/(module+'.lean');body=path.read_text();assert not any(t in body for t in ['native_decide','bv_decide','sorry','axiom ']);names+=re.findall(r'^theorem (\w+)',body,re.M)
  output=base.BUILD/(module+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(output),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 assert len(names)>=10 and 'single_computed_compiled'in names
 audit=base.BUILD/'FixedDispatchAxioms.lean';audit.write_text('import AesCtrBlockWork.FixedDispatchV1Work.WrapperReference\n'+''.join('#print axioms LibSignalReference.Candidate.FixedDispatch.'+n+'\n'for n in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'complete-extraction-report.json',HERE/'Model/prefix.rs',HERE/'Model/Cargo.toml',HERE/'extract_complete.py',HERE/'ArtifactsComplete/selected-methods.rs',HERE/'ArtifactsComplete/instantiated-methods.rs',*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,foundation_axioms_only=True,kernel_endpoints=len(names),endpoints=names,pinned_wrapper_statement_text_preserved=True,explicit_fixed_dispatch_and_library_model_trusted=True,actual_AES_entry_linkage_is_definition=True,both_owner_continuations_preserved=True,computed_key_schedule_to_single_wrapper_to_compiled_circuit=True,parallel_wrapper_to_actual_AES_entry=True,whole_crypto_result_assumed=False,original_GAT_graph_refinement=False,address_unsafe_pointer_and_Drop_proved=False,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str((base.BUILD/('AesCtrBlockWork/FixedDispatchV1Work/'+m+'.olean')).relative_to(ROOT)):sha(base.BUILD/('AesCtrBlockWork/FixedDispatchV1Work/'+m+'.olean'))for m in modules}),indent=2)+'\n');print('PASS',len(names),'foundation-only wrapper/actual AES/compiler endpoints')
if __name__=='__main__':main()
