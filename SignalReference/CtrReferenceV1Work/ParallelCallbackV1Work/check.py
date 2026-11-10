#!/usr/bin/env python3
"""Actual callback composition: computed key -> counter/AES -> source XOR -> compiler."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipt=json.loads((HERE/'extraction-report.json').read_text());assert receipt['charon_exit']==0 and receipt['aeneas_exit']==0 and not receipt['has_errors']
 for n,w in receipt['source_sha256'].items():assert sha(ROOT/n)==w,n
 source=(ROOT/'.deps/libsignal-vendor/cipher-0.5.2/src/stream/core_api.rs').read_text();selected=(HERE/'Artifacts/selected-method.rs').read_text();assert selected in source;body=selected[selected.index('{'):];assert "pub fn apply_parallel_chunk(backend:&mut Backend,mut chunk:InOut<'_,'_>) "+body in (HERE/'Artifacts/model.rs').read_text()
 inherited=[HERE.parent/'ParallelGeneratorV1Work/proof-report.json',HERE.parent/'ParallelXorV1Work/proof-report.json',HERE.parent/'CheckedRemainingV1Work/proof-report.json']
 for p in inherited:
  rec=json.loads(p.read_text());assert rec['passed']
  for n,w in rec['source_sha256'].items():assert sha(ROOT/n)==w,n
 modules=['Generated/Types','Generated/FunsExternal','Generated/Funs','Reference','Circuit'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/ParallelCallbackV1Work/'+suffix;path=REF/(module+'.lean');text=path.read_text();assert not any(t in text for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',text,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'ParallelCallback4Axioms.lean';audit.write_text('import CtrReferenceV1Work.ParallelCallbackV1Work.Circuit\n'+''.join('#print axioms LibSignalReference.Candidate.ParallelCallback4.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract.py',HERE/'extraction-report.json',HERE/'Artifacts/model.rs',HERE/'Artifacts/selected-method.rs',*inherited,*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,backend_independent=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,actual_selected_parallel_chunk_statement_block_unchanged=True,source_block_factoring_and_fixed_content_dispatch_trusted=True,primitive_slots_DEF_link_proved_actual_source=True,computed_key_schedule_counter_parallel_AES_nested_XOR_and_compiler_composed=True,key_nonce_and_complete_output_owner_preserved=True,checked_wrapper_acceptance_implies_no_counter_wrap=True,counter_is_public_profile_parameter=True,full_ApplyBlocksCtx_loop_and_byte_chunk_view_not_yet_proved=True,full_buffered_wrapper_HMAC_KDF_open=True,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS',len(names),'foundation-only actual parallel chunk/compiler endpoints')
if __name__=='__main__':main()
