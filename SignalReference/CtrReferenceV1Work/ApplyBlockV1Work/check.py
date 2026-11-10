#!/usr/bin/env python3
"""Actual callback composition: computed key -> counter/AES -> source XOR -> compiler."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipt=json.loads((HERE/'extraction-report.json').read_text());assert receipt['charon_exit']==0 and receipt['aeneas_exit']==0 and not receipt['has_errors']
 for n,w in receipt['source_sha256'].items():assert sha(ROOT/n)==w,n
 source=(ROOT/'.deps/libsignal-vendor/cipher-0.5.2/src/stream/core_api.rs').read_text();selected=(HERE/'Artifacts/selected-method.rs').read_text();assert selected in source;body=selected[selected.index('{'):];assert '    pub fn call(mut self, backend: &mut Backend) '+body in (HERE/'Artifacts/model.rs').read_text()
 inherited=[HERE.parent/'FixedGeneratorV1Work/proof-report.json',HERE.parent/'XorContentV1Work/proof-report.json']
 for p in inherited:
  rec=json.loads(p.read_text());assert rec['passed']
  for n,w in rec['source_sha256'].items():assert sha(ROOT/n)==w,n
 modules=['Generated/Types','Generated/FunsExternal','Generated/Funs','Reference','Circuit'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/ApplyBlockV1Work/'+suffix;path=REF/(module+'.lean');text=path.read_text();assert not any(t in text for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',text,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'ApplyBlock16Axioms.lean';audit.write_text('import CtrReferenceV1Work.ApplyBlockV1Work.Circuit\n'+''.join('#print axioms LibSignalReference.Candidate.ApplyBlock16.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract.py',HERE/'extraction-report.json',HERE/'Artifacts/model.rs',HERE/'Artifacts/selected-method.rs',*inherited,*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,backend_independent=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,actual_callback_statement_body_unchanged=True,dispatch_and_flattened_content_layout_trusted=True,primitive_slots_are_DEF_links_to_proved_source=True,actual_key_schedule_counter_AES_XOR_callback_compiler_composed=True,key_owner_and_nonce_prefix_preserved=True,counter_profile_public_deterministic_index=True,unchecked_core_API=True,remaining_preflight_in_full_wrapper_still_required=True,full_StreamCipherCoreWrapper_parallel_tail_HMAC_KDF_not_proved=True,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str((base.BUILD/('CtrReferenceV1Work/ApplyBlockV1Work/'+m+'.olean')).relative_to(ROOT)):sha(base.BUILD/('CtrReferenceV1Work/ApplyBlockV1Work/'+m+'.olean'))for m in modules}),indent=2)+'\n');print('PASS',len(names),'foundation-only actual counter/AES/XOR callback/compiler endpoints')
if __name__=='__main__':main()
