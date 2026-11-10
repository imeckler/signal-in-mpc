#!/usr/bin/env python3
"""Actual callback composition: computed key -> counter/AES -> source XOR -> compiler."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipt=json.loads((HERE/'extraction-report.json').read_text());assert receipt['charon_exit']==0 and receipt['aeneas_exit']==0 and not receipt['has_errors']
 for n,w in receipt['source_sha256'].items():assert sha(ROOT/n)==w,n
 selected=(HERE/'Artifacts/selected-method.rs').read_text();source=ROOT/'.deps/libsignal-vendor/cipher-0.5.2/src/stream/core_api.rs';assert selected in source.read_text()
 method=selected.replace('    fn gen_tail_blocks','    pub fn gen_tail_blocks').replace('Block<Self>','Block').replace('Self::ParBlocksSize::USIZE','4');assert method in (HERE/'Artifacts/model.rs').read_text()
 std_source=ROOT/'.deps/rust-nightly-2026-08-18/lib/rustlib/src/rust/library/core/src/slice/iter.rs';assert 'self.iter_mut()' in std_source.read_text()
 inherited=[HERE.parent/'ApplyBlockV1Work/proof-report.json',HERE.parent/'CheckedRemainingV1Work/proof-report.json']
 for p in inherited:
  rec=json.loads(p.read_text());assert rec['passed']
  for n,w in rec['source_sha256'].items():assert sha(ROOT/n)==w,n
 modules=['Generated/Types','Generated/FunsExternal','Generated/Funs','Reference','Circuit'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/TailGeneratorV1Work/'+suffix;path=REF/(module+'.lean');text=path.read_text();assert not any(t in text for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',text,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'CtrTail16Axioms.lean';audit.write_text('import CtrReferenceV1Work.TailGeneratorV1Work.Circuit\n'+''.join('#print axioms LibSignalReference.Candidate.CtrTail16.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract.py',HERE/'extraction-report.json',HERE/'Artifacts/model.rs',HERE/'Artifacts/selected-method.rs',std_source,*inherited,*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,backend_independent=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,actual_tail_loop_assertion_and_iterator_writeback_retained=True,generator_slot_DEF_links_proved_actual_counter_and_AES=True,pinned_IntoIterator_binding_DEF_dispatches_official_iter_mut_model=True,arbitrary_slices_length_zero_to_three=True,oversize_rejected_before_generation=True,actual_wrapper_acceptance_implies_no_counter_wrap=True,actual_key_schedule_tail_trace_and_fresh_XOR_compiler_composed=True,public_deterministic_fresh_counter_profile=True,full_ApplyBlocksCtx_buffered_caller_HMAC_KDF_open=True,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS',len(names),'foundation-only actual tail/counter/AES/compiler endpoints')
if __name__=='__main__':main()
