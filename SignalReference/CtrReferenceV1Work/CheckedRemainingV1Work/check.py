#!/usr/bin/env python3
"""Actual callback composition: computed key -> counter/AES -> source XOR -> compiler."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipt=json.loads((HERE/'extraction-report.json').read_text());assert receipt['charon_exit']==0 and receipt['aeneas_exit']==0 and not receipt['has_errors']
 for n,w in receipt['source_sha256'].items():assert sha(ROOT/n)==w,n
 selected=(HERE/'Artifacts/selected-method.rs').read_text();source=ROOT/'.deps/libsignal-vendor/cipher-0.5.2/src/stream/wrapper.rs';assert selected in source.read_text()
 method=selected.replace('    fn check_remaining','    pub fn check_remaining').replace('T::BlockSize::USIZE','16');assert method in (HERE/'Artifacts/model.rs').read_text()
 std_source=ROOT/'.deps/rust-nightly-2026-08-18/lib/rustlib/src/rust/library/core/src/num/uint_macros.rs'
 assert 'let d = self / rhs;\n            let r = self % rhs;\n            if r > 0 {\n                d + 1\n            } else {\n                d\n            }' in std_source.read_text()
 inherited=[HERE.parent/'FixedGeneratorV1Work/proof-report.json',HERE.parent/'ReadBufferV1Work/proof-report.json']
 for p in inherited:
  rec=json.loads(p.read_text());assert rec['passed']
  for n,w in rec['source_sha256'].items():assert sha(ROOT/n)==w,n
 modules=['Generated/Types','Generated/FunsExternal','Generated/Funs','Reference'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/CheckedRemainingV1Work/'+suffix;path=REF/(module+'.lean');text=path.read_text();assert not any(t in text for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',text,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'CheckedCtr16Axioms.lean';audit.write_text('import CtrReferenceV1Work.CheckedRemainingV1Work.Reference\n'+''.join('#print axioms LibSignalReference.Candidate.CheckedCtr16.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract.py',HERE/'extraction-report.json',HERE/'Artifacts/model.rs',HERE/'Artifacts/selected-method.rs',std_source,*inherited,*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,backend_independent=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,actual_check_remaining_body_unchanged_except_fixed_BS16=True,remaining_slots_are_DEF_links_to_proved_actual_source=True,pinned_div_ceil_Std_arithmetic_content_model_trusted=True,all_Usize_request_lengths_and_valid_buffer_cursors=True,exhausted_counter_permits_only_cached_bytes=True,accepted_requests_cannot_counter_wrap=True,whole_buffered_CTR_HMAC_KDF_open=True,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS',len(names),'foundation-only actual exhaustion decision endpoints')
if __name__=='__main__':main()
