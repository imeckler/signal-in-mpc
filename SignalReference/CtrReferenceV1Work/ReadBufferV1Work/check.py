#!/usr/bin/env python3
"""Kernel-check actual fixed ReadBuffer cache methods against logical unread suffix."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 rec=json.loads((HERE/'opaque-attr-extraction-report.json').read_text());assert rec['charon_exit']==0 and rec['aeneas_exit']==0 and not rec['has_errors']
 for name,want in rec['source_sha256'].items():assert sha(ROOT/name)==want,name
 source=(ROOT/'.deps/libsignal-vendor/block-buffer-0.12.1/src/read.rs').read_text();selected=json.loads((HERE/'ArtifactsOpaqueAttr/selected.json').read_text());assert len(selected)==6
 for body in selected.values():assert body in source
 methods='\n'.join(('    #[charon::opaque]\n'+b if n=='get_pos'else b)for n,b in selected.items()).replace('BS::USIZE','16').replace('BS::U8','16')
 assert (HERE/'ArtifactsOpaqueAttr/model.rs').read_text()=='#![register_tool(charon)]\n#![feature(register_tool)]\npub struct ReadBuffer { pub buffer:[u8;16] }\nimpl ReadBuffer {\n'+methods+'\n}\n'
 modules=['GeneratedOpaqueAttr/Types','GeneratedOpaqueAttr/FunsExternal','GeneratedOpaqueAttr/Funs','CursorReference'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/ReadBufferV1Work/'+suffix;path=REF/(module+'.lean');body=path.read_text();assert not any(t in body for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',body,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'ReadBuffer16Axioms.lean';audit.write_text('import CtrReferenceV1Work.ReadBufferV1Work.CursorReference\n'+''.join('#print axioms LibSignalReference.Candidate.ReadBuffer16.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True)
 assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract_opaque_attr.py',HERE/'opaque-attr-extraction-report.json',HERE/'ArtifactsOpaqueAttr/model.rs',HERE/'ArtifactsOpaqueAttr/selected.json',*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,backend_independent=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,selected_non_getter_method_statement_bodies_retained=True,fixed_hybrid_array_native16_content_binding_trusted=True,source_grounded_getter_model_trusted=True,getter_actual_bottom_branch_translation_not_proved=True,valid_cursor_domain='1..16, Fin16 representation; invariant established by setter/reset',requested_usize_unrestricted=True,all_payload_tail_bytes_unrestricted=True,actual_read_cached_to_take_drop_logical_suffix=True,both_supported_platform_widths_checked=True,source_write_block_ResetGuard_and_callbacks_not_yet_composed=True,full_CTR_HMAC_KDF_refinement=False,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str((base.BUILD/('CtrReferenceV1Work/ReadBufferV1Work/'+m+'.olean')).relative_to(ROOT)):sha(base.BUILD/('CtrReferenceV1Work/ReadBufferV1Work/'+m+'.olean'))for m in modules}),indent=2)+'\n');print('PASS',len(names),'foundation-only actual fixed ReadBuffer cache/owner endpoints')
if __name__=='__main__':main()
