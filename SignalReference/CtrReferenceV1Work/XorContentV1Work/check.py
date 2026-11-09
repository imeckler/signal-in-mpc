#!/usr/bin/env python3
"""Audit retained source XOR loop/owner/compiler agreement under explicit content models."""
import copy,hashlib,importlib.util,json,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
s=importlib.util.spec_from_file_location('b',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(s);s.loader.exec_module(base)
sys.path.insert(0,str(REF));from MetadataWork.trim_step_metadata import walk,reviewed_input_fingerprint
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 rec=json.loads((HERE/'extraction-report.json').read_text());assert rec['charon_exit']==0 and rec['aeneas_exit']==2
 for n,w in rec['source_sha256'].items():assert sha(ROOT/n)==w,n
 selected=(HERE/'Artifacts/selected-method.rs').read_text();source=(ROOT/'.deps/libsignal-vendor/inout-0.2.2/src/inout.rs').read_text();assert selected in source
 method=selected.replace('&Array<u8, N>','&Block').replace('ptr::read(self.in_ptr)','*self.input').replace('Array::<u8, N>::default()','Block::default()').replace('N::USIZE','16').replace('ptr::write(self.out_ptr, temp);','*self.output = temp;')
 assert (HERE/'Artifacts/model.rs').read_text()=='pub type Block=[u8;16];\npub struct InOut<\'i,\'o> { pub input:&\'i Block, pub output:&\'o mut Block }\nimpl InOut<\'_,\'_> {\n'+method+'\n}\n'
 sel=json.loads((HERE/'selection-report.json').read_text());assert sha(HERE/'select_metadata.py')==sel['script_sha256'];assert sel['aeneas_exit']==0 and sel['reversible_metadata_changes']==7
 original=HERE/'Artifacts/xor.llbc';normalized=HERE/'ArtifactsSelected/selected.llbc';assert sha(original)==sel['original_sha256']and sha(normalized)==sel['selected_sha256'];before=json.loads(original.read_text());after=json.loads(normalized.read_text());assert reviewed_input_fingerprint(before)=='45a98c73f2cebfd50619ec2a8e979989af4debe50a6e375c986e2c590fa942ac'
 changes=HERE/'ArtifactsSelected/changes.json';assert sha(changes)==sel['changes_sha256'];restored=copy.deepcopy(after)
 for c in json.loads(changes.read_text()):
  obj=restored
  for k in c['path'][:-1]:obj=obj[k]
  obj[c['path'][-1]]=c['before']
 assert restored==before
 for i,f in enumerate(before['translated']['fun_decls']):
  if f and f['body']!='Opaque':assert after['translated']['fun_decls'][i]==f
 semantic={k:v for k,v in after['translated'].items()if k not in ['item_names','short_names']}
 for node in walk(semantic):
  if isinstance(node,dict):
   assert node.get('Regular')not in[96,100];assert node.get('TraitMethod')not in[[2,2],[2,6]]
   if isinstance(node.get('skip_binder'),dict):assert node['skip_binder'].get('id')not in[96,100]
 for n,w in sel['generated_sha256'].items():assert sha(ROOT/n)==w,n
 modules=['GeneratedSelected/Types','GeneratedSelected/Funs','LoopReference','Circuit'];names=[]
 for suffix in modules:
  module='CtrReferenceV1Work/XorContentV1Work/'+suffix;path=REF/(module+'.lean');body=path.read_text();assert not any(t in body for t in ['sorry','axiom ','native_decide','bv_decide']);names+=re.findall(r'^theorem (\w+)',body,re.M)
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'XorContent16Axioms.lean';audit.write_text('import CtrReferenceV1Work.XorContentV1Work.Circuit\n'+''.join('#print axioms LibSignalReference.Candidate.XorContent16.'+n+'\n'for n in names));text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for g in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 assert '_native'not in text and 'sorryAx'not in text;(HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'extract.py',HERE/'select_metadata.py',HERE/'extraction-report.json',HERE/'selection-report.json',HERE/'Artifacts/model.rs',HERE/'Artifacts/selected-method.rs',changes,*[HERE/(m+'.lean')for m in modules]]
 (HERE/'proof-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),endpoints=names,foundation_axioms_only=True,backend_independent=True,retained_source_range_loop_and_XOR_statement=True,fixed_pointer_read_write_array_content_model_trusted=True,additional_unused_Step_metadata_selection_unmechanized=True,all_retained_computations_unchanged=True,all_input_data_old_output_bits_unrestricted=True,updated_owner_and_outer_borrow_continuation_retained=True,actual_source_instantiated_XOR_to_compiled_circuit=True,generic_InOutBuf_tail_and_four_block_XOR_not_yet_linked=True,whole_CTR_HMAC_KDF_proved=False,production_changed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str((base.BUILD/('CtrReferenceV1Work/XorContentV1Work/'+m+'.olean')).relative_to(ROOT)):sha(base.BUILD/('CtrReferenceV1Work/XorContentV1Work/'+m+'.olean'))for m in modules}),indent=2)+'\n');print('PASS',len(names),'foundation-only retained source XOR loop/owner/compiler endpoints')
if __name__=='__main__':main()
