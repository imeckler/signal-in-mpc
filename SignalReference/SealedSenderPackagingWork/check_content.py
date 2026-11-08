#!/usr/bin/env python3
"""Actual USMC derive encoder→circuit bytes; naming replay/body hashes explicit."""
import copy,hashlib,json,os,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];REF=HERE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def replay(original,selected,changes):
 before=json.loads(original.read_text());after=json.loads(selected.read_text());delta=json.loads(changes.read_text());copyOf=copy.deepcopy(before)
 for c in delta:
  at=copyOf
  for k in c['path'][:-1]:at=at[k]
  assert at[c['path'][-1]]==c['before'];at[c['path'][-1]]=c['after']
 assert copyOf==after
 for i,f in enumerate(before['translated']['fun_decls']):
  if f and f['body']!='Opaque':assert f==after['translated']['fun_decls'][i]
 return len(delta)
def main():
 payload=HERE/'payload-report.json';prior=json.loads(payload.read_text());assert prior['kernel_endpoints']==8 and not prior['payload_success_or_correctness_assumption']
 for name,digest in prior['source_sha256'].items():assert sha(ROOT/name)==digest,name
 original=HERE/'Artifacts/WireFields/ss_content.llbc';selected=HERE/'Artifacts/WireContent/selected.llbc';changes=selected.parent/'changes.json'
 assert replay(original,selected,changes)==13
 extraction=json.loads((original.parent/'inventory.json').read_text());assert extraction['charon_exit_code']==0 and not extraction['has_errors'] and extraction['counts']['ordered_decls']>0
 for name,digest in extraction['source_sha256'].items():assert sha(ROOT/name)==digest,name
 old=REF/'SignalMessageWork/BytesFieldWork';assert replay(old/'Artifacts/bytes_field.llbc',old/'Selected/selected.llbc',old/'Selected/changes.json')==10
 oldReview=json.loads((old/'Selected/review.json').read_text());assert oldReview['aeneas_exit_code']==0 and not oldReview['remaining_external_templates']
 for name,digest in oldReview['generated_files'].items():assert sha(REF/name)==digest,name
 review=json.loads((selected.parent/'review.json').read_text());assert review['aeneas_exit_code']==0
 for name,digest in review['generated_sha256'].items():assert sha(ROOT/name)==digest,name
 subprocess.run(['python3',str(HERE/'prepare_type_replay.py')],cwd=ROOT,check=True)
 naming=json.loads((HERE/'TypeReplay/replay.json').read_text());assert not naming['generated_computational_Funs_modified']
 for row in naming['rows']:
  assert sha(ROOT/row['Funs_file'])==row['original_Funs_sha256'] and row['exact_inverse_replay_checked']
 cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages');paths=[HERE/'Build',REF/'.lake/build/lib/lean',ROOT/'.lake/build/lib/lean',ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean'for p in cache.iterdir()if(p/'.lake/build/lib/lean').is_dir()];env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)))
 modules=[]
 for module in ['SignalMessageWork/BytesFieldWork/GeneratedSelected','SealedSenderPackagingWork/Generated/WireContent']:
  modules.append((module+'/Types',HERE/'TypeReplay/Modules'/module/'Types.lean',HERE/'TypeReplay/Modules'))
  if module.startswith('SealedSender'):modules.append((module+'/FunsExternal',REF/module/'FunsExternal.lean',REF))
  modules.append((module+'/Funs',REF/module/'Funs.lean',REF))
 modules += [('SealedSenderPackagingWork/'+name,HERE/(name+'.lean'),REF)for name in ['ContentWireReference','TypeReplay/Checks','ContentChecks']]
 audit=''
 for module,source,cwd in modules:
  out=HERE/'Build'/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  result=subprocess.run(['lean','-o',str(out),str(source)],cwd=cwd,env=env,text=True,capture_output=True,check=True);audit+=result.stdout+result.stderr
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)+audit.count('does not depend on any axioms')==15,audit
 for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'},audit
 assert 'sorryAx'not in audit and '_native'not in audit;(HERE/'content-axioms.txt').write_text(audit)
 files=[Path(__file__),payload,HERE/'prepare_type_replay.py',HERE/'select_wire_content_metadata.py',original,selected,changes,selected.parent/'review.json',old/'Selected/review.json',old/'Selected/changes.json',old/'Selected/selected.llbc',old/'Artifacts/bytes_field.llbc',HERE/'TypeReplay/replay.json']+[p for _,p,_ in modules]
 files += [ROOT/name for name in extraction['source_sha256']]+[ROOT/'TlsMpc/Signal/SealedSenderV1.lean',ROOT/'TlsMpc/Signal/Serialization.lean',ROOT/'TlsMpc/Signal/Varint.lean']
 report={'kernel_endpoints':15,'foundation_axioms_only':True,'native_reflection_used':False,'actual_derive_USMC_encoder_agreement':True,'numeric_circuit_to_actual_encoder_endpoint':True,'payload_contract_assumption':False,
  'domain':'MESSAGE2/defaultcontenthint/absentgroupID; arbitrary certificate/inner byte vectors and arbitrary existing output prefix with lengths+34<=official model Usize.max.',
  'proved':'Actual retained int32/key/varint/bytes/Vec-copy operations assemble exact SealedSenderV1.usmc bytes. Empty-output serialization and compiled numeric USMC bit agreement included.',
  'trust_boundary':['Pinned Aeneas translator/official scalar+container models; valid buffers and successful allocations below actual isize::MAX; heap/capacity/Drop/erasure excluded.','Exact13 reversible unused metadata changes for current actual encoder (plus reused prior helper selection), all retained computational bodies unchanged; independent scope review pending.','Deterministic type-export naming replay with definitional constructor aliases; original generated Funs bytes unchanged; all18 discriminants checked across3 co-imported real WireType namespaces.'],
  'not_established':['Whole UnidentifiedSenderMessageContent::new/encode_to_vec wrapper.','Certificate signature/validation, whole AES-CTR/HMAC/KDF/SS implementation refinement.','PrivateBuffer variable-length USMC packing semantics and full service composition.'],
  'source_sha256':{str(p.relative_to(ROOT)):sha(p)for p in files}}
 (HERE/'content-report.json').write_text(json.dumps(report,indent=2)+'\n');print('15 kernel endpoints; actual USMC encoder/numeric agreement and3-namespace collision regression passed')
if __name__=='__main__':main()
