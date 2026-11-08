#!/usr/bin/env python3
"""Actual append wrapper+actual Vec loop, explicit bounded content models."""
import copy,hashlib,json,os,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];REF=HERE.parent;PARSER=REF/'ProtoParseWork/BytesReferenceWork'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 inventoryPath=HERE/'Artifacts/PayloadAppend/inventory.json';inventory=json.loads(inventoryPath.read_text())
 assert inventory['charon_exit_code']==0 and inventory['aeneas_exit_code']==0 and not inventory['has_errors'] and inventory['verified_dependencies']
 for name,digest in inventory['source_sha256'].items():assert sha(ROOT/name)==digest,name
 oldInventoryPath=PARSER/'Artifacts/vec_replace_put_body/inventory.json';oldInventory=json.loads(oldInventoryPath.read_text())
 assert oldInventory['charon_exit_code']==0 and oldInventory['aeneas_exit_code']==0 and oldInventory['source_patches']==[]
 for name,digest in oldInventory['source_sha256'].items():assert sha(ROOT/name)==digest,name
 for name,digest in oldInventory['generated_files'].items():assert sha(REF/name)==digest,name
 oldLlbc=PARSER/'Artifacts/vec_replace_put_body/prost.llbc';assert sha(oldLlbc)==oldInventory['llbc_sha256']
 original=HERE/'Artifacts/PayloadAppend/ss_append.llbc';selected=HERE/'Artifacts/PayloadAppendSelected/selected.llbc';before=json.loads(original.read_text());after=json.loads(selected.read_text());changes=json.loads((selected.parent/'changes.json').read_text());assert len(changes)==5
 replay=copy.deepcopy(before)
 for c in changes:
  at=replay
  for k in c['path'][:-1]:at=at[k]
  assert at[c['path'][-1]]==c['before'];at[c['path'][-1]]=c['after']
 assert replay==after
 for i,f in enumerate(before['translated']['fun_decls']):
  if f and f['body']!='Opaque':assert f==after['translated']['fun_decls'][i]
 review=json.loads((selected.parent/'review.json').read_text());assert review['aeneas_exit_code']==0 and review['put_callback_slot_retained']==4
 for name,digest in review['generated_sha256'].items():assert sha(ROOT/name)==digest,name
 modules=[]
 for n in ['TypesExternal','Types','FunsExternal']:
  p=PARSER/'Modules/ProtoParseWork/FieldReferenceWork/Generated/bytes_step'/(n+'.lean') if n.endswith('External') else REF/'ProtoParseWork/FieldReferenceWork/Generated/bytes_step'/(n+'.lean')
  modules.append(('ProtoParseWork/FieldReferenceWork/Generated/bytes_step/'+n,p))
 modules.append(('BytesReferenceWork/Replayed/BufModel',PARSER/'Modules/BytesReferenceWork/Replayed/BufModel.lean'))
 for n in ['Types','FunsExternal','Funs']:
  p=PARSER/'Modules/ProtoParseWork/BytesReferenceWork/Generated/vec_replace_put_body'/(n+'.lean') if n=='FunsExternal' else PARSER/'Generated/vec_replace_put_body'/(n+'.lean')
  modules.append(('ProtoParseWork/BytesReferenceWork/Generated/vec_replace_put_body/'+n,p))
 modules.append(('BytesReferenceWork/VecReference',PARSER/'Modules/BytesReferenceWork/VecReference.lean'))
 for n in ['Types','FunsExternal','Funs']:modules.append(('SealedSenderPackagingWork/Generated/PayloadAppendSelected/'+n,HERE/'Generated/PayloadAppendSelected'/(n+'.lean')))
 modules.append(('SealedSenderPackagingWork/VecPayloadReference',HERE/'VecPayloadReference.lean'))
 cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages');paths=[HERE/'Build',ROOT/'.lake/build/lib/lean',ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean'for p in cache.iterdir()if(p/'.lake/build/lib/lean').is_dir()];env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,paths)))
 for module,source in modules:
  target=HERE/'Build'/(module+'.olean');target.parent.mkdir(parents=True,exist_ok=True);subprocess.run(['lean','-o',str(target),str(source)],cwd=REF,env=env,check=True)
 audit=subprocess.check_output(['lean',str(HERE/'PayloadChecks.lean')],cwd=REF,env=env,text=True);groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)+audit.count('does not depend on any axioms')==8,audit
 for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'},audit
 assert 'sorryAx'not in audit and '_native'not in audit;(HERE/'payload-axioms.txt').write_text(audit)
 files=[inventoryPath,oldInventoryPath,oldLlbc]+[ROOT/name for name in inventory['source_sha256']]+[ROOT/'.deps/aeneas-2026-08-27/backends/lean/Aeneas/Std'/name for name in ['Vec.lean','Slice.lean','Core/Iter.lean']]+[Path(__file__),HERE/'PayloadChecks.lean',HERE/'select_append_metadata.py',HERE/'extract_append.py',original,selected,selected.parent/'changes.json',selected.parent/'review.json']+[p for _,p in modules]
 report={'kernel_endpoints':8,'foundation_axioms_only':True,'actual_BytesAdapter_to_actual_Vec_put_append_proved':True,'payload_success_or_correctness_assumption':False,
  'domain':'Every destination prefix and contiguous source fitting official model Usize bound; empty source and overflow rejection included.',
  'trust_boundary':['Existing Vec/Slice content models, valid buffers, successful allocations below actual isize::MAX; addresses/capacity/Drop/erasure excluded.','Vec::as_slice forwards to official Vec.deref; shared Slice.advance reuses existing bounded Slice content model. No whole crypto/payload primitive interpretation supplied.','Exact5 unused unsafe/default metadata selection, put callback slot retained; independent scope review pending.'],
  'whole_SS_constructor_refinement':False,'source_sha256':{str(p.relative_to(ROOT)):sha(p)for p in files}}
 (HERE/'payload-report.json').write_text(json.dumps(report,indent=2)+'\n');print('8 kernel endpoints; actual BytesAdapter+Vec put append/empty/overflow passed without payload contract')
if __name__=='__main__':main()
