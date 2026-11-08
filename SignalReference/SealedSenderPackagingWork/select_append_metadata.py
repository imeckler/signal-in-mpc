#!/usr/bin/env python3
"""Exact unused unsafe/default dictionary metadata selection for append_to."""
import copy,hashlib,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(HERE.parent))
from MetadataWork.trim_step_metadata import reviewed_input_fingerprint
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def walk(x):
 yield x
 if isinstance(x,dict):
  for v in x.values():yield from walk(v)
 elif isinstance(x,list):
  for v in x:yield from walk(v)
def main():
 source=HERE/'Artifacts/PayloadAppend/ss_append.llbc';before=json.loads(source.read_text());after=copy.deepcopy(before);t=after['translated'];changes=[]
 # This exact extraction is pinned below; no arbitrary generalized trimming.
 expected='93c76ac520fcca2242161a5021f49fb2fd18bd07530a3bdba8b110ee5dcd9cbe';assert reviewed_input_fingerprint(before)==expected
 assert t['fun_decls'][0]['item_meta']['span']['data']['beg']['line']==681 and t['fun_decls'][0]['body']!='Opaque'
 def change(path,value):
  at=after
  for k in path[:-1]:at=at[k]
  changes.append({'path':path,'before':at[path[-1]],'after':value});at[path[-1]]=value
 for slot,name in [(0,'remaining_mut'),(1,'advance_mut'),(3,'chunk_mut')]:
  assert t['trait_decls'][3]['methods'][slot]['skip_binder']['name']==name
  change(['translated','trait_decls',3,'methods',slot],None)
 assert t['trait_decls'][3]['methods'][4]['skip_binder']['name']=='put'
 assert t['trait_decls'][3]['methods'][4]['skip_binder']['default']['id']==95 and t['fun_decls'][95]['body']=='Opaque'
 change(['translated','trait_decls',3,'methods',4,'skip_binder','default'],None)
 omitted=[{'Fun':{'NonRec':95}},{'Type':{'NonRec':11}}]
 change(['translated','ordered_decls'],[d for d in t['ordered_decls'] if d not in omitted])
 bodies=[]
 for i,f in enumerate(before['translated']['fun_decls']):
  if f and f['body']!='Opaque':
   assert t['fun_decls'][i]==f;bodies.append(i)
   for node in walk(f['body']):
    if isinstance(node,dict):
     assert node.get('Regular')!=95
     assert node.get('TraitMethod')not in [[3,0],[3,1],[3,3]]
     ref=node.get('Trait')
     if isinstance(ref,list)and len(ref)==2:
      assert (ref[0]['Untagged']['trait_decl_ref']['skip_binder']['id'],ref[1])not in [(3,0),(3,1),(3,3)]
 assert bodies==[0,1,2,3,139,140]
 restored=copy.deepcopy(after)
 for c in changes:
  at=restored
  for k in c['path'][:-1]:at=at[k]
  at[c['path'][-1]]=c['before']
 assert restored==before
 dest=HERE/'Artifacts/PayloadAppendSelected';dest.mkdir(exist_ok=True);selected=dest/'selected.llbc';selected.write_text(json.dumps(after,separators=(',',':'))+'\n');(dest/'changes.json').write_text(json.dumps(changes,indent=2)+'\n')
 gen=HERE/'Generated/PayloadAppendSelected';gen.mkdir(exist_ok=True)
 command=[str(ROOT/'.deps/aeneas-2026-08-27/aeneas'),'-backend','lean',str(selected),'-dest',str(HERE.parent),'-subdir','/SealedSenderPackagingWork/Generated/PayloadAppendSelected','-split-files','-namespace','SealedSenderAppend','-warnings-as-errors','-no-progress-bar']
 with(dest/'aeneas.log').open('w')as out:r=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 report={'candidate_only':True,'independent_review':'pending','source_sha256':sha(source),'normalized_input_fingerprint':expected,'selected_sha256':sha(selected),'changes_sha256':sha(dest/'changes.json'),'script_sha256':sha(Path(__file__)),'reversible_changes':5,'retained_computational_bodies_identical':bodies,'put_callback_slot_retained':4,'allocation_or_payload_implementation_replaced':False,'aeneas_exit_code':r.returncode,'generated_sha256':{str(p.relative_to(ROOT)):sha(p)for p in gen.glob('*.lean') if p.name not in ['FunsExternal.lean','TypesExternal.lean']}}
 (dest/'review.json').write_text(json.dumps(report,indent=2)+'\n');print('Append exact5 metadata selection exit',r.returncode)
if __name__=='__main__':main()
