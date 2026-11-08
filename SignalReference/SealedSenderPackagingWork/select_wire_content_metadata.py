#!/usr/bin/env python3
"""Compose exact Step and unused unsafe/default selections for USMC encoding."""
import copy,hashlib,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def walk(x):
 yield x
 if isinstance(x,dict):
  for v in x.values():yield from walk(v)
 elif isinstance(x,list):
  for v in x:yield from walk(v)
def main():
 original=HERE/'Artifacts/WireFields/ss_content.llbc';prior=HERE/'Artifacts/WireFieldsSelected/selected.llbc'
 before=json.loads(original.read_text());after=json.loads(prior.read_text());changes=json.loads((prior.parent/'changes.json').read_text());assert len(changes)==7
 def change(path,value):
  at=after
  for k in path[:-1]:at=at[k]
  changes.append({'path':path,'before':at[path[-1]],'after':value});at[path[-1]]=value
 t=after['translated']
 for slot,name in [(0,'remaining_mut'),(1,'advance_mut'),(3,'chunk_mut')]:
  assert t['trait_decls'][3]['methods'][slot]['skip_binder']['name']==name;change(['translated','trait_decls',3,'methods',slot],None)
 for slot,fid,name in [(4,15,'put'),(5,16,'put_slice')]:
  m=t['trait_decls'][3]['methods'][slot]['skip_binder'];assert m['name']==name and m['default']['id']==fid and t['fun_decls'][fid]['body']=='Opaque'
  change(['translated','trait_decls',3,'methods',slot,'skip_binder','default'],None)
 omitted=[{'Fun':{'NonRec':15}},{'Fun':{'NonRec':16}},{'Type':{'NonRec':13}}]
 change(['translated','ordered_decls'],[d for d in t['ordered_decls']if d not in omitted])
 bodies=[]
 for i,f in enumerate(before['translated']['fun_decls']):
  if f and f['body']!='Opaque':
   assert t['fun_decls'][i]==f;bodies.append(i)
   for node in walk(f['body']):
    if isinstance(node,dict):
     assert node.get('Regular')not in[15,16,296,300]
     assert node.get('TraitMethod')not in[[3,0],[3,1],[3,3],[12,2],[12,6]]
     ref=node.get('Trait')
     if isinstance(ref,list)and len(ref)==2:assert(ref[0]['Untagged']['trait_decl_ref']['skip_binder']['id'],ref[1])not in[(3,0),(3,1),(3,3),(12,2),(12,6)]
 restored=copy.deepcopy(after)
 for c in reversed(changes):
  at=restored
  for k in c['path'][:-1]:at=at[k]
  at[c['path'][-1]]=c['before']
 assert restored==before and len(changes)==13
 dest=HERE/'Artifacts/WireContent';dest.mkdir(exist_ok=True);selected=dest/'selected.llbc';selected.write_text(json.dumps(after,separators=(',',':'))+'\n');(dest/'changes.json').write_text(json.dumps(changes,indent=2)+'\n')
 gen=HERE/'Generated/WireContent';gen.mkdir(exist_ok=True)
 command=[str(ROOT/'.deps/aeneas-2026-08-27/aeneas'),'-backend','lean',str(selected),'-dest',str(HERE.parent),'-subdir','/SealedSenderPackagingWork/Generated/WireContent','-split-files','-namespace','SealedSenderPackaging','-warnings-as-errors','-no-progress-bar']
 with(dest/'aeneas.log').open('w')as out:r=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 report={'candidate_only':True,'independent_review':'pending','original_sha256':sha(original),'selected_sha256':sha(selected),'changes_sha256':sha(dest/'changes.json'),'script_sha256':sha(Path(__file__)),'reversible_changes':13,'retained_computational_bodies_identical':bodies,'retained_put_put_slice_put_u8_slots':[4,5,7],'aeneas_exit_code':r.returncode,'generated_sha256':{str(p.relative_to(ROOT)):sha(p)for p in gen.glob('*.lean')if p.name not in['FunsExternal.lean','TypesExternal.lean']}}
 (dest/'review.json').write_text(json.dumps(report,indent=2)+'\n');print('Actual USMC content exact13 metadata selection exit',r.returncode)
if __name__=='__main__':main()
