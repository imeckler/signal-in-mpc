#!/usr/bin/env python3
"""Proof-erased name replay; deterministic full qualified instantiation hash."""
import copy,hashlib,json,pathlib,sys
source=pathlib.Path(sys.argv[1]);output=pathlib.Path(sys.argv[2]);original=json.loads(source.read_text());assert not original['has_errors'];named=copy.deepcopy(original);tr=named['translated'];changes=[];seen={}
for field,kind in [('type_decls','Type'),('fun_decls','Fun'),('global_decls','Global'),('trait_decls','TraitDecl'),('trait_impls','TraitImpl')]:
 for item in tr[field]:
  if item is None:continue
  old=item['item_meta']['name']
  if not any('Instantiated'in p for p in old):continue
  if[p['Ident'][0]for p in old if'Ident'in p][:2]==['core','marker']:continue
  digest=hashlib.sha256(json.dumps(old,sort_keys=True,separators=(',',':')).encode()).hexdigest();new=[p for p in old if'Instantiated'not in p]+[{'Ident':['specialized_'+kind+'_'+digest,0]}];key=json.dumps(new,sort_keys=True)
  assert key not in seen,(seen.get(key),(kind,item['def_id']));seen[key]=(kind,item['def_id']);item['item_meta']['name']=new
  for entry in tr['item_names']:
   if entry['key']=={kind:item['def_id']}:entry['value']=new
  changes.append(dict(field=field,kind=kind,id=item['def_id'],old=old,new=new))
def semantic(value):
 out=copy.deepcopy(value);out['translated']['item_names']=[]
 for field in ['type_decls','fun_decls','global_decls','trait_decls','trait_impls']:
  for item in out['translated'][field]:
   if item is not None:item['item_meta']['name']=[]
 return out
assert semantic(named)==semantic(original)
restored=copy.deepcopy(named)
for change in changes:
 restored['translated'][change['field']][change['id']]['item_meta']['name']=change['old']
 for entry in restored['translated']['item_names']:
  if entry['key']=={change['kind']:change['id']}:entry['value']=change['old']
assert restored==original
# Fail closed on any post-replay declaration-name collision, not probability.
for field in ['type_decls','fun_decls','global_decls','trait_decls','trait_impls']:
 names=[json.dumps(i['item_meta']['name'],sort_keys=True)for i in tr[field]if i is not None];assert len(names)==len(set(names)),field
output.write_text(json.dumps(named,separators=(',',':')));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();output.with_suffix('.names.json').write_text(json.dumps(dict(candidate_only=True,scope='declaration names/item-name lookup only; full qualified original name hash, no body/type/region/trait/rename-attribute changes',input_sha256=sha(source),output_sha256=sha(output),script_sha256=sha(pathlib.Path(__file__)),inverse_checked=True,semantic_json_equal=True,collision_checked=True,changes=changes),indent=2)+'\n')
