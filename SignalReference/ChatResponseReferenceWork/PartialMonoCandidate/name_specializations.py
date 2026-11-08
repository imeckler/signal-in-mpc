#!/usr/bin/env python3
"""Deterministic LLBC declaration-name repair only, preserving every body/type."""
from pathlib import Path
import sys,json,hashlib,copy
source=Path(sys.argv[1]);output=Path(sys.argv[2]);d=json.loads(source.read_text());assert not d['has_errors'];x=d['translated'];before_all=copy.deepcopy(d);changes=[]
for field,kind in [('type_decls','Type'),('fun_decls','Fun'),('global_decls','Global'),('trait_decls','TraitDecl'),('trait_impls','TraitImpl')]:
 for item in x[field]:
  if item is None:continue
  old=item['item_meta']['name']
  if not any('Instantiated' in p for p in old):continue
  if [p['Ident'][0] for p in old if 'Ident' in p][:2]==['core','marker']:continue
  before=copy.deepcopy(item);idx=item['def_id'];new=[p for p in old if 'Instantiated' not in p]+[{'Ident':[f'partial_{kind}_{idx}',0]}]
  item['item_meta']['name']=new
  for entry in x['item_names']:
   if entry['key']=={kind:idx}:entry['value']=new
  item['item_meta']['name']=old;assert item==before;item['item_meta']['name']=new
  changes.append({'kind':kind,'id':idx,'original_name':old,'new_name':new})
for item in x['trait_impls']:
 if item is not None and not item['impl_trait']['generics']['types']:
  assert item['item_meta']['attr_info']['rename'] is None
  rename=f"reference_Impl_{item['def_id']}"
  item['item_meta']['attr_info']['rename']=rename
  changes.append({'kind':'TraitImplRename','id':item['def_id'],'rename':rename})
def semantic_view(value):
 value=copy.deepcopy(value);tr=value['translated'];tr['item_names']=[]
 for field in ['type_decls','fun_decls','global_decls','trait_decls','trait_impls']:
  for item in tr[field]:
   if item is not None:
    item['item_meta']['name']=[];item['item_meta']['attr_info']['rename']=None
 return value
assert semantic_view(d)==semantic_view(before_all)
output.write_text(json.dumps(d));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
output.with_suffix('.names.json').write_text(json.dumps({'scope':'Declaration names only; no computational/type/region changes','input_sha256':sha(source),'output_sha256':sha(output),'script_sha256':sha(Path(__file__)),'changes':changes},indent=2)+'\n')
