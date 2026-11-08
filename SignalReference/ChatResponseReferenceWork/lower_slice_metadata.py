#!/usr/bin/env python3
"""Typed candidate lowering of immutable &[u8] metadata to native slice length.
Only cached length queries change. No UTF8 loop/branch/byte computation is removed.
"""
import copy,hashlib,json,sys
from pathlib import Path
H=Path(__file__).resolve().parent
USIZE={'Untagged':{'Literal':{'UInt':'Usize'}}}
U8={'Untagged':{'Literal':{'UInt':'U8'}}}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def walk(x,path=()):
 yield path,x
 if isinstance(x,dict):
  for k,v in x.items():yield from walk(v,path+(k,))
 elif isinstance(x,list):
  for i,v in enumerate(x):yield from walk(v,path+(i,))
def at(x,path):
 for k in path:x=x[k]
 return x
def ident(f):
 n=f['item_meta']['name']
 return n[-1].get('Ident',[''])[0]
def root_local(place):
 k=place.get('kind',{})
 if 'Local' in k:return k['Local']
 if 'Projection' in k:return root_local(k['Projection'][0])
 return None
def shared_u8(place):
 t=place.get('ty',{}).get('Untagged',{}).get('Ref')
 return bool(t and len(t)==3 and t[2]=='Shared' and t[1]=={'Untagged':{'Slice':U8}})
def lower_function(original,helper_id,seed_call):
 f=copy.deepcopy(original)
 if f['body']=='Opaque':return f,[]
 body=f['body']['Structured'];replacements=[];base=None
 for path,node in list(walk(body['body'])):
  if not isinstance(node,dict) or 'kind' not in node or 'Projection' not in node['kind']:continue
  parent,projection=node['kind']['Projection']
  if projection!='PtrMetadata':continue
  assert node.get('ty')==USIZE,'metadata result must be usize'
  assert shared_u8(parent),'only shared &[u8] metadata is supported'
  assert 'Local' in parent['kind'],'only direct immutable input locals are supported'
  i=parent['kind']['Local'];assert 1<=i<=body['locals']['arg_count'],'metadata base must be an input'
  assert body['locals']['locals'][i]['ty']==parent['ty'],'input type mismatch'
  if base is None:base=parent
  assert base==parent,'multiple/different metadata bases are outside this rule'
  assert path and path[-1]=='Copy','metadata operand must be a Copy'
  replacements.append((path,copy.deepcopy(node)))
 if not replacements:return f,[]
 base_id=base['kind']['Local']
 for _,node in walk(body['body']):
  if not isinstance(node,dict):continue
  k=node.get('kind',{})
  if isinstance(k,dict) and 'Assign' in k:assert root_local(k['Assign'][0])!=base_id,'metadata input is assigned'
  if isinstance(k,dict) and 'Call' in k:assert root_local(k['Call']['call']['dest'])!=base_id,'metadata input is overwritten by a call'
 new_id=len(body['locals']['locals']);place={'kind':{'Local':new_id},'ty':USIZE}
 span=copy.deepcopy(original['item_meta']['span'])
 body['locals']['locals'].append({'index':new_id,'name':'chat_slice_metadata_length','span':span,'ty':USIZE})
 for path,_ in replacements:
  target=at(body['body'],path);target.clear();target.update(copy.deepcopy(place))
 entry=copy.deepcopy(seed_call)
 call=entry['kind']['Call']['call'];assert call['func']['Regular']['kind']=={'Fun':{'Regular':helper_id}}
 generics=call['func']['Regular']['generics']
 assert not generics['types'] and not generics['const_generics'] and not generics['trait_refs'] and len(generics['regions'])==1
 generics['regions']=[copy.deepcopy(base['ty']['Untagged']['Ref'][0])]
 call['args']=[{'Copy':copy.deepcopy(base)}];call['dest']=copy.deepcopy(place)
 ids=[n['id'] for _,n in walk(body['body']) if isinstance(n,dict) and 'id' in n and 'kind' in n and 'span' in n]
 entry['id']=max(ids,default=-1)+1;entry['span']=span
 body['body']['statements'].insert(0,entry)
 restored=copy.deepcopy(f);rb=restored['body']['Structured'];rb['body']['statements'].pop(0);rb['locals']['locals'].pop()
 for path,node in replacements:
  target=at(rb['body'],path);target.clear();target.update(node)
 assert restored==original,'non-reversible lowering'
 return f,[{'path':list(path),'original':node,'replacement':place} for path,node in replacements]
def main():
 profile=sys.argv[1];source=H/'Artifacts'/profile/'chat.llbc';before=json.loads(source.read_text());after=copy.deepcopy(before);tr=after['translated']
 helper=next(f for f in tr['fun_decls'] if f and ident(f)=='slice_metadata_len');assert helper['body']=='Opaque'
 seed=next(f for f in tr['fun_decls'] if f and ident(f)=='reference_length_seed')
 calls=[n for _,n in walk(seed['body']) if isinstance(n,dict) and isinstance(n.get('kind'),dict) and 'Call' in n['kind']]
 entry=next(n for n in calls if n['kind']['Call']['call']['func'].get('Regular',{}).get('kind')=={'Fun':{'Regular':helper['def_id']}})
 changes=[];negative=[]
 for i,f in enumerate(before['translated']['fun_decls']):
  if not f:continue
  try:new,delta=lower_function(f,helper['def_id'],entry)
  except AssertionError as e:
   if profile=='metadata_negative' and (ident(f).startswith('slice_metadata_negative_') or ident(f)=='len'):negative.append({'function':ident(f),'reason':str(e)});continue
   raise
  if delta:tr['fun_decls'][i]=new;changes.append({'function_id':i,'function':ident(f),'metadata_reads':delta})
 roots=[]
 if profile=='utf8':
  for f in tr['fun_decls']:
   if f and ident(f)=='run_utf8_validation':
    assert f['item_meta']['name'][:3]==[{'Ident':['core',0]},{'Ident':['str',0]},{'Ident':['validations',0]}]
    roots.append({'function_id':f['def_id'],'original_is_local':f['item_meta']['is_local']})
    f['item_meta']['is_local']=True
  assert len(roots)==1
 # The added helper calls introduce a dependency absent from original ordering.
 ordered=tr['ordered_decls'];helper_decl={'Fun':{'NonRec':helper['def_id']}}
 assert ordered.count(helper_decl)==1
 ordered.remove(helper_decl)
 target_ids={c['function_id'] for c in changes}
 first=next((i for i,d in enumerate(ordered) if isinstance(d.get('Fun'),dict) and d['Fun'].get('NonRec') in target_ids),len(ordered))
 ordered.insert(first,helper_decl)
 restored=copy.deepcopy(after)
 for change in changes:restored['translated']['fun_decls'][change['function_id']]=before['translated']['fun_decls'][change['function_id']]
 for root in roots:restored['translated']['fun_decls'][root['function_id']]['item_meta']['is_local']=root['original_is_local']
 restored['translated']['ordered_decls']=before['translated']['ordered_decls']
 assert restored==before,'unrecorded transformation'
 if profile=='metadata_negative':
  assert len(negative)==2 and all(c['function']=='reference_length_seed' for c in changes)
 else:assert changes,'no supported metadata reads found'
 dest=source.with_name('metadata-lowered.llbc')
 if not negative:dest.write_text(json.dumps(after,separators=(',',':'))+'\n')
 report={'candidate_only':True,'original_sha256':sha(source),'lowered_sha256':sha(dest) if not negative else None,'source_delta':changes,'retained_requested_extraction_roots':roots,'helper_dependency_order_restored':True,'negative_regressions':negative,'no_other_body_changes':True,'strict_rule':'Copy PtrMetadata of direct immutable input shared &[u8], result usize; all other types rejected','model_boundary':'Rust slice_metadata_len(input) =input.len(); concrete functional Aeneas Slice.len, not an assumed UTF8 predicate','script_sha256':sha(Path(__file__))}
 source.with_name('metadata-lowering.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'lowered_functions':len(changes),'lowered_reads':sum(len(c['metadata_reads']) for c in changes),'negative_regressions':negative}))
if __name__=='__main__':main()
