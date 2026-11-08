#!/usr/bin/env python3
"""Narrow type-preserving specialization of mem::forget<DropGuard<'a>>.
Retain the actual no-op body; expose its concrete borrowed input to Aeneas.
Never erase a destructor, alter a branch, or specialize arbitrary callers.
"""
from pathlib import Path
import copy,hashlib,json,argparse
H=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--input',type=Path,default=H/'Artifacts/string_forget/chat.llbc');parser.add_argument('--output',type=Path,default=H/'Artifacts/string_forget/specialized.llbc');parser.add_argument('--receipt',type=Path,default=H/'forget-guard-specialization.json');args=parser.parse_args()
source=args.input;d=json.loads(source.read_text());x=d['translated']
name=lambda f:[p['Ident'][0] for p in f['item_meta']['name'] if 'Ident' in p]
funs=[f for f in x['fun_decls'] if f and name(f)==['core','mem','forget']];assert len(funs)==1
f=funs[0];fid=f['def_id'];guard=x['type_decls'][0]
assert name(guard)==['prost','encoding','string','merge','DropGuard']
assert len(guard['generics']['regions'])==1 and not guard['generics']['types']
calls=[]
def walk(v):
 if isinstance(v,dict):
  if 'Call' in v:
   c=v['Call']['call'];p=c['func'].get('Regular',{})
   if p.get('kind')=={'Fun':{'Regular':fid}}:calls.append(c)
  for a in v.values():walk(a)
 elif isinstance(v,list):
  for a in v:walk(a)
walk(x['fun_decls']);assert len(calls)==1
call=calls[0];g=call['func']['Regular']['generics'];assert not g['regions'] and len(g['types'])==1 and not g['trait_refs']
ty=g['types'][0];adt=ty['Untagged']['Adt'];assert adt['id']=={'Adt':0};actual=adt['generics'];assert len(actual['regions'])==1 and not actual['types'] and not actual['trait_refs']
assert not f['generics']['regions'] and len(f['generics']['types'])==1 and not f['generics']['trait_clauses'] and not f['generics']['const_generics']
assert f['signature']['output']=={'Untagged':{'Adt':{'id':{'Builtin':'Tuple'},'generics':{'regions':[],'types':[],'const_generics':[],'trait_refs':[]}}}}
assert f['signature']['inputs']==[{'Untagged':{'TypeVar':{'Free':0}}}]
body=f['body']['Structured'];assert body['locals']['arg_count']==1
assert [s['kind'] if isinstance(s['kind'],str) else next(iter(s['kind'])) for s in body['body']['statements']]==['StorageLive','Assign','StorageDead','Return']
original_body=copy.deepcopy(body['body']);original=copy.deepcopy(f)
special=copy.deepcopy(ty);special['Untagged']['Adt']['generics']['regions']=[{'Var':{'Free':0}}]
# Charon region generic references use Free rather than body-local region IDs.
f['generics']=copy.deepcopy(guard['generics']);f['signature']['inputs']=[special];body['locals']['locals'][1]['ty']=copy.deepcopy(special)
newname=[{'Ident':['prost',0]},{'Ident':['reference_forget_drop_guard',0]}];f['item_meta']['name']=newname
for entry in x['item_names']:
 if entry['key']=={'Fun':fid}:entry['value']=newname
call['func']['Regular']['generics']=copy.deepcopy(actual)
assert body['body']==original_body
out=args.output;out.write_text(json.dumps(d))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
args.receipt.write_text(json.dumps({'candidate_only':True,'input_sha256':sha(source),'output_sha256':sha(out),'script_sha256':sha(Path(__file__)),'function_id':fid,'call_count':len(calls),'original_function_sha256':hashlib.sha256(json.dumps(original,sort_keys=True).encode()).hexdigest(),'actual_body_unchanged':True,'scope':'Only actual mem::forget instantiated with Prost string DropGuard; expose existing mutable-borrow lifetime in function signature. No general destructor erasure.'},indent=2)+'\n')
print(out)
