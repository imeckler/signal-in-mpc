#!/usr/bin/env python3
"""Retype true Rust immutable string literal constants at required static calls.
No borrow/dynamic string is promoted. Payload/body/region tables remain intact.
"""
from pathlib import Path
import json,sys,copy,hashlib
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ref_str(ty):
 try:
  region,inner,kind=ty['Untagged']['Ref']
  exact={'Untagged':{'Adt':{'id':{'Builtin':'Str'},'generics':{'regions':[],'types':[],'const_generics':[],'trait_refs':[]}}}}
  return (region,kind) if inner==exact else None
 except (KeyError,TypeError,ValueError):return None

def normalize(data):
 assert data['has_errors'] is False
 result=copy.deepcopy(data);decls=result['translated']['fun_decls'];changes=[]
 def walk(value,caller):
  if isinstance(value,dict):
   if 'Call' in value:
    call=value['Call']['call'];fn=call['func'].get('Regular',{}).get('kind',{}).get('Fun',{}).get('Regular')
    if fn is not None:
     callee=decls[fn];inputs=callee['signature']['inputs'];assert len(inputs)==len(call['args'])
     for i,(expected,arg) in enumerate(zip(inputs,call['args'])):
      if ref_str(expected)!=('Static','Shared'):continue
      # Already statically typed Globals/borrows remain untouched.
      if 'Const' not in arg:
       actual=next(iter(arg.values())).get('ty') if arg else None
       if actual is not None and ref_str(actual) not in [None,('Static','Shared')]:
        raise ValueError('borrowed/dynamic string cannot be promoted')
       continue
      const=arg['Const'].get('Untagged')
      if not isinstance(const,list) or len(const)!=2:raise ValueError('unsupported constant')
      payload,actual=const
      if actual==expected:continue
      if ref_str(actual) is None:raise ValueError('non-string pointer constant')
      region,kind=ref_str(actual)
      if kind!='Shared' or not isinstance(region,dict) or set(region)!= {'Body'}:raise ValueError('unsupported literal reference/region')
      if not isinstance(payload,dict) or set(payload)!= {'Literal'} or not isinstance(payload['Literal'],dict) or set(payload['Literal'])!= {'Str'} or not isinstance(payload['Literal']['Str'],str):raise ValueError('non-literal string constant')
      before=copy.deepcopy(actual);const[1]=copy.deepcopy(expected)
      changes.append({'caller':caller,'callee':fn,'argument':i,'literal':payload['Literal']['Str'],'old_type':before,'new_type':copy.deepcopy(expected)})
   for child in value.values():walk(child,caller)
  elif isinstance(value,list):
   for child in value:walk(child,caller)
 for f in decls:
  if f is not None:walk(f['body'],f['def_id'])
 # Only the recorded operand types may change; payloads and all region tables
 # are protected by replaying the exact edits backwards before comparison.
 restored=copy.deepcopy(result)
 count=0
 def undo(value):
  nonlocal count
  if isinstance(value,dict):
   if 'Call' in value:
    call=value['Call']['call'];fn=call['func'].get('Regular',{}).get('kind',{}).get('Fun',{}).get('Regular')
    for i,arg in enumerate(call['args']):
     if 'Const' not in arg:continue
     const=arg['Const'].get('Untagged')
     if not isinstance(const,list):continue
     for change in changes:
      if fn==change['callee'] and i==change['argument'] and const[0]=={'Literal':{'Str':change['literal']}} and const[1]==change['new_type']:
       const[1]=change['old_type'];count+=1;break
   for child in value.values():undo(child)
  elif isinstance(value,list):
   for child in value:undo(child)
 undo(restored)
 assert count==len(changes) and restored==data
 return result,changes
if __name__=='__main__':
 source,output=map(Path,sys.argv[1:]);data,changes=normalize(json.loads(source.read_text()));output.write_text(json.dumps(data));output.with_suffix('.static.json').write_text(json.dumps({'scope':'True Rust Literal::Str operand type only, immutable Body-region reference to callee-required static; all dynamic/borrowed/mutable/non-Str promotions reject. No computation or region-table edits.','input_sha256':sha(source),'output_sha256':sha(output),'script_sha256':sha(Path(__file__)),'changes':changes},indent=2)+'\n');print('static literal operand types normalized:',len(changes))
