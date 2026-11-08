#!/usr/bin/env python3
"""Single-use safe-reference copy/reborrow normalization for actual Buf::advance.
Preserve every region table, reborrow kind, destination and pointer metadata.
Reject other temporary uses; never lower raw pointer copies or DropGuard copies.
"""
from pathlib import Path
import copy,json,hashlib,argparse
H=Path(__file__).resolve().parent;p=argparse.ArgumentParser();p.add_argument('--input',type=Path,default=H/'Artifacts/forward-actual.llbc');p.add_argument('--output',type=Path,default=H/'Artifacts/forward-actual-reborrow.llbc');a=p.parse_args();d=json.loads(a.input.read_text());assert not d['has_errors'];x=d['translated'];rewrites=[]
def local_uses(v,index):
 if isinstance(v,dict):return int(v.get('kind')=={'Local':index})+sum(local_uses(z,index) for z in v.values())
 if isinstance(v,list):return sum(local_uses(z,index) for z in v)
 return 0
def ident(f):return [z['Ident'][0] for z in f['item_meta']['name'] if 'Ident' in z]
for f in x['fun_decls']:
 if f is None or not isinstance(f['body'],dict):continue
 if ident(f)!=['bytes','buf','buf_impl','advance']:continue
 before=copy.deepcopy(f);body=f['body']['Structured'];assert len(f['signature']['inputs'])==2
 receiver=f['signature']['inputs'][0]['Untagged']['Ref'];assert receiver[2]=='Mut' and receiver[1]['Untagged']['Ref'][2]=='Mut'
 found=[]
 def walk(v):
  if isinstance(v,dict):
   statements=v.get('statements')
   if statements is not None:
    for i,statement in enumerate(statements):
     assign=statement['kind'].get('Assign') if isinstance(statement['kind'],dict) else None
     if assign is None:continue
     dest,rhs=assign
     use=rhs.get('Use')
     if use is None or 'Copy' not in use[0]:continue
     source=use[0]['Copy'];typ=dest['ty'].get('Untagged',{}).get('Ref')
     if typ is None or typ[2]!='Mut':continue
     assert use[1]=='No' and set(dest['kind'])=={'Local'}
     temp=dest['kind']['Local'];assert temp>body['locals']['arg_count']
     assert source['kind']['Projection'][1]=='Deref'
     assert source['kind']['Projection'][0]['kind']=={'Local':1}
     stype=source['ty']['Untagged']['Ref'];assert stype[2]=='Mut' and stype[1]==typ[1]
     j=i+1
     while j<len(statements) and isinstance(statements[j]['kind'],dict) and set(statements[j]['kind'])<= {'StorageLive','StorageDead'}:j+=1
     assert j<len(statements)
     reassign=statements[j]['kind']['Assign'];ref=reassign[1]['Ref'];place=ref['place'];assert ref['kind']=='TwoPhaseMut'
     assert place['kind']['Projection'][1]=='Deref' and place['kind']['Projection'][0]['kind']=={'Local':temp}
     assert place['ty']==typ[1] and local_uses(body,temp)==2
     old_ref=copy.deepcopy(ref);old_statement=copy.deepcopy(statement)
     ref['place']['kind']['Projection'][0]=copy.deepcopy(source)
     statement['kind']='Nop'
     assert ref['kind']==old_ref['kind'] and ref['ptr_metadata']==old_ref['ptr_metadata']
     found.append({'temp':temp,'copy':old_statement,'old_reborrow':old_ref,'new_reborrow':copy.deepcopy(ref)})
   for z in v.values():walk(z)
  elif isinstance(v,list):
   for z in v:walk(z)
 walk(body['body']);assert len(found)==1
 # The entire declaration is unchanged except the two exact statements above.
 assert f['generics']==before['generics'] and f['signature']==before['signature']
 assert body['bound_body_regions']==before['body']['Structured']['bound_body_regions']
 rewrites.append({'function_id':f['def_id'],'before_sha256':hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest(),'rewrite':found[0]})
assert len(rewrites)==1;a.output.write_text(json.dumps(d));sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
a.output.with_suffix('.rewrite.json').write_text(json.dumps({'candidate_only':True,'input_sha256':sha(a.input),'output_sha256':sha(a.output),'script_sha256':sha(Path(__file__)),'all_region_declarations_preserved':True,'scope':'Only actual mutable Buf::advance receiver temporary, with exactly one safe reborrow use and no other value use','rewrites':rewrites},indent=2)+'\n')
