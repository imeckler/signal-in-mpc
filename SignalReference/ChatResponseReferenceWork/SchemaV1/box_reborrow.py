#!/usr/bin/env python3
"""One-use compiler Box place alias → the same direct mutable reborrow."""
from pathlib import Path
import copy,json,hashlib,sys
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def normalize(data):
 d=copy.deepcopy(data);changes=[]
 for f in d['translated']['fun_decls']:
  if f is None or not any('Ident' in p and p['Ident'][0].startswith('push_literal_') for p in f['item_meta']['name']):continue
  body=f['body']['Structured'];statements=body['body']['statements'];candidates=[]
  for i,statement in enumerate(statements):
   try:
    dest,rv=statement['kind']['Assign'];operand,flag=rv['Use'];src=operand['Copy'];temp=dest['kind']['Local']
    box=src['ty']['Untagged']['Adt'];assert box['id']=={'Builtin':'Box'} and len(box['generics']['types'])==1
   except (KeyError,TypeError,ValueError,AssertionError):continue
   assert flag=='No' and dest['ty']==src['ty'],'unsupported owning Box copy'
   # Require precisely ((*self).inner): a safe mutable receiver field, no raw
   # pointer access and no general Box copy interpretation.
   parent,field=src['kind']['Projection'];receiver,deref=parent['kind']['Projection']
   assert field=={'Field':[None,0]} and deref=='Deref' and receiver['kind']=={'Local':1}
   assert receiver['ty']['Untagged']['Ref'][2]=='Mut'
   occurrences=[]
   def count(v):
    if isinstance(v,dict):
     if v.get('kind')=={'Local':temp}:occurrences.append(v)
     for a in v.values():count(a)
    elif isinstance(v,list):
     for a in v:count(a)
   count(body['body']);assert len(occurrences)==2,'Box alias has extra uses'
   j=i+1
   while j<len(statements) and isinstance(statements[j]['kind'],dict) and set(statements[j]['kind'])=={'StorageLive'}:j+=1
   consumer=statements[j];_,rvalue=consumer['kind']['Assign'];borrow=rvalue['Ref'];assert borrow['kind'] in ['Mut','TwoPhaseMut']
   oldplace=copy.deepcopy(borrow['place']);replaced=0
   def substitute(v):
    nonlocal replaced
    if isinstance(v,dict):
     if v.get('kind')=={'Local':temp}:
      assert v['ty']==src['ty'];v.clear();v.update(copy.deepcopy(src));replaced+=1;return
     for a in list(v.values()):substitute(a)
    elif isinstance(v,list):
     for a in v:substitute(a)
   substitute(borrow['place']);assert replaced==1
   removed=statements.pop(i)
   # Restore exactly before recording: only this compiler place alias changes.
   restored=copy.deepcopy(f);rs=restored['body']['Structured']['body']['statements'];rs.insert(i,copy.deepcopy(removed));rs[j]['kind']['Assign'][1]['Ref']['place']=oldplace
   original=data['translated']['fun_decls'][f['def_id']];assert restored==original
   changes.append({'function':f['def_id'],'temporary':temp,'removed_statement':removed['id'],'reborrow_statement':consumer['id'],'original_place':oldplace,'direct_place':copy.deepcopy(borrow['place'])})
   break
 assert changes,'no one-use Box aliases found'
 return d,changes
if __name__=='__main__':
 src,out=map(Path,sys.argv[1:]);data,changes=normalize(json.loads(src.read_text()));out.write_text(json.dumps(data));out.with_suffix('.box.json').write_text(json.dumps({'scope':'Safe receiver Box field place alias, Copy/No with exactly one immediate mutable reborrow; no actual Box clone/ownership operation. All region tables and heap mutation preserved.','input_sha256':sha(src),'output_sha256':sha(out),'script_sha256':sha(Path(__file__)),'changes':changes},indent=2)+'\n');print('direct Box reborrows:',len(changes))
