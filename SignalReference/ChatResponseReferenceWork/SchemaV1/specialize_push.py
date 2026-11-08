#!/usr/bin/env python3
"""Specialize unchanged actual DecodeError.push at proven literal arguments."""
from pathlib import Path
import json,copy,hashlib,sys
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def string_ref(ty):
 try:
  region,inner,kind=ty['Untagged']['Ref']
  return (region,kind) if inner=={'Untagged':{'Adt':{'id':{'Builtin':'Str'},'generics':{'regions':[],'types':[],'const_generics':[],'trait_refs':[]}}}} else None
 except (KeyError,TypeError,ValueError):return None

def specialize(data):
 assert data['has_errors'] is False
 d=copy.deepcopy(data);x=d['translated'];decls=x['fun_decls'];templates=[f for f in decls if f and [p['Ident'][0] for p in f['item_meta']['name'] if 'Ident' in p]==['prost','error','push']]
 assert len(templates)==1
 template=templates[0];tid=template['def_id'];assert len(template['signature']['inputs'])==3
 assert all(string_ref(t)==('Static','Shared') for t in template['signature']['inputs'][1:])
 assert template['body']['Structured']['locals']['arg_count']==3
 changes=[];clones={}
 def literal(arg):
  if 'Const' in arg:
   payload,ty=arg['Const']['Untagged']
   assert string_ref(ty) is not None and string_ref(ty)[1]=='Shared','non-string/mutable literal'
   assert isinstance(payload,dict) and set(payload)=={'Literal'} and set(payload['Literal'])=={'Str'},'non-literal constant'
   value=payload['Literal']['Str'];assert isinstance(value,str)
   return value
  assert set(arg)=={'Copy'},'dynamic/borrowed string cannot specialize'
  place=arg['Copy'];assert set(place['kind'])=={'Global'},'dynamic/local string cannot specialize'
  ptr=place['kind']['Global'];assert ptr['generics']=={'regions':[],'types':[],'const_generics':[],'trait_refs':[]}
  glob=x['global_decls'][ptr['id']];assert glob['global_kind']=='NamedConst' and string_ref(glob['ty'])==('Static','Shared')
  expression,_=glob['value']['Untagged'];fn,args=expression['Call'];assert not args and set(fn['kind'])=={'Fun'}
  init=decls[fn['kind']['Fun']['Regular']];assert not init['signature']['inputs']
  statements=init['body']['Structured']['body']['statements'];assignments=[]
  for statement in statements:
   kind=statement['kind']
   if kind=='Return' or isinstance(kind,dict) and set(kind) in [{'StorageLive'},{'StorageDead'}]:continue
   assert isinstance(kind,dict) and set(kind)=={'Assign'},'nonliteral global initializer computation'
   place,rvalue=kind['Assign'];assert place['kind']=={'Local':0}
   assert set(rvalue)=={'Use'}
   operand,move=rvalue['Use'];assert move=='Yes';assignments.append(operand)
  assert len(assignments)==1
  return literal(assignments[0])
 def clone(pair):
  if pair in clones:return clones[pair]
  f=copy.deepcopy(template);fid=len(decls);f['def_id']=fid
  suffix=hashlib.sha256(json.dumps(pair).encode()).hexdigest()[:12]
  f['item_meta']['name'][-1]['Ident'][0]='push_literal_'+suffix
  f['signature']['inputs']=f['signature']['inputs'][:1]
  body=f['body']['Structured'];body['locals']['arg_count']=1
  # All original locals/regions/statements are kept. Former parameters become
  # locals initialized from the proven static literals before the actual body.
  ids=[]
  def statement_ids(v):
   if isinstance(v,dict):
    if 'id' in v and 'kind' in v:ids.append(v['id'])
    for a in v.values():statement_ids(a)
   elif isinstance(v,list):
    for a in v:statement_ids(a)
  statement_ids(body['body']);nextid=max(ids)+1;prefix=[]
  for local_id,text in zip([2,3],pair):
   ty=body['locals']['locals'][local_id]['ty'];assert string_ref(ty) is not None and string_ref(ty)[1]=='Shared'
   place={'kind':{'Local':local_id},'ty':copy.deepcopy(ty)}
   prefix.append({'span':copy.deepcopy(body['span']),'id':nextid,'kind':{'Assign':[place,{'Use':[{'Const':{'Untagged':[{'Literal':{'Str':text}},copy.deepcopy(ty)]}},'Yes']}]},'comments_before':[]});nextid+=1
  body['body']['statements']=prefix+body['body']['statements']
  # Verify actual body/region/local computational provenance exactly.
  restored=copy.deepcopy(f);restored['def_id']=tid;restored['item_meta']['name']=copy.deepcopy(template['item_meta']['name']);restored['signature']['inputs']=copy.deepcopy(template['signature']['inputs']);rb=restored['body']['Structured'];rb['locals']['arg_count']=3;rb['body']['statements']=rb['body']['statements'][2:];assert restored==template
  decls.append(f);x['item_names'].append({'key':{'Fun':fid},'value':copy.deepcopy(f['item_meta']['name'])});clones[pair]=fid
  return fid
 def walk(v,caller):
  if isinstance(v,dict):
   if 'Call' in v:
    c=v['Call']['call'];regular=c['func'].get('Regular')
    if regular and regular['kind']=={'Fun':{'Regular':tid}}:
     assert len(c['args'])==3
     pair=tuple(literal(a) for a in c['args'][1:]);fid=clone(pair)
     changes.append({'caller':caller,'original_callee':tid,'specialized_callee':fid,'literals':pair,'original_arguments':copy.deepcopy(c['args'])})
     regular['kind']['Fun']['Regular']=fid;c['args']=c['args'][:1]
   for a in list(v.values()):walk(a,caller)
  elif isinstance(v,list):
   for a in v:walk(a,caller)
 for f in list(decls):
  if f and f['def_id']!=tid:walk(f['body'],f['def_id'])
 assert changes,'no literal call sites'
 ordered=[];seen=0
 for group in x['ordered_decls']:
  if group=={'Fun':{'NonRec':tid}}:
   ordered.extend({'Fun':{'NonRec':fid}} for fid in clones.values());seen+=1
  else:ordered.append(group)
 assert seen==1,'recursive/missing push declaration group'
 x['ordered_decls']=ordered
 decls[tid]=None;x['item_names']=[n for n in x['item_names'] if n['key']!={'Fun':tid}]
 def check(v):
  if isinstance(v,dict):
   assert v!={'Fun':{'Regular':tid}},'unhandled native push reference'
   for a in v.values():check(a)
  elif isinstance(v,list):
   for a in v:check(a)
 check(d)
 return d,{'scope':'Actual unchanged DecodeError.push body specialized only at literal/static transparent literal constants. Self borrow and every region/local table retained. Native body restored byte-for-byte after stripping only two constant local initializers. Original removed only after all-reference check.','template_sha256':hashlib.sha256(json.dumps(template,sort_keys=True).encode()).hexdigest(),'changes':changes,'specialized_functions':list(clones.values())}
if __name__=='__main__':
 src,out=map(Path,sys.argv[1:]);data,report=specialize(json.loads(src.read_text()));out.write_text(json.dumps(data));report.update(input_sha256=sha(src),output_sha256=sha(out),script_sha256=sha(Path(__file__)));out.with_suffix('.push.json').write_text(json.dumps(report,indent=2)+'\n');print('actual push literal specializations:',len(report['specialized_functions']))
