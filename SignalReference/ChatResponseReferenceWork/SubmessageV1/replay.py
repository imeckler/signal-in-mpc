#!/usr/bin/env python3
"""Exact body replay plus guarded borrowed-triple trait type specialization."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;out=H/'Replayed';out.mkdir(exist_ok=True);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=(H/'Generated/Types.lean').read_text();head,body=s.split('\nnamespace ActualSubmessageV1\n',1);body,tail=body.rsplit('\nend ActualSubmessageV1',1)
aliases={'alloc.borrow.Cow':'ActualResponseBytesV1','prost.encoding.wire_type.WireType':'ActualResponseBytesV1','prost.error.DecodeErrorKind':'ActualResponseBytesV1','prost.error.Inner':'ActualResponseBytesV1','prost.error.DecodeError':'ActualResponseBytesV1','prost.encoding.DecodeContext':'ActualResponseBytesV1','bytes.buf.buf_impl.Buf':'ActualInnerResponseV1','bytes.buf.buf_mut.BufMut':'ActualInnerScanV1'}
seen=[];parts=[]
for block in re.split(r'(?=^/--)',body,flags=re.M):
 m=re.search(r'^(?:inductive|structure|def) ([\w.]+)',block,re.M)
 if m and m.group(1) in aliases:
  name=m.group(1);seen.append(name);ns=aliases[name];parts.append(f'\nabbrev {name} := {ns}.{name}\n')
  for ctor in re.findall(r'^\| (\w+)',block,re.M):parts.append(f'abbrev {name}.{ctor} := @{ns}.{name}.{ctor}\n')
 else:parts.append(block)
assert set(seen)==set(aliases)
head=head.replace('import Aeneas','import ChatResponseReferenceWork.InnerScanV1.DriverReference',1);head=re.sub(r'^import .*TypesExternal\n','',head,flags=re.M)
(out/'Types.lean').write_text(head+'\nnamespace ActualSubmessageV1\n'+''.join(parts)+'\nend ActualSubmessageV1'+tail)
s=(H/'Generated/Funs.lean').read_text().replace('import Generated.Types','import ChatResponseReferenceWork.SubmessageV1.Replayed.Types').replace('import Generated.FunsExternal','import ChatResponseReferenceWork.SubmessageV1.Replayed.FunsExternal')
start=s.index('/-- [prost::encoding::message::merge::{impl core::ops::function::FnMut')
end=s.index('/-- [prost::encoding::message::merge::{impl core::ops::function::FnOnce',start)
raw=s[start:end];header=s[:s.index('namespace ActualSubmessageV1')]
(out/'Raw.lean').write_text(header+'namespace ActualSubmessageV1.Raw\n'+raw+'\nend ActualSubmessageV1.Raw\n')
s=s[:start]+s[end:]
s=s.replace('import ChatResponseReferenceWork.SubmessageV1.Replayed.FunsExternal','import ChatResponseReferenceWork.SubmessageV1.ActualProjection')
def expression(text,pos):
 while text[pos].isspace():pos+=1
 start=pos
 if text[pos]=='(':
  depth=1;pos+=1
  while depth:
   depth+=(text[pos]=='(')-(text[pos]==')');pos+=1
 else:
  while pos<len(text) and not text[pos].isspace():pos+=1
 return text[start:pos],pos
def triple(args):
 assert args.startswith('(') and args.endswith(')');args=args[1:-1];depth=0;parts=[];start=0
 for i,c in enumerate(args):
  depth+=(c=='(')-(c==')')
  if c=='×' and depth==0:parts.append(args[start:i].strip());start=i+1
 parts.append(args[start:].strip());assert len(parts)==3,parts
 assert parts[2]=='prost.encoding.DecodeContext',parts
 return parts
counts={}
for trait,expected in [('FnOnce',1),('FnMut',4)]:
 pattern='core.ops.function.'+trait+' ';position=0;count=0
 while (at:=s.find(pattern,position))>=0:
  self,end=expression(s,at+len(pattern));args,end=expression(s,end);output,end=expression(s,end)
  left,right,context=triple(args)
  replacement=f'ChatResponseReference.FnMutBorrowV1.Borrow{trait} {self} {left} {right} {context} {output}'
  s=s[:at]+replacement+s[end:];position=at+len(replacement);count+=1
 assert count==expected,(trait,count);counts[trait]=count
(out/'Funs.lean').write_text(s)
(H/'replay.json').write_text(json.dumps({'candidate_only':True,'scope':'Identical pinned primitive aliases; borrowed-triple FnOnce/FnMut type annotations specialized; actual raw closure helper namespace split, tagged raw/trait projection; computational bodies otherwise unchanged.','typed_annotations':counts,'script_sha256':sha(Path(__file__)),'generated_sha256':{p.name:sha(p) for p in (H/'Generated').glob('*.lean')},'replayed_sha256':{p.name:sha(p) for p in out.glob('*.lean')}},indent=2)+'\n')
