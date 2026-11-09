#!/usr/bin/env python3
"""Pinned shared primitive types/content interpretation; computation unchanged."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();out=H/'Replayed';out.mkdir(exist_ok=True)
source=H/'Generated/Types.lean';text=source.read_text();head,body=text.split('\nnamespace ActualInnerResponseV1\n',1);body,tail=body.rsplit('\nend ActualInnerResponseV1',1)
aliases=['alloc.borrow.Cow','prost.encoding.wire_type.WireType','prost.error.DecodeErrorKind','prost.error.Inner','prost.error.DecodeError','prost.encoding.DecodeContext'];seen=[];parts=[]
for block in re.split(r'(?=^/--)',body,flags=re.M):
 m=re.search(r'^(?:inductive|structure|def) ([\w.]+)',block,re.M)
 if m and m.group(1) in aliases:
  name=m.group(1);seen.append(name);parts.append(f'\n/-- Identical pinned Rust primitive type. -/\nabbrev {name} := ActualResponseBytesV1.{name}\n')
  for ctor in re.findall(r'^\| (\w+)',block,re.M):parts.append(f'abbrev {name}.{ctor} := @ActualResponseBytesV1.{name}.{ctor}\n')
 else:parts.append(block)
assert set(seen)==set(aliases)
head=head.replace('import Aeneas','import ChatResponseReferenceWork.BytesContentV1.Replayed.Funs',1);head=re.sub(r'^import .*TypesExternal\n','',head,flags=re.M)
(out/'Types.lean').write_text(head+'\nnamespace ActualInnerResponseV1\nabbrev String := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8\n'+''.join(parts)+'\nend ActualInnerResponseV1'+tail)
funs=H/'Generated/Funs.lean';(out/'Funs.lean').write_text(funs.read_text().replace('InnerResponseV1.Generated','InnerResponseV1.Replayed'))
(H/'replay.json').write_text(json.dumps({'scope':'Identical pinned primitive type/constructor aliases, established String byte-content interpretation, and import paths only in computational Funs. No computational body edits.','script_sha256':sha(Path(__file__)),'original_types_sha256':sha(source),'original_funs_sha256':sha(funs),'replayed_types_sha256':sha(out/'Types.lean'),'replayed_funs_sha256':sha(out/'Funs.lean'),'aliases':seen},indent=2)+'\n')
