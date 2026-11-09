#!/usr/bin/env python3
"""Share identical pinned primitive types; retain every computational body."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();out=H/'Replayed';out.mkdir(exist_ok=True)
source=H/'Generated/Types.lean';text=source.read_text();head,body=text.split('\nnamespace ActualRepeatedStringV1\n',1);body,tail=body.rsplit('\nend ActualRepeatedStringV1',1)
aliases=['alloc.borrow.Cow','encoding.wire_type.WireType','error.DecodeErrorKind','error.Inner','error.DecodeError','encoding.DecodeContext'];seen=[];parts=[]
for block in re.split(r'(?=^/--)',body,flags=re.M):
 m=re.search(r'^(?:inductive|structure|def) ([\w.]+)',block,re.M)
 if m and m.group(1) in aliases:
  name=m.group(1);seen.append(name);parts.append(f'\n/-- Same pinned Rust type as the proved String primitive. -/\nabbrev {name} := ActualStringContentV3.{name}\n')
  for ctor in re.findall(r'^\| (\w+)',block,re.M):parts.append(f'abbrev {name}.{ctor} := @ActualStringContentV3.{name}.{ctor}\n')
 else:parts.append(block)
assert set(seen)==set(aliases)
head=head.replace('import Aeneas','import ChatResponseReferenceWork.StringContentV3.Generated.Funs',1)
(out/'Types.lean').write_text(head+'\nnamespace ActualRepeatedStringV1\nabbrev String := ActualStringContentV3.String\n'+''.join(parts)+'\nend ActualRepeatedStringV1'+tail)
funs=H/'Generated/Funs.lean';(out/'Funs.lean').write_text(funs.read_text().replace('RepeatedStringV1.Generated','RepeatedStringV1.Replayed'))
(H/'replay.json').write_text(json.dumps({'scope':'Primitive type aliases to identical pinned String extraction types plus established byte-content String interpretation; import paths only in Funs, no computational-body edits.','script_sha256':sha(Path(__file__)),'original_types_sha256':sha(source),'original_funs_sha256':sha(funs),'replayed_types_sha256':sha(out/'Types.lean'),'replayed_funs_sha256':sha(out/'Funs.lean'),'aliases':seen},indent=2)+'\n')
