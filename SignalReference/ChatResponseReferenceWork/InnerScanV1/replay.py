#!/usr/bin/env python3
"""Actual default Message merge/owned decode with shared primitive types."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parent;source=H.parent/'GeneratedOwnedDriver';out=H/'Replayed';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=(source/'Types.lean').read_text();head,body=s.split('\nnamespace ActualChatResponseOwned_driver\n',1);body,tail=body.rsplit('\nend ActualChatResponseOwned_driver',1);head=head.replace('import Aeneas','import ChatResponseReferenceWork.InnerResponseV1.Replayed.Types',1);head=re.sub(r'^import .*TypesExternal\n','',head,flags=re.M);parts=[];aliases=['prost.encoding.wire_type.WireType','prost.encoding.DecodeContext'];seen=[]
for block in re.split(r'(?=^/--)',body,flags=re.M):
 m=re.search(r'^structure ([\w.]+)|^inductive ([\w.]+)',block,re.M)
 name=next((v for v in m.groups() if v),None) if m else None
 if name in aliases:
  parts.append(f'\nabbrev {name} := ActualResponseBytesV1.{name}\n');seen.append(name)
  for ctor in re.findall(r'^\| (\w+)',block,re.M):parts.append(f'abbrev {name}.{ctor} := @ActualResponseBytesV1.{name}.{ctor}\n')
 else:parts.append(block)
assert set(seen)==set(aliases)
(out/'Types.lean').write_text(head+'\nnamespace ActualInnerScanV1\nabbrev prost.error.DecodeError := ActualResponseBytesV1.prost.error.DecodeError\n'+''.join(parts)+'\nend ActualInnerScanV1'+tail)
(out/'Funs.lean').write_text((source/'Funs.lean').read_text().replace('GeneratedOwnedDriver','InnerScanV1.Replayed').replace('ActualChatResponseOwned_driver','ActualInnerScanV1'))
(H/'replay.json').write_text(json.dumps({'scope':'Namespace/import replay; identical pinned primitive Wire/Context/Error type aliases. Actual default merge loop and transferred owned wrapper computational bodies unchanged.','script_sha256':sha(Path(__file__)),'original_sha256':{n:sha(source/n) for n in ['Types.lean','Funs.lean']},'replayed_sha256':{n:sha(out/n) for n in ['Types.lean','Funs.lean']}},indent=2)+'\n')
