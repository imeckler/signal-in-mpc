#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;out=H/'Replayed';out.mkdir(exist_ok=True);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();files={}
for name in ['Types.lean','Funs.lean']:
 src=H/'Generated'/name;s=src.read_text().replace('BytesContentV1.Generated','BytesContentV1.Replayed')
 if name=='Types.lean':
  s=re.sub(r'discriminant (?:u8|isize), ','',s)
  s+='\ndef ActualResponseBytesV1.prost.encoding.wire_type.WireType.read_discriminant : ActualResponseBytesV1.prost.encoding.wire_type.WireType → Aeneas.Std.U8\n'
  for i,c in enumerate(['Varint','SixtyFourBit','LengthDelimited','StartGroup','EndGroup','ThirtyTwoBit']):s+=f'  | .{c} => {i}#u8\n'
  s+='instance responseBytesV1WireDiscriminant : Aeneas.Std.Discriminant ActualResponseBytesV1.prost.encoding.wire_type.WireType Aeneas.Std.U8 := ⟨ActualResponseBytesV1.prost.encoding.wire_type.WireType.read_discriminant⟩\n'
 (out/name).write_text(s);files[name]={'source_sha256':sha(src),'replayed_sha256':sha(out/name)}
(H/'replay.json').write_text(json.dumps({'scope':'Import paths; remove unused Cow/error discriminant attrs and unique identical wire instance. No computational-body edits.','files':files,'script_sha256':sha(Path(__file__))},indent=2)+'\n')
