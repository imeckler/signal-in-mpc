#!/usr/bin/env python3
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;S=H.parent/'SkipTranslatorWork'
items=[('Types',S/'Trees/candidate/SkipTranslatorWork/Generated/skip/Types.lean'),('FunsExternal',S/'Modules/SkipTranslatorWork/Generated/skip/FunsExternal.lean'),('Funs',S/'Trees/candidate/SkipTranslatorWork/Generated/skip/Funs.lean')]
report=[]
for name,src in items:
 before=src.read_text();s=before.replace('SkipTranslatorWork.Generated.skip','ProtoParseWork.DispatcherIntegrationWork.SkipReplay')
 if name=='Types':
  s=re.sub(r'discriminant (?:u8|isize), ','',s)
  s=re.sub(r'@\[discriminant (?:u8|isize)\]\n','',s)
  s+='\ndef LoopSupportSkip.encoding.wire_type.WireType.read_discriminant : LoopSupportSkip.encoding.wire_type.WireType → Aeneas.Std.U8\n'
  for i,c in enumerate(['Varint','SixtyFourBit','LengthDelimited','StartGroup','EndGroup','ThirtyTwoBit']):s+=f'  | .{c} => {i}#u8\n'
  s+='instance skipWireDiscriminant : Aeneas.Std.Discriminant LoopSupportSkip.encoding.wire_type.WireType Aeneas.Std.U8 := ⟨LoopSupportSkip.encoding.wire_type.WireType.read_discriminant⟩\n'
 target=H/'SkipReplay'/(name+'.lean');target.parent.mkdir(exist_ok=True);target.write_text(s)
 report.append({'module':'SkipReplay.'+name,'source':str(src),'source_sha256':hashlib.sha256(before.encode()).hexdigest(),'replayed_sha256':hashlib.sha256(s.encode()).hexdigest()})
(H/'skip-replay.json').write_text(json.dumps({'changes':'Import substitutions and explicit uniquely named equivalent wire discriminant instance; removed unused DecodeErrorKind discriminant attribute. Function computational bodies unchanged.','modules':report},indent=2)+'\n')
