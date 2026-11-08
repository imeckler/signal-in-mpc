#!/usr/bin/env python3
"""Replay accepted uint32 proofs; remove only colliding auto-generated attributes."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parent;F=H.parent/'FieldReferenceWork'
items=[('Types',F/'Generated/uint32_step/Types.lean'),('FunsExternal',F/'Modules/ProtoParseWork/FieldReferenceWork/Generated/uint32_step/FunsExternal.lean'),('Funs',F/'Generated/uint32_step/Funs.lean')]
items += [('Replayed.'+n,F/'Modules/FieldReferenceWork/Replayed'/(n+'.lean')) for n in ['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']]
items += [('Uint32Reference',F/'Modules/FieldReferenceWork/Uint32Reference.lean')]
report=[]
for name,src in items:
 s=src.read_text();old=s
 s=s.replace('ProtoParseWork.FieldReferenceWork.Generated.uint32_step','ProtoParseWork.DispatcherIntegrationWork.FieldReplay').replace('FieldReferenceWork.Replayed','ProtoParseWork.DispatcherIntegrationWork.FieldReplay.Replayed')
 if name=='Types':
  s=re.sub(r'discriminant (?:u8|isize), ','',s)
  s=re.sub(r'@\[discriminant (?:u8|isize)\]\n','',s)
  s+='\ndef ProstFieldCandidate.encoding.wire_type.WireType.read_discriminant : ProstFieldCandidate.encoding.wire_type.WireType → Aeneas.Std.U8\n'
  for i,c in enumerate(['Varint','SixtyFourBit','LengthDelimited','StartGroup','EndGroup','ThirtyTwoBit']):s+=f'  | .{c} => {i}#u8\n'
  s+='instance fieldWireDiscriminant : Aeneas.Std.Discriminant ProstFieldCandidate.encoding.wire_type.WireType Aeneas.Std.U8 := ⟨ProstFieldCandidate.encoding.wire_type.WireType.read_discriminant⟩\n'
 target=H/'FieldReplay'/Path(*name.split('.')).with_suffix('.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_text(s)
 report.append({'module':'FieldReplay.'+name,'source':str(src),'original_sha256':hashlib.sha256(old.encode()).hexdigest(),'replayed_sha256':hashlib.sha256(s.encode()).hexdigest()})
(H/'replay.json').write_text(json.dumps({'changes':'Import paths only, remove unused Cow/error-kind discriminant attributes, and spell the identical wire discriminant mapping with a unique instance name to avoid global collisions. Parser computational declarations unchanged.','modules':report},indent=2)+'\n')
