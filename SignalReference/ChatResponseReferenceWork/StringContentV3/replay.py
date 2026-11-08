#!/usr/bin/env python3
"""Declaration selection/namespace replay, never computational-body correction."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parent;ROOT=H.parents[2];source=H.parent/'PartialMonoCandidate/GeneratedProst';out=H/'Generated';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={}
for name in ['Types.lean','Funs.lean']:
 s=(source/name).read_text();original=s
 if name=='Types.lean':
  s=re.sub(r'discriminant (?:u8|isize), ','',s)
  s=re.sub(r'@\[discriminant (?:u8|isize)\]\n','',s)
  s+='\ndef PartialMonoProst.encoding.wire_type.WireType.read_discriminant : PartialMonoProst.encoding.wire_type.WireType → Aeneas.Std.U8\n'
  for i,c in enumerate(['Varint','SixtyFourBit','LengthDelimited','StartGroup','EndGroup','ThirtyTwoBit']):s+=f'  | .{c} => {i}#u8\n'
  s+='instance stringV3WireDiscriminant : Aeneas.Std.Discriminant PartialMonoProst.encoding.wire_type.WireType Aeneas.Std.U8 := ⟨PartialMonoProst.encoding.wire_type.WireType.read_discriminant⟩\n'
 if name=='Funs.lean':
  # The emitted unused Drop dictionary has a raw/trait type mismatch. Keep the
  # actual standalone drop body; select out only its unreferenced dictionary.
  pattern=r'/-- Trait implementation: \[prost::encoding::string::merge::\{impl core::ops::drop::Drop::partial_TraitDecl_26.*?\ndef reference_Impl_0 :.*?\n}\n'
  s,n=re.subn(pattern,'',s,flags=re.S);assert n==1
  assert len(re.findall(r'\breference_Impl_0\b',s))==1 # standalone drop definition only
 s=s.replace('ChatResponseReferenceWork.PartialMonoCandidate.GeneratedProst','ChatResponseReferenceWork.StringContentV3.Generated').replace('PartialMonoProst','ActualStringContentV3')
 (out/name).write_text(s);files[name]={'original_sha256':sha(source/name),'replayed_sha256':sha(out/name)}
(H/'replay.json').write_text(json.dumps({'scope':'Unique wire discriminant instance (same mapping), remove unused error/Cow discriminant attributes; namespace/import replay and removal of unused erroneous Drop dictionary only. Standalone actual clear body retained. No generated computational body/type correction. String byte-content interpretation provided separately by external model; owned-error observation required.','files':files,'mixed_copier_checkpoint_commit':'aacda3d','script_sha256':sha(Path(__file__))},indent=2)+'\n')
