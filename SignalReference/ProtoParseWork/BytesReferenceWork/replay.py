#!/usr/bin/env python3
"""Replay accepted varint proofs; explicit new fifth Buf slot recorded separately."""
import hashlib,json,difflib
from pathlib import Path
HERE=Path(__file__).resolve().parent;FIELD=HERE.parent/'FieldReferenceWork'
FILES=['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 marker='/-- [prost::error::{impl core::convert::From<prost::error::DecodeErrorKind>'
 a=(FIELD/'Generated/uint32_step/Funs.lean').read_text().split(marker,1)[1].split('\n/-- [prost::encoding::wire_type::',1)[0].strip()
 b=(FIELD/'Generated/bytes_step/Funs.lean').read_text().split(marker,1)[1].split('\n/-- [prost::encoding::wire_type::',1)[0].strip()
 assert a==b,'Actual common varint computational bodies differ'
 rules={'LibSignalReference.Candidate.ProstFieldSlice':'LibSignalReference.Candidate.ProstBytesSlice','LibSignalReference.Candidate.ProstFieldBuf':'LibSignalReference.Candidate.ProstBytesBuf','ProstFieldSlice.':'ProstBytesSlice.','ProstFieldCandidate':'ProstBytesCandidate','ProtoParseWork.FieldReferenceWork.Generated.uint32_step':'ProtoParseWork.FieldReferenceWork.Generated.bytes_step','FieldReferenceWork.Replayed':'BytesReferenceWork.Replayed','ProstFieldBuf.':'ProstBytesBuf.'}
 files={}
 for name in FILES:
  src=FIELD/'Modules/FieldReferenceWork/Replayed'/(name+'.lean');dest=HERE/'Modules/BytesReferenceWork/Replayed'/(name+'.lean');text=src.read_text()
  for old,new in rules.items():text=text.replace(old,new)
  if name=='BufModel':
   before=text
   text=text.replace('/-- Exact four-slot byte-slice Buf instance; get_u8 is the pinned default body. -/','/-- Contiguous-slice Buf extended by the explicit bounded content-copy model. -/').replace('⟨remaining,chunk,advance,getByte⟩','⟨remaining,chunk,advance,getByte,ContentModel.copySlice⟩')
   assert text!=before
   (HERE/'buf-copy-slot.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),text.splitlines(True),fromfile='namespace-replay/BufModel.lean',tofile='candidate/BufModel.lean')))
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(text);files[name]={'source_sha256':digest(src),'destination_sha256':digest(dest)}
 (HERE/'replay-report.json').write_text(json.dumps({'candidate_only':True,'actual_common_varint_bodies_identical':True,'generated_files_modified':False,'substitutions':rules,'additional_model_delta':'buf-copy-slot.diff','files':files,'script_sha256':digest(Path(__file__))},indent=2)+'\n')
if __name__=='__main__':main()
