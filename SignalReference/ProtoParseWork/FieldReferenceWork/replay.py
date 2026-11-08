#!/usr/bin/env python3
"""Exact namespace/import replay of accepted varint proofs, with common-body check."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;KEY=HERE.parent/'KeyReferenceWork'
FILES=['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 a=(KEY/'Generated/key_step/Funs.lean').read_text().split('namespace ProstKeyCandidate\n',1)[1].split('\n/-- [prost::encoding::wire_type::',1)[0].strip()
 b=(HERE/'Generated/uint32_step/Funs.lean').read_text().split('namespace ProstFieldCandidate\n',1)[1].split('\n/-- [prost::encoding::wire_type::',1)[0].strip()
 assert a==b,'Actual common varint computational bodies differ'
 rules={'LibSignalReference.Candidate.ProstKeySlice':'LibSignalReference.Candidate.ProstFieldSlice','LibSignalReference.Candidate.ProstKeyVarint':'LibSignalReference.Candidate.ProstFieldBuf','ProstKeySlice.':'ProstFieldSlice.','ProstKeyCandidate':'ProstFieldCandidate','ProtoParseWork.KeyReferenceWork.Generated.key_step':'ProtoParseWork.FieldReferenceWork.Generated.uint32_step','ProtoParseWork.KeyReferenceWork.Replayed':'FieldReferenceWork.Replayed','ProstKeyVarint.':'ProstFieldBuf.'}
 files={}
 for name in FILES:
  src=KEY/'Replayed'/(name+'.lean');dest=HERE/'Modules/FieldReferenceWork/Replayed'/(name+'.lean');text=src.read_text()
  for old,new in rules.items():text=text.replace(old,new)
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(text);files[name]={'source_sha256':digest(src),'destination_sha256':digest(dest)}
 src=KEY/'Modules/ProtoParseWork/KeyReferenceWork/Generated/key_step/FunsExternal.lean';dest=HERE/'Modules/ProtoParseWork/FieldReferenceWork/Generated/uint32_step/FunsExternal.lean';text=src.read_text()
 for old,new in rules.items():text=text.replace(old,new)
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(text);files['External']={'source_sha256':digest(src),'destination_sha256':digest(dest)}
 (HERE/'replay-report.json').write_text(json.dumps({'candidate_only':True,'actual_common_varint_bodies_identical':True,'generated_files_modified':False,'substitutions':rules,'files':files,'script_sha256':digest(Path(__file__))},indent=2)+'\n')
if __name__=='__main__':main()
