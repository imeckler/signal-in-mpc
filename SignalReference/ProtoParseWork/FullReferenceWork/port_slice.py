#!/usr/bin/env python3
"""Proof-only namespace replay to avoid generated global discriminant collisions.
Generated Rust computational definitions and frozen slice sources are untouched.
"""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent
EXPECTED={'SliceReference.lean':'3defdcaf00bad4a177e34903b85d56b1427d55336518b1c19bc3d43a4985d499','SliceBridge.lean':'dcc6f68988aeae1d803cbcb719c3afa3c07434243de31d7b7ca1ee487cf3fda1'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    old_fun=(PARENT/'Generated/slice/Funs.lean').read_text()
    new_fun=(PARENT/'Generated/varint_step/Funs.lean').read_text()
    marker='def encoding.varint.decode_varint_slice'
    original_body=old_fun[old_fun.index(marker):old_fun.index('\n\nend ProstParserReference')]
    selected_body=new_fun[new_fun.index(marker):new_fun.index('\n\n/-- [prost::encoding::varint::decode_varint]:')]
    assert original_body==selected_body
    changes={}
    for name,sha in EXPECTED.items():
        source=PARENT/name;assert digest(source)==sha
        text=source.read_text();substitutions={
          'LibSignalReference.Candidate.ProstSlice':'LibSignalReference.Candidate.ProstFullSlice',
          'ProstParserReference':'ProstParserFullCandidate',
          'import ProtoParseWork.Generated.slice.Funs':'import ProtoParseWork.Generated.varint_step.Funs',
          'import ProtoParseWork.SliceReference':'import ProtoParseWork.FullReferenceWork.SliceReference'}
        counts={}
        for old,new in substitutions.items():
            counts[old]={'replacement':new,'count':text.count(old)};text=text.replace(old,new)
        dest=HERE/name;dest.write_text(text)
        changes[name]={'frozen_source_sha256':sha,'replayed_source_sha256':digest(dest),'literal_substitutions':counts}
    report={'proof_only_replay':True,'generated_computational_definitions_modified':False,
      'reason':'Generated Types modules emit colliding global discriminant instance names, preventing simultaneous imports.',
      'slice_computational_body_exactly_identical':True,
      'slice_computational_body_sha256':hashlib.sha256(original_body.encode()).hexdigest(),
      'files':changes,'script_sha256':digest(Path(__file__))}
    (HERE/'slice-proof-replay.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
