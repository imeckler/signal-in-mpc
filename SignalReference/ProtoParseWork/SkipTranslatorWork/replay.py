#!/usr/bin/env python3
"""Replay accepted varint proofs into candidate skip namespace; no computational edits."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;KEY=HERE.parent/'KeyReferenceWork'
FILES=['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    a=(KEY/'Generated/key_step/Funs.lean').read_text().split('namespace ProstKeyCandidate\n',1)[1].split('\n/-- [prost::encoding::wire_type::',1)[0].strip()
    b=(HERE/'Trees/candidate/SkipTranslatorWork/Generated/skip/Funs.lean').read_text().split('namespace LoopSupportSkip\n',1)[1].split('\n/-- [prost::encoding::wire_type::',1)[0].strip()
    assert a==b,'Actual common varint computational bodies differ'
    rules={'LibSignalReference.Candidate.ProstKeySlice':'LibSignalReference.Candidate.ProstSkipSlice','LibSignalReference.Candidate.ProstKeyVarint':'LibSignalReference.Candidate.ProstSkipBuf','ProstKeySlice.':'ProstSkipSlice.','ProstKeyCandidate':'LoopSupportSkip','ProtoParseWork.KeyReferenceWork.Generated.key_step':'SkipTranslatorWork.Generated.skip','ProtoParseWork.KeyReferenceWork.Replayed':'SkipTranslatorWork.Replayed'}
    rules.update({'ProstKeyVarint.':'ProstSkipBuf.','LibSignalReference.Candidate.ProstKey':'LibSignalReference.Candidate.ProstSkipKey','ProtoParseWork.KeyReferenceWork.KeyValue':'SkipTranslatorWork.KeyValue'})
    files={}
    for name in FILES:
        src=KEY/'Replayed'/(name+'.lean');dest=HERE/'Modules/SkipTranslatorWork/Replayed'/(name+'.lean');text=src.read_text()
        for old,new in rules.items():text=text.replace(old,new)
        dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(text)
        files[name]={'source_sha256':digest(src),'destination_sha256':digest(dest)}
    original=(KEY/'Generated/key_step/Funs.lean').read_text().split('def encoding.decode_key',1)[1].split('\nend ProstKeyCandidate',1)[0].strip()
    candidate=(HERE/'Trees/candidate/SkipTranslatorWork/Generated/skip/Funs.lean').read_text().split('def encoding.decode_key',1)[1].split('/-- [prost::encoding::skip_field::',1)[0].strip()
    assert original==candidate,'Actual decode_key computational body differs'
    for name in ['KeyValue','KeyReference']:
        src=KEY/(name+'.lean');dest=HERE/'Modules/SkipTranslatorWork'/(name+'.lean');text=src.read_text()
        for old,new in rules.items():text=text.replace(old,new)
        dest.write_text(text);files[name]={'source_sha256':digest(src),'destination_sha256':digest(dest)}
    (HERE/'replay-report.json').write_text(json.dumps({'candidate_only':True,'actual_common_varint_bodies_identical':True,'generated_files_modified':False,'substitutions':rules,'files':files,'script_sha256':digest(Path(__file__))},indent=2)+'\n')
if __name__=='__main__':main()
