#!/usr/bin/env python3
"""Deterministic proof/model namespace replay; generated computational bodies untouched."""
import hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent;FULL=PARENT/'FullReferenceWork';ROOT=PARENT.parent.parent
FILES=['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    frozen=json.loads((FULL/'proof-report.json').read_text())
    for name,sha in frozen['source_sha256'].items():assert digest(ROOT/name)==sha,name
    old=(PARENT/'Generated/varint_step/Types.lean').read_text().replace('ProstParserFullCandidate','ProstKeyCandidate')
    assert old==(HERE/'Generated/key_step/Types.lean').read_text()
    old=(PARENT/'Generated/varint_step/Funs.lean').read_text().split('namespace ProstParserFullCandidate\n',1)[1].rsplit('\nend ProstParserFullCandidate',1)[0].strip()
    new=(HERE/'Generated/key_step/Funs.lean').read_text().split('namespace ProstKeyCandidate\n',1)[1].split('\n/-- [prost::encoding::wire_type::',1)[0].strip()
    assert old==new
    common_body=old
    rules={'LibSignalReference.Candidate.ProstFullSlice':'LibSignalReference.Candidate.ProstKeySlice',
      'LibSignalReference.Candidate.ProstFull':'LibSignalReference.Candidate.ProstKeyVarint',
      'ProstFullSlice.':'ProstKeySlice.',
      'ProstParserFullCandidate':'ProstKeyCandidate',
      'ProtoParseWork.Generated.varint_step':'ProtoParseWork.KeyReferenceWork.Generated.key_step',
      'ProtoParseWork.FullReferenceWork':'ProtoParseWork.KeyReferenceWork.Replayed'}
    files={}
    srcs=[(FULL/(n+'.lean'),HERE/'Replayed'/(n+'.lean')) for n in FILES]
    srcs += [(FULL/'Modules/ProtoParseWork/Generated/varint_step/FunsExternal.lean',HERE/'Modules/ProtoParseWork/KeyReferenceWork/Generated/key_step/FunsExternal.lean')]
    for src,dest in srcs:
      s=src.read_text();counts={}
      for old,new in rules.items():counts[old]={'replacement':new,'count':s.count(old)};s=s.replace(old,new)
      dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(s)
      files[str(dest.relative_to(HERE))]={'original_sha256':digest(src),'replayed_sha256':digest(dest),'substitutions':counts}
    report={'candidate_only':True,'proof_and_external_models_only':True,'generated_files_modified':False,
      'generated_types_identical_modulo_namespace':True,'all_existing_generated_computational_bodies_identical':True,
      'common_generated_body_sha256':hashlib.sha256(common_body.encode()).hexdigest(),
      'full_wrapper_report_sha256':digest(FULL/'proof-report.json'),'files':files,'script_sha256':digest(Path(__file__))}
    (HERE/'replay-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
