#!/usr/bin/env python3
"""Isolated candidate full-wrapper reference build. No frozen inputs modified."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent;REFERENCE=PARENT.parent;ROOT=REFERENCE.parent
BUILD=HERE/'Build'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def env():
    assert digest(PARENT/'SliceReference.lean')=='3defdcaf00bad4a177e34903b85d56b1427d55336518b1c19bc3d43a4985d499'
    assert digest(PARENT/'SliceBridge.lean')=='dcc6f68988aeae1d803cbcb719c3afa3c07434243de31d7b7ca1ee487cf3fda1'
    frozen=json.loads((PARENT/'bridge-proof-report.json').read_text())
    for name,sha in frozen['source_sha256'].items():assert digest(ROOT/name)==sha,name
    cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
    paths=[PARENT/'ModelCandidate/Build',BUILD,PARENT/'BridgeBuild',ROOT/'.lake/build/lib/lean',REFERENCE/'.lake/build/lib/lean',*[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]]
    e=os.environ.copy();e['LEAN_PATH']=os.pathsep.join(map(str,paths));return e

def main():
    e=env()
    if len(sys.argv)>1:
        subprocess.run(['lean',*sys.argv[1:]],cwd=REFERENCE,env=e,check=True);return
    shutil.copytree(PARENT/'BridgeBuild/ProtoParseWork',BUILD/'ProtoParseWork',dirs_exist_ok=True)
    modules=[('ProtoParseWork.Generated.varint_step.Types',PARENT/'Generated/varint_step/Types.lean',REFERENCE),
      ('ProtoParseWork.Generated.varint_step.FunsExternal',HERE/'Modules/ProtoParseWork/Generated/varint_step/FunsExternal.lean',HERE/'Modules'),
      ('ProtoParseWork.Generated.varint_step.Funs',PARENT/'Generated/varint_step/Funs.lean',REFERENCE),
      ('ProtoParseWork.FullReferenceWork.BufModel',HERE/'BufModel.lean',REFERENCE),
      ('ProtoParseWork.FullReferenceWork.SliceReference',HERE/'SliceReference.lean',REFERENCE),
      ('ProtoParseWork.FullReferenceWork.SliceBridge',HERE/'SliceBridge.lean',REFERENCE),
      ('ProtoParseWork.FullReferenceWork.SliceAdapter',HERE/'SliceAdapter.lean',REFERENCE),
      *[('ProtoParseWork.FullReferenceWork.'+name,HERE/(name+'.lean'),REFERENCE) for name in
        ['SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']]]
    for module,source,cwd in modules:
        out=BUILD/(module.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
        print('Checking '+module,flush=True)
        subprocess.run(['lean','-o',str(out),str(source)],cwd=cwd,env=e,check=True)
if __name__=='__main__':main()
