#!/usr/bin/env python3
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
import replay
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent;REFERENCE=PARENT.parent;ROOT=REFERENCE.parent;FULL=PARENT/'FullReferenceWork';BUILD=HERE/'Build'
def env():
    frozen=json.loads((FULL/'proof-report.json').read_text())
    for name,sha in frozen['source_sha256'].items():assert replay.digest(ROOT/name)==sha,name
    cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
    paths=[PARENT/'ModelCandidate/Build',BUILD,FULL/'Build',PARENT/'BridgeBuild',ROOT/'.lake/build/lib/lean',REFERENCE/'.lake/build/lib/lean',*[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]]
    e=os.environ.copy();e['LEAN_PATH']=os.pathsep.join(map(str,paths));return e

def main():
    e=env()
    if len(sys.argv)>1:subprocess.run(['lean',*sys.argv[1:]],cwd=REFERENCE,env=e,check=True);return
    replay.main();shutil.copytree(FULL/'Build/ProtoParseWork',BUILD/'ProtoParseWork',dirs_exist_ok=True)
    if not (BUILD/'TlsMpc').exists():shutil.copytree(FULL/'Build/TlsMpc',BUILD/'TlsMpc')
    modules=[('ProtoParseWork.KeyReferenceWork.Generated.key_step.Types',HERE/'Generated/key_step/Types.lean',REFERENCE),
      ('ProtoParseWork.KeyReferenceWork.Generated.key_step.FunsExternal',HERE/'Modules/ProtoParseWork/KeyReferenceWork/Generated/key_step/FunsExternal.lean',HERE/'Modules'),
      ('ProtoParseWork.KeyReferenceWork.Generated.key_step.Funs',HERE/'Generated/key_step/Funs.lean',REFERENCE)]
    modules += [('ProtoParseWork.KeyReferenceWork.Replayed.'+n,HERE/'Replayed'/(n+'.lean'),REFERENCE) for n in replay.FILES]
    modules += [('ProtoParseWork.KeyReferenceWork.'+n,HERE/(n+'.lean'),REFERENCE) for n in ['KeyValue','KeyReference','KeyCircuit','PlanBridge','ArtifactBridge']]
    for module,source,cwd in modules:
      out=BUILD/(module.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
      print('Checking '+module,flush=True);subprocess.run(['lean','-o',str(out),str(source)],cwd=cwd,env=e,check=True)
if __name__=='__main__':main()
