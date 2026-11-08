#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,sys
H=Path(__file__).resolve().parent;REF=H.parent;ROOT=REF.parent;B=H/'Build';cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
paths=[REF/'ProtoParseWork/ModelCandidate/Build',ROOT/'.lake/build/lib/lean',B,REF/'ProtoParseWork/FullParserV3Work/Build',ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();OUT=Path(env.get('CHAT_RESPONSE_OUTPUT_ROOT',str(B))).resolve()
if OUT!=B:
 for src in list(B.rglob('*.olean')):
  dst=OUT/src.relative_to(B)
  if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve())
env['LEAN_PATH']=os.pathsep.join(map(str,([OUT] if OUT!=B else [])+paths))
for name in sys.argv[1:]:
 source=H/Path(*name.split('.')).with_suffix('.lean');module='ChatResponseReferenceWork.'+name;target=OUT/Path(*module.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 if OUT!=B and target.is_symlink():target.unlink()
 print('Checking',name,flush=True);subprocess.run(['lean','-o',str(target),str(source)],cwd=REF,env=env,check=True,timeout=120)
