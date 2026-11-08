#!/usr/bin/env python3
import os,subprocess,sys,importlib.util
from pathlib import Path
HERE=Path(__file__).resolve().parent;REFERENCE=HERE.parent.parent
for script,probe in [('prepare_replay.py','FieldReplay/Types.lean'),('prepare_skip.py','SkipReplay/Types.lean')]:
 if not (HERE/probe).exists():subprocess.run([sys.executable,str(HERE/script)],check=True)
spec=importlib.util.spec_from_file_location('bytes_check',HERE.parent/'BytesReferenceWork/check.py');check=importlib.util.module_from_spec(spec);spec.loader.exec_module(check)
env=check.env();env['LEAN_PATH']=os.pathsep.join([str(HERE/'Build'),str(HERE.parent/'FieldReferenceWork/Build'),env['LEAN_PATH']])
# Unified read-only object overlay avoids Lean's first-prefix directory shadowing.
for root in [HERE.parent/'SkipTranslatorWork/Build',HERE.parent/'KeyReferenceWork/Build',HERE.parent/'FieldReferenceWork/Build',HERE.parent/'BytesReferenceWork/Build']:
 for src in root.rglob('*.olean'):
  dest=HERE/'Build'/src.relative_to(root)
  if not dest.exists():
   dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(src.resolve())
import json
replay=[x['module'] for x in json.loads((HERE/'replay.json').read_text())['modules']]
replay += [x['module'] for x in json.loads((HERE/'skip-replay.json').read_text())['modules']]
for name in replay+['Generated.TypesExternal','Generated.Types','Generated.FunsExternal','Generated.Funs']+(sys.argv[1:] or ['FieldDispatch','ContiguousReference','NumericBridge','RejectionMismatch']):
 module='ProtoParseWork.DispatcherIntegrationWork.'+name;target=HERE/'Build'/Path(*module.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 if name.startswith(('FieldReplay.','SkipReplay.')) and target.exists() and target.stat().st_mtime > (HERE/Path(*name.split('.')).with_suffix('.lean')).stat().st_mtime: continue
 subprocess.run(['lean','-o',str(target),str(HERE/Path(*name.split('.')).with_suffix('.lean'))],cwd=REFERENCE,env=env,check=True)
