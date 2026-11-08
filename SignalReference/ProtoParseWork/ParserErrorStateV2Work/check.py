#!/usr/bin/env python3
from pathlib import Path
import importlib.util,os,subprocess,sys
H=Path(__file__).resolve().parent;I=H.parent/'DispatcherIntegrationWork';REF=H.parent.parent
ROOT=REF.parent
cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
paths=[ROOT/'.lake/build/lib/lean',H/'Build',ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']
paths += [p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths))
# Read-only dependency overlay. Changed numeric integration modules are recompiled
# under versioned module names; accepted unchanged primitive objects are reused.
for root in [I/'Build',H.parent/'BytesReferenceWork/Build']:
 for src in root.rglob('*.olean'):
  if 'TlsMpc' in src.relative_to(root).parts: continue
  target=H/'Build'/src.relative_to(root)
  if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(src.resolve())
for name in ['Replayed.FieldDispatch','Replayed.ContiguousReference','Replayed.NumericBridge','HistoricalV1']+(sys.argv[1:] or ['Initialization','FailureScan','LastByte','Regressions','CoreAudit']):
 module='ProtoParseWork.ParserErrorStateV2Work.'+name;src=H/Path(*name.split('.')).with_suffix('.lean');target=H/'Build'/Path(*module.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['lean','-o',str(target),str(src)],cwd=REF,env=env,check=True)
