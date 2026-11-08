#!/usr/bin/env python3
from pathlib import Path
import os,json,subprocess,sys
H=Path(__file__).resolve().parent;REF=H.parent.parent;ROOT=REF.parent;B=H/'Build'
cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
paths=[ROOT/'SignalReference/ProtoParseWork/ModelCandidate/Build',ROOT/'.lake/build/lib/lean',B,ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths))
for root in [H.parent/'DispatcherIntegrationWork/Build',H.parent/'ParserErrorStateV2Work/Build']:
 for src in root.rglob('*.olean'):
  if 'TlsMpc' in src.relative_to(root).parts:continue
  dst=B/src.relative_to(root)
  if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve())
names=['Skip.Replayed.'+n for n in ['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']]
names += ['Skip.'+n for n in ['KeyValue','KeyReference','SkipLeaf','SkipGroup','SkipSemantics']]
names += ['KeyCircuit','Table','DecoderTable']
if '--only' in sys.argv:names=[]
for name in names+[n for n in sys.argv[1:] if n not in ['--fresh','--only']]:
 source=H/Path(*name.split('.')).with_suffix('.lean');module='ProtoParseWork.FullParserV3Work.'+name;target=B/Path(*module.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 if name.startswith('Skip.') and '--fresh' not in sys.argv and target.exists() and target.stat().st_mtime>source.stat().st_mtime:continue
 print('Checking',name,flush=True);subprocess.run(['lean','-o',str(target),str(source)],cwd=REF,env=env,check=True)
