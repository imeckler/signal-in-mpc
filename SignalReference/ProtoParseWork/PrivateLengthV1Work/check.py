#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,sys
H=Path(__file__).resolve().parent;REF=H.parents[1];ROOT=REF.parent;B=H/'Build'
OUT=Path(os.environ.get('PRIVATE_PARSE_OUTPUT_ROOT',str(B))).resolve()
cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
for source in (ROOT/'.lake/build/lib/lean/TlsMpc').rglob('*.olean'):
 target=OUT/source.relative_to(ROOT/'.lake/build/lib/lean')
 if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(source.resolve())
accepted=REF/'ProtoParseWork/FullParserV3Work/Build'
for source in accepted.rglob('*.olean'):
 if 'TlsMpc' in source.relative_to(accepted).parts:continue
 target=OUT/source.relative_to(accepted)
 if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(source.resolve())
paths=[OUT,REF/'ProtoParseWork/ModelCandidate/Build',ROOT/'.lake/build/lib/lean',REF/'ProtoParseWork/FullParserV3Work/Build',ROOT/'.deps/aeneas-2026-08-27/backends/lean/.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths))
for name in sys.argv[1:]:
 module=name if name.startswith('TlsMpc.') else 'ProtoParseWork.PrivateLengthV1Work.'+name
 source=ROOT/Path(*module.split('.')).with_suffix('.lean') if name.startswith('TlsMpc.') else H/Path(*name.split('.')).with_suffix('.lean')
 target=OUT/Path(*module.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 if target.is_symlink():target.unlink()
 print('Checking',module,flush=True)
 subprocess.run(['lean','-o',str(target),str(source)],cwd=(ROOT if name.startswith('TlsMpc.') else REF),env=env,check=True,timeout=120)
