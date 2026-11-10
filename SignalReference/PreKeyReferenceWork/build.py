#!/usr/bin/env python3
"""Offline isolated Lean checking; no Lake dependency resolution or source edits."""
import os, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
MODEL=ROOT/'.deps/aeneas-2026-08-27/backends/lean'
CACHE=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
BUILD=HERE/'Build/Lean'
paths=[BUILD,ROOT/'.lake/build/lib/lean',MODEL/'.lake/build/lib/lean',*[p/'.lake/build/lib/lean' for p in sorted(CACHE.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]]
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths))
modules=['Generated/ContentModels/TypesExternal','Generated/ContentModels/Types','Generated/ContentModels/FunsExternal','Generated/ContentModels/Funs','Proofs','Evaluate']
def main():
    for module in modules:
        output=BUILD/'PreKeyReferenceWork'/(module+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
        print('Checking '+module,flush=True)
        subprocess.run(['lean','-o',str(output),str(HERE/(module+'.lean'))],cwd=HERE.parent,env=env,check=True)

if __name__ == '__main__': main()
