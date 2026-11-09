#!/usr/bin/env python3
"""Immutable public AES cost exports; use a fresh stage for each replay."""
import importlib.util,subprocess,pathlib,time,json
root=pathlib.Path(__file__).resolve().parents[3];s=importlib.util.spec_from_file_location('b',root/'SignalReference/CtrReferenceV1Work/check_conversion.py');b=importlib.util.module_from_spec(s);s.loader.exec_module(b)
out=root/'.deps/reference-fixslice-cost-v1';out.mkdir(exist_ok=False)
for kind in ['candidate','reference']:
 for blocks,repeats in [(1,1),(4,1),(1,2),(4,2)]:
  label=f'{kind}-{blocks}x{repeats}';start=time.monotonic();print('START',label,flush=True)
  with (out/(label+'.json')).open('w') as f,(out/(label+'.log')).open('w')as log:
   r=subprocess.run(['lean','--run','AesCtrBlockWork/FixsliceCircuitV1Work/Export.lean',kind,str(blocks),str(repeats)],cwd=root/'SignalReference',env=b.environment,stdout=f,stderr=log,timeout=180)
  print('DONE',label,r.returncode,round(time.monotonic()-start,2),flush=True)
  if r.returncode:print((out/(label+'.json')).read_text()[:2000]);raise SystemExit(1)
