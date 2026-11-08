#!/usr/bin/env python3
"""Status propagation and canonical rejection of typed private TLS payloads."""
import hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
HERE=Path(__file__).resolve().parent;ART=ROOT/'.deps/relay-service-artifacts'
def main():
 cap=900;data=bytes(i%256 for i in range(cap));statuses=[0,1,254,255]
 for fixed in [False,True]:
  path=ART/('payload-fixed.json' if fixed else 'payload-after.json')
  with path.open('w') as out:subprocess.run(['lake','env','lean','--run',str(HERE/'GateExport.lean')]+(['fixed'] if fixed else [])+[str(cap)],cwd=ROOT,stdout=out,check=True)
  pairs=[(p,s) for p in statuses for s in statuses] if not fixed else [(s,s) for s in statuses]
  inputs=[bytes(([s] if fixed else [p,s]))+data for p,s in pairs]
  expected=[b'\xff'+cap.to_bytes(2,'big')+data if p==s==255 else bytes(cap+3) for p,s in pairs]
  assert evaluate_lanes(load(path),inputs)==expected
 files=[Path(__file__),HERE/'GateExport.lean',ROOT/'TlsMpc/Signal/ServicePayload.lean']
 report={'status_pair_cases':16,'fixed_cases':4,'capacity':cap,'output_bytes':cap+3,'canonical_rejection':True,
  'native_mpc_executed':False,'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 Path(__file__).with_name('payload-report.json').write_text(json.dumps(report,indent=2)+'\n');print('20 payload validity/length cases passed')
if __name__=='__main__':main()
