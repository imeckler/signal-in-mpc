#!/usr/bin/env python3
"""Actual PublicKey raw-byte equality differential; normalization is deliberately absent."""
import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
BIN=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-point-equality-oracle'
def main():
 p=2**255-19;points=[]
 for n in list(range(20))+[p-1]+list(range(p,2**255)):
  for high in [0,2**255]:points.append((n+high).to_bytes(32,'little'))
 for i in range(128):points.append(hashlib.sha256(f'PUBLIC point{i}'.encode()).digest())
 rows=[];expected=[]
 for x in points:
  norm=((int.from_bytes(x,'little')%(2**255))%p).to_bytes(32,'little')
  for other in [x,norm,((int.from_bytes(x,'little')+1)%2**256).to_bytes(32,'little')]:
   rows.append(dict(left=x.hex(),right=other.hex()));expected.append(x==other)
 process=subprocess.run(['lake','env','lean','--run',str(HERE/'PointEvaluate.lean')],cwd=ROOT,input=''.join(json.dumps(list(bytes.fromhex(x['left']+x['right'])))+'\n'for x in rows),text=True,capture_output=True,check=True)
 outputs=[x[0]==255 for x in map(json.loads,process.stdout.splitlines())];assert outputs==expected
 process=subprocess.run([str(BIN)],input=''.join(json.dumps(x)+'\n'for x in rows),text=True,capture_output=True,check=True)
 assert [x['equal']for x in map(json.loads,process.stdout.splitlines())]==expected
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[Path(__file__),HERE/'PointEvaluate.lean',ROOT/'TlsMpc/Signal/PrivateSessionReceiveV1.lean',ROOT/'signal_backend/Oracle/src/bin/signal-point-equality-oracle.rs']
 report=dict(points=len(points),actual_pinned_PublicKey_equality_cases=len(rows),high_bit_and_modp_aliases_remain_distinct=True,all19_top_range_encodings=True,oracle_sha256=sha(BIN),full_point_equality_source_refinement_proved=False,whole_session_refinement=False,native_MPC_executed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'point-report.json').write_text(json.dumps(report,indent=2)+'\n');print(f'{len(points)} points/{len(rows)} actual raw PublicKey equality cases passed')
if __name__=='__main__':main()
