#!/usr/bin/env python3
"""Exact public AIG evaluation for the fixed c1 structural validator."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
from account_fixture import fixture
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes

def main():
 artifact=ROOT/'.deps/private-account-admission-native/v2-candidate-1/admit.json';data=fixture();cases=[]
 for name in ['initial','reserve','committed','second_reserve','second_commit']:cases.append((name,b''.join(data[name][:11]),255))
 base=bytearray(cases[2][1])
 for name,offset in [('identity',38),('global',103),('cursor',8298),('binding',8306),('device',8306+5619+602),('selected',8306+6230),('outbox',8306+7368),('disposition',8306+12575)]:
  bad=base.copy();bad[offset]=0 if name=='cursor' else bad[offset]^1;cases.append((name,bytes(bad),0))
 image=load(artifact);result=evaluate_lanes(image,[r for _,r,_ in cases]);assert result==[bytes([v])for _,_,v in cases],[(cases[i][0],r.hex())for i,r in enumerate(result)if r!=bytes([cases[i][2]])]
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 (HERE/'account-admission-artifact-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,cases=[dict(name=n,expected=v)for n,_,v in cases],conversations=1,logical_bytes=len(base),exact_AIG=True,private_native=False,semantic_bootstrap_validation=False,whole_account_activation=False,artifact_sha256=sha(artifact),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),HERE/'account_fixture.py',ROOT/'SignalReference/PrivateRecordWork/ExportAccount.lean']}),indent=2)+'\n');print('PASS: 13 exact account AIG cases')
if __name__=='__main__':main()
