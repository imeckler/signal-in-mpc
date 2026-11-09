#!/usr/bin/env python3
"""Public structural shard cases; no fresh-account activation claim."""
import hashlib,json,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(HERE.parent))
from account_fixture import fixture
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes

def main():
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'ValidationAudit.lean')],cwd=ROOT,text=True);groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==5
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in audit
 data=fixture();global_raw=b''.join(data['committed'][:4]);cases=[('valid',global_raw,b'\xff')]
 for offset in [70,103,8298]:
  bad=bytearray(global_raw);bad[offset]=0;cases.append(('global-reject-'+str(offset),bytes(bad),b'\0'))
 total=0;stage=ROOT/'.deps/private-shard-validation-native/v1-candidate-3'
 image=load(stage/'outbox-global.json');assert evaluate_lanes(image,[r for _,r,_ in cases])==[v for _,_,v in cases];total+=len(cases)
 cases=[]
 for slot in range(2):
  fields=data['committed'][4+7*slot:11+7*slot];queue=fields[5];expanded=b''.join(queue[i*1302:(i+1)*1302]+((i+1).to_bytes(8,'big')if queue[i*1302]else bytes(8))for i in range(4));conv=b''.join(fields[:5])+expanded+fields[6];assert len(conv)==12611
  raw=global_raw+conv;cases.append(('valid-'+str(slot),raw,b'\xff'))
  for offset in [8306+69,8306+7367+1302+7,8306+7367+1310+1302,8306+12607,70]:
   bad=bytearray(raw);bad[offset]=bad[offset]^1;cases.append(('changed-reject-'+str(slot)+'-'+str(offset),bytes(bad),b'\0'))
 image=load(stage/'outbox-conversation.json');actual=evaluate_lanes(image,[r for _,r,_ in cases]);assert actual==[v for _,_,v in cases],[(cases[i][0],v)for i,v in enumerate(actual)if v!=cases[i][2]];total+=len(cases)
 files=[pathlib.Path(__file__),HERE/'ValidationAudit.lean',HERE/'ExportValidation.lean',ROOT/'TlsMpc/Signal/PrivateShardedAccountV1.lean']
 report=dict(passed=True,candidate_only=True,kernel_endpoints=5,foundational_axioms_only=True,exact_AIG_cases=total,public_structural_fixture_only=True,native_MPC=False,account_activation=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'validation-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
