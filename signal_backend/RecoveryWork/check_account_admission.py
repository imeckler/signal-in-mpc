#!/usr/bin/env python3
"""Bounded structural account coherence, not full bootstrap/semantic validity."""
import hashlib,json,pathlib,re,subprocess
from account_fixture import fixture
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent

def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateAccountAdmissionV2Proofs'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
 data=fixture();cases=[]
 for name in ['initial','reserve','committed','second_reserve','second_commit']:
  cases.append((name,b''.join(data[name]),255))
 base=bytearray(cases[2][1]);c=8306
 for name,offset,value in [('identity',38,base[38]^1),('identity_type',70,4),('global_status',103,0),('cursor_domain',8298,0),('recipient_uuid',c,base[c]^1),('registration',c+16,3),('remote_type',c+20,4),('remote_identity',c+21,base[c+21]^1),('access_key',c+53,base[c+53]^1),('device',c+5619+602,2),('selected',c+6230,base[c+6230]^1),('intent_presence',c+6755,1),('outbox_presence',c+7367,1),('outbox_status',c+7368,0),('disposition',c+12575,0),('absent_outbox_data',c+7367+1302+50,1)]:
  bad=base.copy();bad[offset]=value;cases.append((name,bytes(bad),0))
 bad=base.copy();bad[8298:8306]=b'\xff'*8;cases.append(('cursor_exhausted',bytes(bad),0));cases.append(('truncated',bytes(base[:-1]),0))
 request=''.join(json.dumps(dict(conversations=2,raw=list(raw)))+'\n'for _,raw,_ in cases)
 output=subprocess.check_output(['lake','env','lean','--run','SignalReference/PrivateRecordWork/EvaluateAccount.lean'],cwd=ROOT,input=request,text=True)
 actual=[json.loads(s)for s in output.splitlines()];assert actual==[[v]for _,_,v in cases],[(cases[i][0],a)for i,a in enumerate(actual)if a!=[cases[i][2]]]
 audit=HERE/'AccountAdmissionAudit.lean';audit.write_text('import TlsMpc.Signal.PrivateAccountAdmissionV2Proofs\n'+''.join('#print axioms TlsMpc.Signal.PrivateAccountAdmissionV2.'+n+'\n'for n in ['all_map','oneOf_map','canonicalPayload_map','validate_map','compiled_validate_correct']))
 text=subprocess.check_output(['lake','env','lean',str(audit)],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',text,re.S);assert len(groups)==5
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text
 files=[pathlib.Path(__file__),HERE/'account_fixture.py',audit,ROOT/'TlsMpc/Signal/PrivateAccountAdmissionV2.lean',ROOT/'TlsMpc/Signal/PrivateAccountAdmissionV2Proofs.lean',ROOT/'SignalReference/PrivateRecordWork/EvaluateAccount.lean']
 report=dict(passed=True,candidate_only=True,kernel_endpoints=5,foundational_axioms_only=True,cases=[dict(name=n,expected=v)for n,_,v in cases],conversations=2,logical_bytes=len(base),actual_record_and_global_store_fixtures=True,structural_outboxes_synthetic=True,full_global_store_semantic_validation=False,private_public_DH_binding=False,native_MPC=False,whole_account_activation=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'account-admission-report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: 5 foundation-only endpoints; '+str(len(cases))+' bounded account coherence cases')
if __name__=='__main__':main()
