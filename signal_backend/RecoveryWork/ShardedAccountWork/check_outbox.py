#!/usr/bin/env python3
"""Kernel axiom audit + exact exported reusable-cell circuit cases."""
import hashlib,json,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes

def cell(n):return b'\xff\xff\x00\x01'+bytes([n])+bytes(1289)+n.to_bytes(8,'big')*2

def main():
 audit=subprocess.check_output(['lake','env','lean','--run',str(HERE/'OutboxChecks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==5
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in audit and 'passed 42 cases'in audit
 total=0
 for ordinal in range(4):
  old=cell(1);new=cell(99);queue=bytearray(old*4);disp=bytearray([1,2,4,5]);disp[ordinal]=3
  def raw(q=queue,d=disp,n=new,g=99,valid=255):return bytes([valid])+q+d+n+g.to_bytes(8,'big')
  expected=bytearray(queue);expected[ordinal*1310:(ordinal+1)*1310]=new;newdisp=bytearray(disp);newdisp[ordinal]=1
  accepted=b'\xff'+expected+newdisp;cases=[('accepted-reclaim',raw(),bytes(accepted))]
  zero=bytes(5245)
  for status in [0,1,2,4,5,255]:
   bad=bytearray(disp);bad[ordinal]=status;cases.append(('reject-disposition-'+str(status),raw(d=bad),zero))
  for status in [0,1,254]:cases.append(('reject-upstream-'+str(status),raw(valid=status),zero))
  cases += [('generation-mismatch',raw(g=98),zero),('generation-reuse',raw(n=old,g=1),zero)]
  absent=bytearray(queue);absent[ordinal*1310:(ordinal+1)*1310]=bytes(1310);absentdisp=bytearray(disp);absentdisp[ordinal]=0
  cases.append(('canonical-absent',raw(q=absent,d=absentdisp),bytes(accepted)))
  bad=bytearray(new);bad[1293]=1;cases.append(('padding-reject',raw(n=bad),zero))
  bad=bytearray(absent);bad[ordinal*1310+1302]=1;cases.append(('hidden-absent-generation',raw(q=bad,d=absentdisp),zero))
  image=load(ROOT/f'.deps/private-reusable-outbox-native/v1-candidate-1/outbox-{ordinal}.json');actual=evaluate_lanes(image,[r for _,r,_ in cases]);assert actual==[v for _,_,v in cases],[(ordinal,cases[i][0])for i,v in enumerate(actual)if v!=cases[i][2]];total+=len(cases)
 files=[pathlib.Path(__file__),HERE/'OutboxChecks.lean',HERE/'ExportOutbox.lean',ROOT/'TlsMpc/Signal/PrivateReusableOutboxV1.lean']
 report=dict(passed=True,candidate_only=True,kernel_endpoints=5,foundational_axioms_only=True,concrete_cases=42,exact_AIG_cases=total,private_reclaim_only_absent_or_observed_accepted=True,preserve_unsent_attempted_rejected_uncertain=True,other_cells_byte_exact=True,host_must_bind_generation_to_actual_certificate=True,native_MPC=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'outbox-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
