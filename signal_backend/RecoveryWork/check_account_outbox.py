#!/usr/bin/env python3
"""Computed private resume policy; explicit bounded one-pending profile."""
import hashlib,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
from account_fixture import fixture
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes

def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateAccountOutboxV1'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
 audit=HERE/'AccountOutboxAudit.lean';audit.write_text('import TlsMpc.Signal.PrivateAccountOutboxV1\n'+''.join('#print axioms TlsMpc.Signal.PrivateAccountOutboxV1.'+name+'\n'for name in ['resumable_map','select_map','compiled_select_correct']))
 text=subprocess.check_output(['lake','env','lean',str(audit)],cwd=ROOT,text=True);groups=re.findall(r'depends on axioms: \[(.*?)\]',text,re.S);assert len(groups)==3
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text
 data=fixture();entry=data['committed'][9][:1302];total=0
 for ordinal in range(4):
  queue=bytes(ordinal*1302)+entry+bytes((3-ordinal)*1302);disp=bytearray(4);disp[ordinal]=1;raw=b'\xff'+queue+disp;expected=b'\xff'+entry[1:];cases=[('unsent',raw,expected)]
  for value in [2,5]:
   new=bytearray(raw);new[5209+ordinal]=value;cases.append(('resumable-'+str(value),bytes(new),expected))
  for value in [0,3,4,255]:
   new=bytearray(raw);new[5209+ordinal]=value;cases.append(('not-resumable-'+str(value),bytes(new),bytes(1302)))
  for value in [0,1,254]:cases.append(('upstream-'+str(value),bytes([value])+raw[1:],bytes(1302)))
  new=bytearray(raw);other=(ordinal+1)%4;new[1+other*1302:1+(other+1)*1302]=entry;new[5209+other]=1;cases.append(('two-pending',bytes(new),bytes(1302)))
  new=bytearray(raw);new[1+ordinal*1302]=0;cases.append(('absent',bytes(new),bytes(1302)))
  image=load(ROOT/f'.deps/private-account-outbox-native/v1-candidate-1/outbox-{ordinal}.json');actual=evaluate_lanes(image,[r for _,r,_ in cases]);assert actual==[v for _,_,v in cases],[(ordinal,cases[i][0])for i,v in enumerate(actual)if v!=cases[i][2]];total+=len(cases)
 files=[pathlib.Path(__file__),audit,ROOT/'TlsMpc/Signal/PrivateAccountOutboxV1.lean',ROOT/'SignalReference/PrivateRecordWork/ExportAccountOutbox.lean',HERE/'NativeAccountOutbox.h'];sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 (HERE/'account-outbox-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=3,foundational_axioms_only=True,exact_AIG_cases=total,ordinals=4,one_pending_profile=True,computed_resumability_not_host_flag=True,native_MPC=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS: 3 foundation-only endpoints; '+str(total)+' exact private outbox policy cases')
if __name__=='__main__':main()
