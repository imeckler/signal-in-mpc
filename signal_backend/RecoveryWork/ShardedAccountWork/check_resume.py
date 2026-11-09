#!/usr/bin/env python3
import hashlib,json,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(HERE))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
from check_outbox import cell

def main():
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'ResumeAudit.lean')],cwd=ROOT,text=True);groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==2
 for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 total=0
 for ordinal in range(4):
  q=bytes(ordinal*1310)+cell(7)+bytes((3-ordinal)*1310);d=bytearray(4);d[ordinal]=1;raw=b'\xff'+q+d+(7).to_bytes(8,'big');want=b'\xff'+cell(7)[1:1302];zero=bytes(1302);cases=[('unsent',raw,want)]
  for status in [2,5]:
   b=bytearray(raw);b[5241+ordinal]=status;cases.append(('resumable-'+str(status),bytes(b),want))
  for status in [0,3,4,255]:
   b=bytearray(raw);b[5241+ordinal]=status;cases.append(('reject-disposition-'+str(status),bytes(b),zero))
  cases.append(('wrong-certified-generation',raw[:-8]+(8).to_bytes(8,'big'),zero));cases.append(('zero-certified-generation',raw[:-8]+bytes(8),zero));cases.append(('invalid-account',b'\0'+raw[1:],zero))
  b=bytearray(raw);other=(ordinal+1)%4;b[1+other*1310:1+(other+1)*1310]=cell(9);b[5241+other]=1;cases.append(('two-pending',bytes(b),zero))
  actual=evaluate_lanes(load(ROOT/f'.deps/private-shard-resume-native/v1-candidate-1/outbox-{ordinal}.json'),[r for _,r,_ in cases]);assert actual==[v for _,_,v in cases],[(ordinal,cases[i][0])for i,v in enumerate(actual)if v!=cases[i][2]];total+=len(cases)
 files=[pathlib.Path(__file__),HERE/'ResumeAudit.lean',HERE/'ExportResume.lean',ROOT/'TlsMpc/Signal/PrivateShardedOutboxResumeV1.lean'];report=dict(passed=True,candidate_only=True,kernel_endpoints=2,foundational_axioms_only=True,exact_AIG_cases=total,original_private_ID_and_wire_preserved=True,expected_generation_must_come_from_actual_certified_ancestry=True,private_MPC=False,restore_activation=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files});(HERE/'resume-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
