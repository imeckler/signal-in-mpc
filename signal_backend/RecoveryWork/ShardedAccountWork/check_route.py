#!/usr/bin/env python3
"""Explicit private validity versus declassified idle/pending/blocked routes."""
import hashlib,json,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(HERE))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
from check_outbox import cell

def main():
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'RouteAudit.lean')],cwd=ROOT,text=True);groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==5
 for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 total=0;zero=bytes(1304);idle=b'\xff\0\0'+bytes(1301);blocked=b'\xff\0\xff'+bytes(1301)
 for ordinal in range(4):
  q=bytes(ordinal*1310)+cell(7)+bytes((3-ordinal)*1310);d=bytearray(4);d[ordinal]=1
  def raw(queue=q,dispositions=d,generation=7,valid=255):return bytes([valid])+queue+dispositions+generation.to_bytes(8,'big')
  want=b'\xff\xff\0'+cell(7)[1:1302];cases=[('pending',raw(),want),('never-sent-idle',raw(bytes(5240),bytes(4),0),idle),('missing-latest-immutable-entry',raw(bytes(5240),bytes(4),7),zero)]
  for status in [2,5]:
   ds=bytearray(d);ds[ordinal]=status;cases.append(('pending-'+str(status),raw(dispositions=ds),want))
  for status,expected in [(3,idle),(4,blocked),(0,zero),(255,zero)]:
   ds=bytearray(d);ds[ordinal]=status;cases.append(('disposition-'+str(status),raw(dispositions=ds),expected))
  cases.extend([('wrong-generation',raw(generation=8),zero),('zero-generation-nonempty',raw(generation=0),zero),('invalid-account',raw(valid=0),zero)])
  ds=bytearray(d);ds[ordinal]=3;cases.append(('acknowledged-cannot-be-never-sent',raw(dispositions=ds,generation=0),zero))
  other=(ordinal+1)%4;queue=bytearray(q);queue[other*1310:(other+1)*1310]=cell(9);ds=bytearray(d);ds[other]=1;cases.append(('two-pending-malformed',raw(queue,ds),zero));ds[other]=4;cases.append(('rejected-blocks-pending-without-dropping-data',raw(queue,ds),blocked))
  hidden=bytearray(5240);hidden[1302]=1;cases.append(('hidden-never-sent-generation',raw(hidden,bytes(4),0),zero))
  actual=evaluate_lanes(load(ROOT/f'.deps/private-shard-route-native/v1-candidate-2/outbox-{ordinal}.json'),[r for _,r,_ in cases]);assert actual==[v for _,_,v in cases],[(ordinal,cases[i][0],v[:3])for i,v in enumerate(actual)if v!=cases[i][2]];total+=len(cases)
 files=[pathlib.Path(__file__),HERE/'RouteAudit.lean',HERE/'ExportRoute.lean',ROOT/'TlsMpc/Signal/PrivateShardedOutboxRouteV1.lean'];report=dict(passed=True,candidate_only=True,kernel_endpoints=5,foundational_axioms_only=True,exact_AIG_cases=total,idle_pending_blocked_distinct=True,never_sent_requires_canonical_all_absent=True,original_ID_and_wire_preserved_for_pending=True,metadata_declassification_requires_prior_aggregate_authenticated_validity=True,private_MPC=False,restore_activation=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files});(HERE/'route-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
