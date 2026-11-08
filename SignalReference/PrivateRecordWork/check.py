#!/usr/bin/env python3
"""PUBLIC fixture adapter: pinned protobuf -> fixed-capacity private AST."""
import json,subprocess,hashlib,time
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def varint(raw,i):
 n=0;shift=0
 while True:
  b=raw[i];i+=1;n|=(b&127)<<shift
  if b<128:return n,i
  shift+=7;assert shift<70
def fields(raw):
 out={};i=0
 while i<len(raw):
  key,i=varint(raw,i);tag,wire=key>>3,key&7
  if wire==0:value,i=varint(raw,i)
  else:
   assert wire==2;n,i=varint(raw,i);value=raw[i:i+n];i+=n
  out.setdefault(tag,[]).append(value)
 return out
def byte(tag,value=b'',cap=0,present=255,emit=False):
 cap=max(cap,len(value));return dict(kind=0,tag=tag,present=present,emit=emit,length=len(value),data=list(value)+[0]*(cap-len(value)))
def scalar(tag,value=0,emit=False):return dict(kind=1,tag=tag,present=255,emit=emit,data=list(value.to_bytes(4,'big')))
def message(tag,children,present=255):return dict(kind=2,tag=tag,present=present,children=children)
def make(raw,schema):
 f=fields(raw);out=[]
 for tag,kind,arg,count in schema:
  values=f.pop(tag,[]);assert len(values)<=count,(tag,len(values),count)
  for i in range(count):
   v=values[i] if i<len(values) else (0 if kind=='s' else b'');p=255 if i<len(values) else 0
   if kind=='s':out.append(scalar(tag,v))
   elif kind=='b':out.append(byte(tag,v,arg,p))
   elif kind=='o':out.append(byte(tag,v,arg,p,True))
   else:out.append(message(tag,make(v,arg),p))
 assert not f,('unmapped actual fields',f.keys())
 return out
ck=[(1,'s',None,1),(2,'b',32,1)]
chain=[(1,'b',33,1),(2,'b',32,1),(3,'m',ck,1)]
direction=[(1,'s',None,1),(2,'b',32,1),(3,'b',0,1)]
epoch=[(1,'m',direction,1),(2,'m',direction,1)]
pqchain=[(1,'s',None,1),(2,'s',None,1),(3,'m',epoch,1),(4,'b',32,1),(5,'s',None,1),(6,'o',16,1)]
pq=[(1,'o',128,1),(2,'m',pqchain,1),(3,'o',128,1)]
session=[(1,'s',None,1),(2,'b',33,1),(3,'b',33,1),(4,'b',32,1),(5,'s',None,1),(6,'m',chain,1),(7,'m',chain,5),(9,'o',128,1),(10,'s',None,1),(11,'s',None,1),(13,'b',33,1),(14,'o',2048,1),(15,'m',pq,1),(16,'s',None,1)]
record=[(1,'m',session,1),(2,'o',1024,2),(3,'m',[(1,'s',None,1),(2,'s',None,1)],1)]
def main():
 binary=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-session-inorder-oracle'
 fixture=json.loads(subprocess.check_output([str(binary)],input=json.dumps(dict(seed=19,plaintext=(b'A'*79+b'\x80').hex()))+'\n',text=True))
 local_new=json.loads(subprocess.check_output([str(binary)],input=json.dumps(dict(seed=23,origin_local_new=True,plaintext=(b'B'*79+b'\x80').hex()))+'\n',text=True))
 requests=[];expected=[]
 for row in fixture['rows'][:2]+local_new['rows'][:1]:
  before=bytes.fromhex(row['record_before']);after=bytes.fromhex(row['record_after'])
  nodes=make(before,record)
  requests.append(dict(nodes=nodes,result=list(bytes.fromhex(row['expected'])),projection=list(bytes.fromhex(row['expected'])[1:526]),capacity=1024));expected.append(after)
 row=fixture['rows'][0];bad=bytearray.fromhex(row['expected']);bad[0]=0
 requests.append(dict(nodes=make(bytes.fromhex(row['record_before']),record),result=list(bad),projection=list(bytes.fromhex(row['input'])[:525]),capacity=1024));expected.append(bytes.fromhex(row['record_before']))
 started=time.monotonic();p=subprocess.run(['lake','env','lean','--run',str(HERE/'Evaluate.lean')],cwd=ROOT,input=''.join(json.dumps(r)+'\n'for r in requests),text=True,capture_output=True,timeout=240)
 assert p.returncode==0,p.stderr
 for want,line in zip(expected,p.stdout.splitlines(),strict=True):
  got=bytes(json.loads(line));assert got[0]==255;actual=got[3:3+int.from_bytes(got[1:3],'big')]
  assert actual==want,(len(actual),len(want),[(i,x,y)for i,(x,y)in enumerate(zip(actual,want))if x!=y][:10])
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 assert audit.count('depends on axioms:')==5 and all(x not in audit for x in ['sorryAx','_native','Lean.ofReduceBool'])
 sources=[HERE/x for x in ['check.py','Evaluate.lean','Checks.lean','README.md']]+[ROOT/'TlsMpc/Signal'/x for x in ['PrivateRecordEncodingV1.lean','PrivateRecordEncodingV1Proofs.lean','PrivateRecordUpdateV1.lean','PrivateRecordSnapshotV1.lean']]+[ROOT/'signal_backend/Oracle/src/bin/signal-session-inorder-oracle.rs',ROOT/'signal_backend/Oracle/src/session_projection.rs']
 report=dict(passed=True,whole_record_byte_cases=4,private_snapshot_roundtrip_projection_checked=True,first_new_DH=True,repeated_known=True,LocalNew_prekey_acknowledgement=True,rejected_result_exact_preservation=True,encoder_Hom_and_compiler_endpoints=5,axiom_audit=audit,update_Hom_proof=False,actual_source_refinement=False,full_schema_private_validation=False,provider_admission=False,atomic_outbox_restart=False,native_MPC_run=False,seconds=time.monotonic()-started,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources},oracle_binary_sha256=sha(binary))
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 print('4 private canonical full-record encodings match actual libsignal',round(report['seconds'],3),'seconds')
if __name__=='__main__':main()
