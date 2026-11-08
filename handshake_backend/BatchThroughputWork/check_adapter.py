#!/usr/bin/env python3
"""Exact independent-output, lane-width and scheduling differential checks."""
from pathlib import Path
import hashlib,json,random,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.aig import execute
from backend_adapter.aig_packed import plan
from backend_adapter.aig_batched import execute_batch
rng=random.Random(51613);cases=0
class Packed:
    and_bits=0;and_batches=0
    def __init__(self,value,n):self.value=value;self.n=n
    def __xor__(self,other):
        assert self.n==other.n;return Packed(self.value^other.value,self.n)
    def __and__(self,other):
        assert self.n==other.n;Packed.and_bits+=self.n;Packed.and_batches+=1
        return Packed(self.value&other.value,self.n)
for dag in range(64):
 nodes=[[0]]+[[1,i,1,0]for i in range(8)]
 for _ in range(100):
  left,right=[rng.randrange(len(nodes))for _ in range(2)]
  nodes.append([2,left,rng.randrange(2),right,rng.randrange(2)])
  if rng.randrange(4)==0:
   nodes.append([2,left,1,right,1]);nodes.append([2,len(nodes)-2,1,len(nodes)-1,1])
 image={'format':'tls-mpc-aig-v1','input_bits':8,'input_widths':[1]*8,'nodes':nodes,'outputs':[[rng.randrange(len(nodes)),rng.randrange(2)]for _ in range(24)]}
 _,groups=plan(image)
 for count in [1,2,3,4,8,17,64]:
  inputs=[[rng.randrange(2)for _ in range(8)]for _ in range(count)]
  wanted=[execute(image,values,0,1)for values in inputs]
  for width in [1,7,64]:
   Packed.and_bits=Packed.and_batches=0;depths=[]
   def pack(values):return Packed(sum(value<<i for i,value in enumerate(values)),len(values))
   actual=execute_batch(image,inputs,0,1,pack,lambda v,n:[(v.value>>i)&1 for i in range(n)],lambda n,v:Packed(v,n),lanes=width,begin_depth=depths.append)
   assert actual==wanted
   assert Packed.and_bits==count*sum(len(g)for k,g in groups if k[2]==1)
   assert Packed.and_batches==sum((count*len(g)+width-1)//width for k,g in groups if k[2]==1)
   assert depths==sorted(set(k[0]for k,g in groups))
   cases+=1
 for bad in [[],[[0]*7],[[0]*8]*65]:
  try:execute_batch(image,bad,0,1,None,None,None);raise AssertionError('bad dimensions accepted')
  except ValueError:pass
# A failed unpack cannot return a partial payload batch.
try:
 execute_batch(image,[[0]*8,[1]*8],0,1,pack,lambda v,n:[],lambda n,v:Packed(v,n))
 raise AssertionError('bad unpack accepted')
except ValueError:pass
report={'passed':True,'public_cases':cases,'native_MPC_executed':False,'independent_outputs_and_exact_AND_lane_consumption':True,'sequential_VM_caller_required':True,'producer_transaction_integrated':False,'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [ROOT/'backend_adapter/aig_batched.py',Path(__file__)]}}
Path(__file__).with_name('adapter-report.json').write_text(json.dumps(report,indent=2)+'\n');print('batch packing checks passed',cases)
