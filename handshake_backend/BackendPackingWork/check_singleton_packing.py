#!/usr/bin/env python3
"""Public exact-width model plus actual compiler receipts in FastShaSumWork."""
from pathlib import Path
import hashlib,json,random,sys,types
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter import aig,aig_packed
class Packed:
 n=40;triples=0;widths=[]
 def __init__(self,value=0):self.value=value.value if isinstance(value,Packed) else value
 def __and__(self,other):
  width=max(self.n,other.n);Packed.triples+=width;Packed.widths.append(width);return self.get_type(width)(self.value&other.value)
 def __xor__(self,other):return self.get_type(max(self.n,other.n))(self.value^other.value)
 def bit_decompose(self,size):return [Bit((self.value>>i)&1) for i in range(size)]
 @classmethod
 def get_type(cls,n):
  if n==1:return Bit
  return type('WidthBits',(Packed,),{'n':n})
 @classmethod
 def bit_compose(cls,bits):
  if len(bits)==1 and isinstance(bits[0],cls):return cls(bits[0]) # pinned upstream behavior
  return cls.get_type(len(bits))(sum((b.value&1)<<i for i,b in enumerate(bits)))
class Bit(Packed):n=1
compiler=types.ModuleType('Compiler');gc=types.ModuleType('Compiler.GC');typ=types.ModuleType('Compiler.GC.types');prog=types.ModuleType('Compiler.program');typ.sbit=Bit;typ.sbits=Packed;prog.Program=types.SimpleNamespace(prog=types.SimpleNamespace(curr_tape=types.SimpleNamespace(start_new_basicblock=lambda **kwargs:None)))
sys.modules.update({'Compiler':compiler,'Compiler.GC':gc,'Compiler.GC.types':typ,'Compiler.program':prog})
rng=random.Random(731);cases=0;profiles={}
for width in [1,2,3,39,40,41,63,64,65,127,128,129]:
 nodes=[[0]]+[[1,i,1,0]for i in range(2*width)]
 outputs=[]
 for i in range(width):nodes.append([2,1+i,i%2,1+width+i,(i//2)%2]);outputs.append([len(nodes)-1,i%2])
 image=dict(format='tls-mpc-aig-v1',input_bits=2*width,input_widths=[1]*(2*width),nodes=nodes,outputs=outputs)
 for _ in range(16):
  values=[rng.randrange(2)for i in range(2*width)];wanted=aig.execute(image,values,0,1)
  Packed.triples=0;Packed.widths=[];actual=aig_packed.execute_mpc(image,[Bit(v)for v in values]);new=Packed.triples;used=list(Packed.widths)
  assert [v.value&1 for v in actual]==wanted;assert new==width;assert all(n<=64 for n in used)
  Packed.triples=0;legacy=aig_packed.execute(image,[Bit(v)for v in values],Bit(0),Bit(1),Packed.bit_compose,lambda value,size:value.bit_decompose(size),lambda size,value:Packed.get_type(size)(value))
  assert [v.value&1 for v in legacy]==wanted;old=Packed.triples
  assert old==width+(39 if width%64==1 else 0),(width,old,new)
  profiles[str(width)]={'legacy_triples':old,'singleton_triples':new,'new_batch_widths':used};cases+=1
report=dict(passed=True,public_equivalence_cases=cases,modeled_upstream_singleton_width=40,profiles=profiles,actual_compiler_evidence='SignalReference/FastShaSumWork/compile-report-singleton.json',native_MPC_executed=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [Path(__file__),ROOT/'backend_adapter/aig_packed.py']})
(Path(__file__).with_name('singleton-packing-checks.json')).write_text(json.dumps(report,indent=2)+'\n');print('singleton/mixed-width output/consumption checks passed:',cases)
