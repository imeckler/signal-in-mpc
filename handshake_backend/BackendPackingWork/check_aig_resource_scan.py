#!/usr/bin/env python3
"""Compare bounded-memory public scanner with existing adapter plans."""
from pathlib import Path
import json,random,subprocess,sys,tempfile,hashlib
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
sys.path.insert(0,str(ROOT));from backend_adapter.aig import statistics
from backend_adapter.aig_packed import plan
random.seed(71329);binary=Path('/tmp/tls-aig-resource-scan');cases=100
with tempfile.TemporaryDirectory(prefix='tls-aig-scan-check-') as folder:
 for case in range(cases):
  nodes=[[0],[1,0,1,0],[1,1,1,0]]
  for _ in range(80):
   a=random.randrange(len(nodes));b=random.randrange(len(nodes))
   if random.randrange(5)==0:
    l=len(nodes);nodes.append([2,a,0,b,0]);r=len(nodes);nodes.append([2,a,1,b,1]);nodes.append([2,l,1,r,1])
   else:nodes.append([2,a,random.randrange(2),b,random.randrange(2)])
  image=dict(format='tls-mpc-aig-v1',input_bits=2,input_widths=[1,1],nodes=nodes,outputs=[[random.randrange(len(nodes)),random.randrange(2)] for _ in range(20)])
  p=Path(folder)/'dag.json';p.write_text(json.dumps(image));actual=json.loads(subprocess.check_output([str(binary),str(p)]));expected=statistics(image)
  for k,v in expected.items():assert actual[k]==v,(case,k,actual[k],v)
  _,groups=plan(image)
  expected.update(nodes=len(nodes),and_depth=max((k[0] for k,g in groups),default=0),maximum_local_xor_depth=max((k[1] for k,g in groups),default=0),and_groups=sum(k[2]==1 for k,g in groups),xor_groups=sum(k[2]==2 for k,g in groups),packed_and_batches64=sum((len(g)+63)//64 for k,g in groups if k[2]==1),packed_xor_batches64=sum((len(g)+63)//64 for k,g in groups if k[2]==2))
  assert expected==actual,(case,expected,actual)
report=dict(passed=True,public_dags=cases,scope='resource counts/packing groups versus existing adapter; no execution or proof extension',source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [WORK/'aig_resource_scan.cpp',Path(__file__),ROOT/'backend_adapter/aig.py',ROOT/'backend_adapter/aig_packed.py']},binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest())
(WORK/'aig-resource-scan-checks.json').write_text(json.dumps(report,indent=2)+'\n');print('public AIG scanner differential checks passed:',cases)
