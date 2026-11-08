#!/usr/bin/env python3
"""Bounded private padding/final-state differential checks; public fixtures."""
import hashlib,hmac,json,random,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
HERE=Path(__file__).resolve().parent;ART=ROOT/'.deps/private-hash-artifacts';ART.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateHash'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit;(HERE/'axioms.txt').write_text(audit)
 rng=random.Random(65536);profiles=[]
 for cap in [0,56,128,145,512]:
  for mode in ['hash','hmac']:
   path=ART/f'{mode}-{cap}.json'
   with path.open('w') as stream:subprocess.run(['lake','env','lean','--run',str(HERE/'Export.lean'),mode,str(cap)],cwd=ROOT,stdout=stream,check=True)
   lengths=sorted(set(n for n in [0,1,54,55,56,57,63,64,65,119,120,127,128,129,cap-1,cap] if 0<=n<=cap))
   raw=[];expected=[]
   for n in lengths:
    key=rng.randbytes(32);data=rng.randbytes(cap)
    raw.append((key if mode=='hmac' else b'')+b'\xff'+n.to_bytes(2,'big')+data)
    digest=hmac.digest(key,data[:n],'sha256') if mode=='hmac' else hashlib.sha256(data[:n]).digest()
    expected.append(b'\xff\x00\x20'+digest)
   for status,n in [(0,0),(1,0),(254,0),(255,cap+1),(255,65535)]:
    raw.append((bytes(32) if mode=='hmac' else b'')+bytes([status])+n.to_bytes(2,'big')+rng.randbytes(cap));expected.append(bytes(35))
   image=load(path);observed=evaluate_lanes(image,raw);assert observed==expected,(mode,cap,next((i for i,(a,b) in enumerate(zip(observed,expected)) if a!=b),None))
   profiles.append({'mode':mode,'capacity':cap,'cases':len(raw),'nodes':len(image['nodes']),'sha256':sha(path)})
   print(f'{mode} cap{cap}: {len(raw)} private-length cases',flush=True)
 files=[Path(__file__),HERE/'Export.lean',HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateHash.lean',ROOT/'TlsMpc/Signal/PrivateBuffer.lean']
 report={'profiles':profiles,'standard_axioms_only':True,'public_work':'One compression per maximum padded block, no length-dependent execution or opening.',
  'semantic_integer_sha_refinement_proved':False,'backend_native_mpc_executed':False,'service_integrated':False,
  'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Private SHA/HMAC padding, final-state and rejection cases passed',flush=True)
if __name__=='__main__':main()
