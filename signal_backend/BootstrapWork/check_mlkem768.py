#!/usr/bin/env python3
"""PUBLIC four-lane exact component composition vs pinned libcrux keygen."""
import hashlib,json,pathlib,subprocess,sys
from functools import lru_cache
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from signal_backend.BootstrapWork.pinned_stages import PinnedStages
from SignalReference.MlKemWork.adapter import MlKem
from backend_adapter.boolean import execute

def verify(stage):
 stages=PinnedStages(stage/'components.json',expected_variant='mlkem768')
 oracle=ROOT/'.deps/signal-libcrux-mlkem-oracle-target/debug/signal-libcrux-mlkem-oracle'
 seeds=[bytes(64),bytes(range(64)),bytes([255])*64,hashlib.sha512(b'actual-initial-SPQR-MLKEM768').digest()];expected=[]
 for seed in seeds:
  p=subprocess.run([str(oracle)],input='mlkem768|'+seed.hex()+'|'+bytes(32).hex()+'\n',capture_output=True,text=True,check=True)
  sk,pk,*_=map(bytes.fromhex,p.stdout.strip().split('|'));expected.append(b'\xff'+sk+pk)
 lanes=len(seeds);one=(1<<lanes)-1
 raw=[sum(((seed[i//8]>>(7-i%8))&1)<<lane for lane,seed in enumerate(seeds))for i in range(512)]
 image=lru_cache(maxsize=2)(stages.image);calls=[]
 def invoke(key,bits):
  calls.append(key);print('ML-KEM768 numeric component',len(calls),key,flush=True)
  return execute(image(key),bits,0,one)
 result=MlKem('mlkem768',invoke,0,one).keygen(raw)
 actual=[bytes(sum(((result[8*i+j]>>lane)&1)<<(7-j)for j in range(8))for i in range(len(result)//8))for lane in range(lanes)]
 assert actual==expected,'ML-KEM768 staged/numeric actual-libcrux mismatch'
 image.cache_clear()
 return dict(passed=True,public_lanes=lanes,component_calls=len(calls),output_bytes=len(actual[0]),oracle_sha256=hashlib.sha256(oracle.read_bytes()).hexdigest(),source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),native_MPC=False)
if __name__=='__main__':
 print(json.dumps(verify(pathlib.Path(sys.argv[1]).resolve()),indent=2))
