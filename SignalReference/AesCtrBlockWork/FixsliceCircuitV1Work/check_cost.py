#!/usr/bin/env python3
"""Public ciphertext/cost comparison; no native MPC performance claim."""
import hashlib,json,pathlib,random,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT))
from backend_adapter import aig
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 stage=ROOT/'.deps/reference-fixslice-cost-v1';oracle=ROOT/'.deps/reference-fixslice-oracle-target/debug/reference-fixslice-oracle'
 rng=random.Random(0xA256);results={}
 for kind in ['candidate','reference']:
  for blocks,repeats in [(1,1),(4,1),(1,2),(4,2)]:
   label=f'{kind}-{blocks}x{repeats}';path=stage/(label+'.json');image=json.loads(path.read_text());aig.validate(image)
   fixtures=[]
   for case in range(32):
    data=([0]*image['input_bits'] if False else [rng.randrange(256) for _ in image['input_widths']])
    if case<2:data=[255*case]*len(data)
    fixtures.append(data)
   requests=[dict(mode='aes',key=f[:32],plaintext=f[32:])for f in fixtures]
   raw=subprocess.check_output([str(oracle)],input=''.join(json.dumps(x)+'\n'for x in requests),text=True)
   expected=[json.loads(x)['ciphertext']for x in raw.splitlines()];assert len(expected)==32
   packed=[sum(((f[i//8]>>(7-i%8))&1)<<lane for lane,f in enumerate(fixtures))for i in range(image['input_bits'])]
   want=[sum(((f[i//8]>>(7-i%8))&1)<<lane for lane,f in enumerate(expected))for i in range(len(image['outputs']))]
   for optimize in [False,True]:assert aig.execute(image,packed,0,(1<<32)-1,optimize=optimize)==want,(label,optimize)
   kinds=aig._plan(image['nodes'],image['outputs'],True);depth=[0]*len(kinds);ands=[0]*len(kinds)
   for i,(node,k)in enumerate(zip(image['nodes'],kinds)):
    if not k or node[0]!=2:continue
    sources=aig._xor_sources(image['nodes'],node)if k==2 else(node[1],node[2],node[3],node[4])
    depth[i]=max(depth[sources[0]],depth[sources[2]])+1
    ands[i]=max(ands[sources[0]],ands[sources[2]])+(k==1)
   results[label]={**aig.statistics(image),'logical_depth':max(depth),'and_depth':max(ands),'input_bytes':len(image['input_widths']),'output_bytes':len(image['outputs'])//8,'public_rust_cases':32,'artifact_sha256':sha(path)}
   print(label,results[label],flush=True)
 report=dict(passed=True,candidate_only=True,production_changed=False,public_fixture_only=True,native_performance_measured=False,interop='actual aes0.9.1 forced-soft public encrypt_block/encrypt_blocks;32 fixtures/profile; raw and XOR-recovered numeric evaluation',key_reuse='one secret32-byte key, one shared expansion per profile; repeats2 encrypts independent inputs under same key',profiles=results,source_sha256={p.name:sha(p)for p in [HERE/'Export.lean',pathlib.Path(__file__),HERE/'export_cost.py']},oracle_sha256=sha(oracle),remaining=['actual backend trait borrow/copy wrapper extraction','CTR buffering/XOR wrapper composition','HMAC/KDF and full sealed-sender wrapper source composition'])
 (HERE/'cost-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
