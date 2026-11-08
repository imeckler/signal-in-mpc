#!/usr/bin/env python3
"""Private-length packing/append differential checks; public fixtures only."""
import hashlib,json,random,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
HERE=Path(__file__).resolve().parent;ART=ROOT/'.deps/private-buffer-artifacts';ART.mkdir(exist_ok=True)
ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def emit(arguments,name):
 path=ART/(name+'.json')
 with path.open('w') as stream:subprocess.run(['lake','env','lean','--run',str(HERE/'Export.lean'),*arguments],cwd=ROOT,stdout=stream,check=True)
 return path
def oracle(values):
 p=subprocess.run([str(ORACLE)],input=''.join(json.dumps({'mode':'varint','value':n})+'\n' for n in values),text=True,capture_output=True,check=True)
 return [bytes.fromhex(json.loads(line)['wire']) for line in p.stdout.splitlines()]
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateVarint'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S):
  assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit;(HERE/'axioms.txt').write_text(audit)
 rng=random.Random(127128);results=[];total=0
 for cap in [0,1,2,7,16,127,128,255,256,1024]:
  path=emit(['append',str(cap)],'append-'+str(cap));image=load(path);raw=[];expected=[]
  lengths=list(range(cap+2)) if cap<=7 else sorted(set([0,1,cap//2,cap-1,cap,cap+1,65535]))
  pairs=[(x,y,255,255) for x in lengths for y in lengths]
  pairs += [(rng.randrange(65536),rng.randrange(65536),255,255) for _ in range(16)]
  pairs += [(0,0,a,b) for a,b in [(0,255),(255,0),(7,255),(254,255),(0,0)]]
  for l,r,lv,rv in pairs:
   ld=rng.randbytes(cap);rd=rng.randbytes(cap)
   raw.append(bytes([lv])+l.to_bytes(2,'big')+ld+bytes([rv])+r.to_bytes(2,'big')+rd)
   if lv==rv==255 and l<=cap and r<=cap and l+r<=cap:
    content=ld[:l]+rd[:r];expected.append(b'\xff'+len(content).to_bytes(2,'big')+content+bytes(cap-len(content)))
   else:expected.append(bytes(cap+3))
  observed=evaluate_lanes(image,raw);assert observed==expected,cap
  del image;total+=len(raw);results.append({'capacity':cap,'cases':len(raw),'sha256':sha(path)})
  print(f'append capacity{cap}: {len(raw)} cases',flush=True)
 varints={}
 for width in [32,64]:
  values=set(range(256))|{0,1,2**width-1}
  for n in range(7,width,7):values|={2**n-1,2**n,2**n+1}
  values|={rng.randrange(2**width) for _ in range(128)};values=sorted(values)
  reference=oracle(values);path=emit(['varint'+str(width)],'varint'+str(width));image=load(path)
  observed=evaluate_lanes(image,[n.to_bytes(width//8,'big') for n in values]);del image
  cap=5 if width==32 else 10
  assert observed==[b'\xff'+len(x).to_bytes(2,'big')+x+bytes(cap-len(x)) for x in reference]
  varints[str(width)]={'cases':len(values),'sha256':sha(path)}
 path=emit(['counter-chunk'],'counter-chunk');values=[126,127,128,129,16383,16384,2**32-1]
 expected=[]
 for encoded in oracle(values):
  content=b'\x10'+encoded+b'payload';expected.append(b'\xff'+len(content).to_bytes(2,'big')+content+bytes(16-len(content)))
 assert evaluate_lanes(load(path),[n.to_bytes(4,'big') for n in values])==expected
 files=[HERE/'Export.lean',HERE/'Checks.lean',Path(__file__),ROOT/'TlsMpc/Signal/PrivateBuffer.lean',ROOT/'TlsMpc/Signal/PrivateVarint.lean']
 report={'candidate_only':True,'append_cases':total,'capacities':results,'actual_prost_varint_cases':varints,
  'counter_width_chunk_cases':len(values),'127_to_128_preserves_secret_length_and_canonical_bytes':True,
  'wire_contract':'valid mask8 || lengthBE16 || fixed-capacity data; valid empty distinct from rejection',
  'append_overflow':'Reject and zero validity/length/data; never truncate accepted data',
  'chunk_semantics':'Concatenate only each valid chunk prefix, preserving embedded zero bytes and order; any rejected chunk poisons result',
  'native_mpc_executed':False,'full_signal_private_length_hmac_and_serialization':False,'tls_integrated':False,
  'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'oracle_sha256':sha(ORACLE),
  'integer_endian_add_compare_lemmas':False,'all_capacity_append_integer_spec_theorem':False,'production_ready':False}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 print(f'{total} append cases; native varint comparisons;7 width-transition chunks passed',flush=True)
if __name__=='__main__':main()
