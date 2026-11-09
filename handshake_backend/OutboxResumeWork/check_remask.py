#!/usr/bin/env python3
import hashlib,json,pathlib,random,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import execute,validate
cap=1290;image=validate(json.loads(pathlib.Path('/tmp/tls-remask-1290.json').read_text()));rng=random.Random(91721)
cases=[];expected=[];payloads=[]
def add(n,mutate=None):
 plain=bytes(rng.randrange(256)for _ in range(n-8));old=rng.randbytes(4);fresh=rng.randbytes(4)
 frame=b'\x82\xfe'+len(plain).to_bytes(2,'big')+old+bytes(v^old[i%4]for i,v in enumerate(plain))
 data=bytearray(b'\xff\xff'+n.to_bytes(2,'big')+frame+bytes(cap-n)+fresh)
 if mutate:mutate(data)
 new=frame[:4]+fresh+bytes(v^fresh[i%4]for i,v in enumerate(plain))
 cases.append(bytes(data));expected.append((b'\xff'+n.to_bytes(2,'big')+new+bytes(cap-n))if not mutate else bytes(cap+3));payloads.append(plain)
for n in range(134,cap+1):add(n)
mutations=[lambda b:b.__setitem__(0,0),lambda b:b.__setitem__(0,254),lambda b:b.__setitem__(1,0),lambda b:b.__setitem__(4,0x02),lambda b:b.__setitem__(4,0x81),lambda b:b.__setitem__(5,0x7e),lambda b:b.__setitem__(5,0xff),lambda b:b.__setitem__(6,b[6]^1),lambda b:b.__setitem__(7,b[7]^1),lambda b:b.__setitem__(2,0xff),lambda b:b.__setitem__(3,0),lambda b:b.__setitem__(4+200,1)]
for mutate in mutations:add(200,mutate)
# Padding case above modifies first inactive byte, not application data.
start=time.monotonic();one=(1<<len(cases))-1
columns=[]
for byte in range(cap+8):
 for bit in range(7,-1,-1):columns.append(sum(((raw[byte]>>bit)&1)<<i for i,raw in enumerate(cases)))
outputs=execute(image,columns,0,one)
for case,want in enumerate(expected):
 got=bytes(sum(((outputs[8*i+j]>>case)&1)<<(7-j)for j in range(8))for i in range(cap+3))
 assert got==want,(case,got[:12].hex(),want[:12].hex())
 if got[0]:
  n=int.from_bytes(got[1:3],'big');frame=got[3:3+n];mask=frame[4:8]
  assert bytes(v^mask[i%4]for i,v in enumerate(frame[8:]))==payloads[case]
report={'passed':True,'capacity':cap,'accepted_lengths':cap-134+1,'rejected_cases':len(mutations),'case_count':len(cases),'nodes':len(image['nodes']),'seconds':time.monotonic()-start,'artifact_sha256':hashlib.sha256(pathlib.Path('/tmp/tls-remask-1290.json').read_bytes()).hexdigest(),'native_mpc':False,'fresh_mask_source':'Public fixture input here; production wrapper must generate32 joint private VM random bits per call.'}
pathlib.Path(__file__).with_name('remask-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
