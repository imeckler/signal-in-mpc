#!/usr/bin/env python3
"""Public fixture differential: numeric XEdDSA stages versus unchanged libsignal.
SHA512 and modulo-ell reduction remain native oracle fixture boundaries.
No native MPC execution or actual Aeneas refinement is claimed.
"""
import hashlib,json,os,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load as load_bool
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes
from handshake_backend.field_dag import load as load_field,evaluate_clear,MODULUS as P
WORK=Path(__file__).resolve().parent
ELL=2**252+27742317777372353535851937790883648493
ART=WORK/'Artifacts';ART.mkdir(exist_ok=True)
ORACLE=ROOT/'.deps/signal-xeddsa-oracle-target/debug/signal-xeddsa-oracle'
EXPORT=WORK/'.lake/build/bin/emit_xeddsa'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def oracle(lines):
 p=subprocess.run([str(ORACLE)],input='\n'.join(lines)+'\n',text=True,capture_output=True,check=True)
 return p.stdout.splitlines()
def le(n):return n.to_bytes(32,'little')
def compress(x,y):return le(y|((x&1)<<255))
def sample(label,n):return hashlib.shake_256(label.encode()).digest(n)
def export(args):
 path=ART/('signal-xeddsa-'+'-'.join(map(str,args))+'.json')
 with path.open('w') as f:subprocess.run([str(EXPORT),*map(str,args)],stdout=f,check=True,timeout=600)
 return path

def main():
 subprocess.run(['lake','build'],cwd=WORK,check=True)
 env=dict(os.environ,CARGO_TARGET_DIR=str(ROOT/'.deps/signal-xeddsa-oracle-target'))
 subprocess.run(['cargo','+nightly-2025-09-24','build','--offline','--ignore-rust-version','--locked'],cwd=WORK/'Oracle',env=env,check=True)
 check=ROOT/'SignalReference/XEdDsaChecks.lean'
 audited=subprocess.run(['lake','env','lean',str(check)],cwd=ROOT,text=True,capture_output=True,check=True)
 names=re.findall(r'^#print axioms (\S+)',check.read_text(),re.M)
 found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",audited.stdout)
 assert [n for n,_ in found]==names
 for n,a in found:assert not ({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
 (WORK/'axioms.txt').write_text(audited.stdout)
 rows=[];fields={};bools={}
 for mode,count in [('recover',3),('double',2)]:
  fields[mode]=[]
  for i in range(count):
   path=export(['field',mode,i]);im=load_field(path);fields[mode].append(im)
   rows.append({'profile':path.stem,'sha256':sha(path),'nodes':len(im['nodes']),'field_multiplications':sum(n['op']=='mul' for n in im['nodes'])})
 for args in [['decode',n] for n in (0,63,64,65,128)]+[['match']]:
  path=export(args);im=load_bool(path);bools[tuple(args)]=im
  rows.append({'profile':path.stem,'sha256':sha(path),'statistics':statistics(im)})
  if args[0]=='decode':
   n=args[1];inputs=[sample('decode',max(0,n-1))+bytes([x]) if n else b'' for x in range(256)]
   expected=[(b'\xff'+bytes([raw[-1]>>7])+raw[:63]+bytes([raw[-1]&127])) if n==64 and raw[-1]&96==0 else bytes(66) for raw in inputs]
   assert evaluate_lanes(im,inputs)==expected,args
 def field(mode,inputs):return [evaluate_clear(im,inputs)[0] for im in fields[mode]]
 def recover(raw,sign):
  u=(int.from_bytes(raw,'little')%(2**255))%P
  valid,x,y=field('recover',[u]);assert valid in (0,1)
  if (x&1)!=sign:x=(-x)%P
  return valid,x,y
 rng=random.Random(0x584544)
 us=[0,1,2,9,P-1,P,P+1,P+2,2**255-1]+[rng.randrange(2**255) for _ in range(36)]
 rawus=[le(u|top) for u in us for top in (0,2**255)]
 recovery_cases=[]
 answers=oracle([f'recover {u.hex()} {sign}' for u in rawus for sign in (0,1)])
 for (raw,sign),answer in zip([(u,s) for u in rawus for s in (0,1)],answers):
  valid,x,y=recover(raw,sign)
  assert (compress(x,y).hex() if valid else 'none')==answer,(raw.hex(),sign,valid,x,y,answer)
  recovery_cases.append({'u':raw.hex(),'sign':sign,'accepted':bool(valid),'compressed':answer})
 print(f'recovery cases: {len(recovery_cases)}',flush=True)
 doubles=[]
 for i,u in enumerate(rawus):
  sign=i%2;valid,x,y=recover(u,sign)
  if not valid:continue
  h=int.from_bytes(sample(f'h{i}',64),'little')%ELL
  s=[0,1,ELL-1,ELL,ELL+1,2**253-1][i%6] if i<36 else rng.randrange(2**253)
  inp=[x,y]+[(h>>j)&1 for j in range(256)]+[(s>>j)&1 for j in range(253)]
  rx,ry=field('double',inp)
  answer=oracle([f'double {u.hex()} {sign} {le(h).hex()} {le(s).hex()}'])[0]
  assert compress(rx,ry).hex()==answer,(i,u.hex(),sign,s,answer)
  doubles.append({'u':u.hex(),'sign':sign,'h':le(h).hex(),'s':le(s).hex(),'compressed':answer})
 print(f'double-scalar cases: {len(doubles)}',flush=True)
 source=ROOT/'.deps/libsignal-v0.106.1/rust/core/src/curve/curve25519.rs'
 src=source.read_text();known={}
 for name in ('alice_identity_public','alice_ephemeral_public','alice_signature'):
  body=re.search(r'let '+name+r':[^=]+?= \[(.*?)\];',src,re.S).group(1)
  known[name]=bytes(int(x,16) for x in re.findall(r'0x([0-9a-fA-F]+)',body))
 key=b'\x05'+known['alice_identity_public'];msg=known['alice_ephemeral_public'];sig=known['alice_signature']
 sigs=[('pinned',key,msg,sig)]
 for i in range(64):
  t=bytearray(sig);t[i]^=1;sigs.append((f'mutated-{i}',key,msg,bytes(t)))
 for i in range(8):
  m=sample(f'msg{i}',[0,1,31,33,64,128,1569,33][i]);k,s=oracle([f'sign {sample(f"key{i}",32).hex()} {m.hex() or "-"}'])[0].split()
  sigs.append((f'generated-{i}',bytes.fromhex(k),m,bytes.fromhex(s)))
 for label,k,m,s in list(sigs):
  if label.startswith(('pinned','generated')):
   sn=int.from_bytes(s[32:],'little')%(2**255)
   t=s[:32]+le((sn+ELL)|((s[-1]>>7)<<255))
   assert (t[-1]&96)==0
   sigs.append((label+'-S-plus-ell',k,m,t))
 for n in (0,1,63,65,128):sigs.append((f'bad-length-{n}',key,msg,sample('bad-length',n)))
 for u in (0,1,2,P-1,P,P+1,P+2,2**255-1):sigs.append((f'special-u-{u}',b'\x05'+le(u),msg,sig))
 # Probe actual low-order-point behavior; this is not a new acceptance policy.
 for u in (1,P+1):
  for sign in (0,1):sigs.append((f'low-order-{u}-{sign}',b'\x05'+le(u),b'public fixture',le(1)+le(sign<<255)))
 for t in (0x20,0x40,0x60,0x80):sigs.append((f'high-bits-{t}',key,msg,sig[:63]+bytes([sig[-1]^t])))
 verified=oracle([f'verify {k.hex()} {m.hex() or "-"} {s.hex() or "00"}' for _,k,m,s in sigs])
 # Empty signature needs literal empty support in oracle; zero-byte vs empty both reject.
 composed=[]
 for (label,k,m,s),expected in zip(sigs,verified):
  actual=False;hbytes=None
  if len(s)==64 and s[-1]&96==0:
   valid,x,y=recover(k[1:],s[-1]>>7)
   if valid:
    capA=compress(x,y);data=s[:32]+capA+m
    full,hhex=oracle([f'hash {data.hex()}'])[0].split();hbytes=bytes.fromhex(hhex)
    assert bytes.fromhex(full)==hashlib.sha512(data).digest()
    assert int.from_bytes(hbytes,'little')==int.from_bytes(bytes.fromhex(full),'little')%ELL
    hh=int.from_bytes(hbytes,'little');ss=int.from_bytes(s[32:],'little')%(2**255)
    rx,ry=field('double',[x,y]+[(hh>>j)&1 for j in range(256)]+[(ss>>j)&1 for j in range(253)])
    actual=evaluate_lanes(bools[('match',)],[s+le(rx)+le(ry)])[0]==b'\xff'
  assert actual==(expected=='true'),(label,expected,actual)
  composed.append({'label':label,'key':k.hex(),'message':m.hex(),'signature':s.hex(),'native_h':hbytes.hex() if hbytes else None,'accepted':actual})
 fixtures={'recovery':recovery_cases,'double_scalar':doubles,'composed_native_hash_boundary':composed}
 (WORK/'fixtures.json').write_text(json.dumps(fixtures,indent=2)+'\n')
 print(f'composed cases: {len(composed)}',flush=True)
 sources=set()
 def visit(mod):
  if not mod.startswith('TlsMpc'):return
  p=ROOT/(mod.replace('.','/')+'.lean')
  if p in sources:return
  sources.add(p)
  for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
 visit('TlsMpc.Signal.XEdDsa');visit('TlsMpc.Signal.XEdDsaField')
 sources|={Path(__file__),check,WORK/'Export.lean',ROOT/'SignalReference/XEdDsaExport.lean',WORK/'lakefile.toml',WORK/'Oracle/Cargo.toml',WORK/'Oracle/Cargo.lock',WORK/'Oracle/src/main.rs',WORK/'Oracle/.cargo/config.toml',ROOT/'handshake_backend/field_dag.py',ROOT/'scripts/check_lean_crypto.py',ROOT/'backend_adapter/boolean.py',ROOT/'backend_adapter/aig.py',source,ROOT/'.deps/libsignal-v0.106.1/rust/core/src/curve.rs',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/session.rs',ROOT/'.deps/libsignal-v0.106.1/Cargo.lock'}
 for name in ('curve25519-dalek-5.0.0','sha2-0.11.0','x25519-dalek-3.0.0'):
  sources.update((ROOT/'.deps/libsignal-vendor'/name).rglob('*.rs'))
 sources.update((ROOT/'.deps/libsignal-v0.106.1/rust/core/src').rglob('*.rs'))
 sources.update((ROOT/'.deps/libsignal-v0.106.1/rust/debug/src').rglob('*.rs'))
 report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'proof_endpoints':len(names),'custom_axioms':[],
  'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(sources)},'oracle_binary_sha256':sha(ORACLE),'export_binary_sha256':sha(EXPORT),
  'fixtures_sha256':sha(WORK/'fixtures.json'),'profiles':rows,'decode_lanes':5*256,'recovery_cases':len(recovery_cases),'double_scalar_cases':len(doubles),'composed_cases':len(composed),
  'noncanonical_S_plus_ell_accepted':sum(r['accepted'] and 'S-plus-ell' in r['label'] for r in composed),
  'actual_native_libsignal_and_dalek_differential':True,'actual_aeneas_refinement':False,'native_mpc_executed':False,'pqxdh_validation_status_produced':False,
  'security_profile':{'parties':5,'malicious':2,'statistical_security':128,'abort_allowed':True,'tested_runtime':False},
  'compiler_proof':'Every accepted field output and Boolean byte circuit equals the executable Lean formula for all assignments. No group-law or Rust source refinement theorem.',
  'native_boundary':'SHA512 and hash modulo ell from actual pinned RustCrypto/dalek oracle; Python canonical field-to-byte conversion and signed root selection. Not a complete MPC verifier.',
  'oracle_build':'offline installed nightly-2025-09-24 --ignore-rust-version: source unchanged; libsignal declares rust-version1.93.1; all compiled successfully',
  'remaining':['shared SHA512 and scalar reduction','proved/composed canonical field-byte and sign binding','actual Aeneas verifier refinement','prekey identity trust and complete policy','native five-party malicious statistical128 execution']}
 (WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
