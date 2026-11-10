#!/usr/bin/env python3
"""Actual pinned constructors/key leaves/prefix vs kernel-checked numeric stages."""
import hashlib,json,os,re,shutil,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes
WORK=Path(__file__).resolve().parent;ART=WORK/'Artifacts';ART.mkdir(exist_ok=True)
EXPORT=WORK/'.lake/build/bin/emit_prekey';XWORK=ROOT/'SignalReference/XEdDsaWork'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def oracle(rows,features='all'):
 p=subprocess.run([str(WORK/'Bin'/('oracle-'+features))],input=''.join(json.dumps(v)+'\n' for v in rows),text=True,capture_output=True,check=True)
 return [json.loads(x) for x in p.stdout.splitlines()]
def artifact(mode,n,features='all'):
 path=ART/f'signal-prekey-{mode}-{n}-{features}.json'
 with path.open('w') as f:subprocess.run([str(EXPORT),'export',mode,str(n),features],stdout=f,check=True)
 return path
def concrete(mode,n,features,inputs):
 p=subprocess.run([str(EXPORT),'evaluate',mode,str(n),features],input=''.join(json.dumps(list(v))+'\n' for v in inputs),text=True,capture_output=True,check=True)
 return [bytes(json.loads(x)) for x in p.stdout.splitlines()]
def metadata(row):return (row.get('registration',0xffffffff).to_bytes(4,'big')+bytes([row.get('device',127)])+b''.join(row.get(k,0xffffffff).to_bytes(4,'big') for k in ('optional_id','signed_id','pq_id')))
def expected_result(answer):
 code=answer['code']
 return bytes([255,0,int(answer['optional'])])+bytes(answer['metadata']) if code==0 else bytes([0,code])+bytes(18)
def frozen_check():
 comp=json.loads((XWORK/'completion.json').read_text())
 for p,h in comp['files'].items():assert sha(ROOT/p)==h,('frozen source changed',p)
 return sha(XWORK/'completion.json')
def main():
 frozen=frozen_check();mods=['PreKeyWire','PreKeyBundle','PreKeyValidation']
 lines=['import TlsMpc.Signal.'+m for m in mods]
 for m in mods:lines += ['#print axioms TlsMpc.Signal.'+m+'.'+n for n in re.findall(r'^theorem (\w+)',(ROOT/'TlsMpc/Signal'/f'{m}.lean').read_text(),re.M)]
 (WORK/'Checks.lean').write_text('\n'.join(lines)+'\n')
 subprocess.run(['lake','build'],cwd=WORK,check=True)
 env=dict(os.environ,CARGO_TARGET_DIR=str(WORK/'Build/Oracle'))
 (WORK/'Bin').mkdir(exist_ok=True)
 for features,args in [('base',[]),('all',['--features','all-kems'])]:
  subprocess.run(['cargo','+nightly-2025-09-24','build','--offline','--ignore-rust-version','--locked',*args],cwd=WORK/'Oracle',env=env,check=True)
  shutil.copyfile(WORK/'Build/Oracle/debug/signal-prekey-oracle',WORK/'Bin'/('oracle-'+features));(WORK/'Bin'/('oracle-'+features)).chmod(0o755)
 p=subprocess.run(['lake','env','lean',str(WORK/'Checks.lean')],cwd=ROOT,text=True,capture_output=True,check=True)
 found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
 names=re.findall(r'^#print axioms (\S+)',(WORK/'Checks.lean').read_text(),re.M);assert [n for n,_ in found]==names
 for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
 (WORK/'axioms.txt').write_text(p.stdout)
 profiles=[];counts={};wire_samples=[]
 def check(mode,n,features,inputs,expected):
  assert concrete(mode,n,features,inputs)==expected,(mode,n,features,'concrete')
  path=artifact(mode,n,features);im=load(path);assert evaluate_lanes(im,inputs)==expected,(mode,n,features,'numeric')
  profiles.append({'profile':path.stem,'sha256':sha(path),'lanes':len(inputs),'statistics':statistics(im)})
  counts[mode]=counts.get(mode,0)+len(inputs)
 for mode,features,sizes in [('ec','all',[0,1,32,33,35]),('kem','base',[0,1,1185,1186,1568,1569,1570]),('kem','all',[0,1,1185,1186,1568,1569,1570])]:
  for n in sizes:
   inputs=[bytes([tag])+bytes((i*31)%256 for i in range(n-1)) for tag in range(256)] if n else [b'']
   answers=oracle([{'mode':mode,'raw':x.hex()} for x in inputs],features)
   expected=[bytes([255 if a['code']==0 else 0,a['code']])+(bytes.fromhex(a['wire']) if a['code']==0 else bytes(33 if mode=='ec' else n)) for a in answers]
   check(mode,n,features,inputs,expected)
   wire_samples.extend({'mode':mode,'features':features,'size':n,'tag':raw[0] if raw else None,'code':a['code']} for raw,a in zip(inputs,answers))
 vals=list(range(256))+[256,65535,65536,2**31,2**32-1]
 answers=oracle([{'mode':'device','value':n} for n in vals]);inputs=[n.to_bytes(4,'big') for n in vals]
 check('device',4,'all',inputs,[bytes([255,a['value']]) if a['valid'] else bytes(2) for a in answers])
 inputs=[bytes([f,s]) for f in [0,1,2] for s in range(256)];check('optional',2,'all',inputs,[bytes([x[1] if x[0]==1 else 255]) for x in inputs])
 bases=oracle([{'mode':'generate','seed':114+tag,'tag':tag} for tag in [7,8,10]])
 for b,tag in zip(bases,[7,8,10]):b['tag_profile']=tag
 base=bases[1];construct_rows=[]
 for n in range(2048):
  row=dict(base,mode='construct',flags=[(n>>i)&1 for i in range(11)],registration=n*1048577,device=1+n%127,
   optional_id=[0,1,2**31,2**32-1][n%4],signed_id=[2**32-1,2**31,1,0][n%4],pq_id=(n*65537)&0xffffffff)
  construct_rows.append(row)
 answers=oracle(construct_rows);inputs=[bytes(r['flags'])+metadata(r) for r in construct_rows]
 check('construct',28,'all',inputs,[expected_result(a) for a in answers])
 constructed=bytes([255,0,1])+metadata(base);inputs=[];expected=[]
 for trust in range(256):
  for ec in [0,1,255]:
   for pq in [0,1,255]:
    code=(0 if ec==pq==255 else 18) if trust==0 else (16 if trust==1 else 17)
    inputs.append(constructed+bytes([trust,ec,pq]));expected.append(constructed if code==0 else bytes([0,code])+bytes(18))
 check('finish',23,'all',inputs,expected)
 prefix_cases=[]
 for trust in [0,1,2]:
  for ec_bad,pq_bad in [(False,False),(True,False),(False,True),(True,True)]:
   row=dict(base,mode='validate',trust=trust,label=f'trust{trust}-ec{ec_bad}-pq{pq_bad}')
   for key,bad in [('ec_sig',ec_bad),('pq_sig',pq_bad)]:
    if bad:r=bytearray.fromhex(row[key]);r[0]^=1;row[key]=r.hex()
   prefix_cases.append(row)
 for pos in range(11):
  row=dict(base,mode='validate',label=f'absent-{pos}',flags=[1]*11,trust=2);row['flags'][pos]=0;prefix_cases.append(row)
 for label,changes in [('ec-trailing',{'ec':base['ec']+'aabbcc'}),('identity-trailing',{'identity':base['identity']+'ff'}),
  ('untagged-ec-signature',{'ec_sig':base['untagged_ec_sig']}),('untagged-pq-signature',{'pq_sig':base['untagged_pq_sig']}),
  ('zero-ids',{'registration':0,'optional_id':0,'signed_id':0,'pq_id':0}),('empty-ec-signature',{'ec_sig':''}),('short-pq-signature',{'pq_sig':base['pq_sig'][:-2]}),
  ('changed-pq-tag',{'pq': '0a'+base['pq'][2:]}),('absent-identity-garbage',{'identity':'','flags':[1,1,1,1,1,1,1,0,1,1,1]}),
  ('absent-optional-garbage',{'optional_key':'','flags':[1,1,1,0,1,1,1,1,1,1,1]})]:
  prefix_cases.append(dict(base,mode='validate',label=label,**changes))
 for b in bases:prefix_cases.append(dict(b,mode='validate',label=f'valid-tag{b["tag_profile"]}'))
 outcomes=oracle(prefix_cases)
 for row,out in zip(prefix_cases,outcomes):
  if out['code']==0:assert out['trace']==['trust_sending','load_session_boundary']
  elif out['code'] in (16,17,18):assert out['trace']==['trust_sending']
  else:assert out['trace']==[]
 fixtures={'bases':bases,'prefix':[{'input':r,'actual':o} for r,o in zip(prefix_cases,outcomes)],'wire_classes':wire_samples}
 (WORK/'fixtures.json').write_text(json.dumps(fixtures,indent=2)+'\n')
 # Numeric prefix applied to actual constructor outputs and actual fixture signatures.
 # Signature statuses here are test inputs only; full adapter computes them separately.
 cin=oracle([dict(r,mode='construct') for r in prefix_cases]);fin=[];fout=[]
 for row,out,c in zip(prefix_cases,outcomes,cin):
  # Obtain each real signature result by actual prefix calls with the OTHER valid signature.
  ec_probe=dict(row,flags=[1]*11,trust=0,pq_sig=base['pq_sig'],pq=base['pq'],identity=base['identity'],optional_key=base['ec'])
  pq_probe=dict(row,flags=[1]*11,trust=0,ec_sig=base['ec_sig'],ec=base['ec'],identity=base['identity'],optional_key=base['ec'])
  if row.get('label','').startswith('valid-tag'):
   ec_ok=pq_ok=True
  elif row['identity']=='':ec_ok=pq_ok=False
  else:
   ec_ok=oracle([dict(ec_probe,mode='validate')])[0]['code']==0
   pq_ok=oracle([dict(pq_probe,mode='validate')])[0]['code']==0
  fin.append(expected_result(c)+bytes([row['trust'],255 if ec_ok else 0,255 if pq_ok else 0]));fout.append(expected_result(out))
 assert evaluate_lanes(load(ART/'signal-prekey-finish-23-all.json'),fin)==fout
 sources=set()
 def visit(mod):
  if not mod.startswith('TlsMpc'):return
  p=ROOT/(mod.replace('.','/')+'.lean')
  if p in sources:return
  sources.add(p)
  for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
 for m in mods:visit('TlsMpc.Signal.'+m)
 sources|={Path(__file__),WORK/'Checks.lean',WORK/'Export.lean',WORK/'lakefile.toml',WORK/'Oracle/Cargo.toml',WORK/'Oracle/Cargo.lock',WORK/'Oracle/src/main.rs',WORK/'Oracle/.cargo/config.toml',ROOT/'backend_adapter/boolean.py',ROOT/'backend_adapter/aig.py',ROOT/'scripts/check_lean_crypto.py',XWORK/'completion.json'}
 for d in ['rust/core/src','rust/protocol/src','rust/crypto/src']:sources.update((ROOT/'.deps/libsignal-v0.106.1'/d).rglob('*.rs'))
 sources.add(ROOT/'.deps/libsignal-v0.106.1/Cargo.lock')
 report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'proof_endpoints':len(names),'custom_axioms':[],
  'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(sources)},'profiles':profiles,'lanes':counts,
  'actual_constructor_presence_combinations':len(construct_rows),'actual_process_validation_prefix_cases':len(prefix_cases),'actual_rust_store_trace_checked':True,
  'oracle_binary_sha256':{f:sha(WORK/'Bin'/('oracle-'+f)) for f in ['base','all']},'export_binary_sha256':sha(EXPORT),'fixtures_sha256':sha(WORK/'fixtures.json'),
  'frozen_xeddsa_completion_sha256':frozen,'actual_aeneas_refinement':False,'native_mpc_executed':False,'full_process_prekey_bundle_success_claimed':False,
  'scope':'Typed key/device leaves, actual constructor optional/presence order, ordered validation-prefix result. Actual process function stops at intentional load_session sentinel after signature verification; no session/KEM initialization or writes.'}
 assert frozen_check()==frozen
 (WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({'lanes':counts,'proof_endpoints':len(names),'prefix_cases':len(prefix_cases)}),flush=True)
if __name__=='__main__':main()
