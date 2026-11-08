#!/usr/bin/env python3
"""Candidate mux/counter model, checked compiler map and fresh numeric artifacts."""
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
def main():
 out=ROOT/'benchmarks/results/raw/chat-mux';out.mkdir(parents=True,exist_ok=True)
 subprocess.run(['lake','build','chat_mux_emitter','request_id_emitter'],cwd=ROOT,check=True)
 fixture=subprocess.run(['lake','env','lean','--run','handshake_backend/WebSocketWork/MuxFixture.lean',str(out/'byte.txt'),str(out/'admit.txt')],cwd=ROOT,text=True,capture_output=True,check=True)
 (out/'fixture.log').write_text(fixture.stdout+fixture.stderr)
 mux=['process_map','admit_map','runByte_map','runAdmit_map','exactlyOne_four','compiled_runByte_correct','compiled_runAdmit_correct']
 counter=['seedBytes_map','next_map','allowed_value','next_increases','seed_prefix','seed_range','compiled_seed_correct','compiled_next_correct']
 audit=out/'Audit.lean';audit.write_text('import TlsMpc.TlsChatResponseMux\nimport TlsMpc.TlsPrivateRequestId\n'+''.join('#print axioms TlsMpc.TlsChatResponseMux.'+x+'\n' for x in mux)+''.join('#print axioms TlsMpc.TlsPrivateRequestId.'+x+'\n' for x in counter))
 proof=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,text=True,capture_output=True,check=True);(out/'proof.log').write_text(proof.stdout+proof.stderr)
 for line in proof.stdout.splitlines():
  if 'depends on axioms:' in line:assert set(re.search(r'\[(.*)\]',line).group(1).replace(' ','').split(','))<=set(['propext','Classical.choice','Quot.sound']),line
 results=[]
 for mode in ('byte','admit'):
  artifact=out/(mode+'.json')
  with artifact.open('w') as stream:subprocess.run([str(ROOT/'.lake/build/bin/chat_mux_emitter'),mode],stdout=stream,check=True)
  rows=[line.split() for line in (out/(mode+'.txt')).read_text().splitlines()]
  actual=evaluate_lanes(load(artifact),[bytes.fromhex(row[0]) for row in rows]);assert actual==[bytes.fromhex(row[1]) for row in rows],mode
  results.append({'mode':mode,'vectors':len(rows),'sha256':hashlib.sha256(artifact.read_bytes()).hexdigest()})
 rng=random.Random(517)
 seeds=[bytes([x])+rng.randbytes(7) for x in range(256)]+[bytes(8),bytes([255])*8]
 values=[0,1,2**63-1,2**63,2**63+127,2**63+128,3*2**62-1,2**64-3,2**64-2,2**64-1]+[rng.randrange(2**64) for _ in range(128)]
 for mode,inputs in [('seed',seeds),('next',[x.to_bytes(8,'big') for x in values])]:
  artifact=out/(mode+'.json')
  with artifact.open('w') as stream:subprocess.run([str(ROOT/'.lake/build/bin/request_id_emitter'),mode],stdout=stream,check=True)
  actual=evaluate_lanes(load(artifact),inputs)
  expected=[bytes([(x[0]&63)|128])+x[1:] for x in inputs] if mode=='seed' else [bytes([255])+(x+1).to_bytes(8,'big') if 2**63<=x<=2**64-2 else bytes(9) for x in values]
  assert actual==expected,mode
  results.append({'mode':mode,'vectors':len(inputs),'sha256':hashlib.sha256(artifact.read_bytes()).hexdigest()})
 files=['TlsMpc/TlsChatResponseMux.lean','TlsMpc/TlsPrivateRequestId.lean','handshake_backend/WebSocketWork/EmitMux.lean','handshake_backend/WebSocketWork/EmitRequestId.lean','handshake_backend/WebSocketWork/MuxFixture.lean','scripts/check_chat_mux.py','programs/tls_private_request_id.mpc','.lake/build/bin/chat_mux_emitter','.lake/build/bin/request_id_emitter']
 report={'passed':True,'native_mpc_executed':False,'scope':'candidate four-slot mux/counter source and compiler maps; full Rust/schema refinement, native mux/ID lifecycle and randomized VM wrapper integration separate','vectors':results,'proof_endpoints':{'mux':mux,'counter':counter},'sha256':{f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files}}
 (ROOT/'benchmarks/results/tls-chat-mux-checks.json').write_text(json.dumps(report,indent=2)+'\n');print(fixture.stdout.strip())
if __name__=='__main__':main()
