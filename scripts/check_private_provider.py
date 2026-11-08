#!/usr/bin/env python3
"""Public ownership/lifecycle checks; no native MPC execution."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
def main():
 out=ROOT/'benchmarks/results/raw/private-provider';out.mkdir(parents=True,exist_ok=True)
 subprocess.run(['lake','build','provider_gate_emitter'],cwd=ROOT,check=True)
 image=out/'gate.json'
 with image.open('w') as stream:subprocess.run([str(ROOT/'.lake/build/bin/provider_gate_emitter')],stdout=stream,check=True)
 rows=[bytes([a,b]) for a in range(256) for b in range(256)]
 actual=evaluate_lanes(load(image),rows)
 assert actual==[bytes([255 if a==255 and b==255 else 0]) for a,b in rows]
 audit=out/'Audit.lean';names=['gate_map','gate_value','compiled_gate_correct']
 audit.write_text('import TlsMpc.TlsProviderGate\n'+''.join('#print axioms TlsMpc.TlsProviderGate.'+n+'\n' for n in names))
 p=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,text=True,capture_output=True,check=True);(out/'proof.log').write_text(p.stdout+p.stderr)
 for line in p.stdout.splitlines():
  if 'depends on axioms:' in line:assert set(re.search(r'\[(.*)\]',line).group(1).replace(' ','').split(','))<=set(['propext','Classical.choice','Quot.sound'])
 executable=out/'registry-checks'
 subprocess.run(['c++','-std=c++20','-O1','-fsanitize=address,undefined',str(ROOT/'handshake_backend/WebSocketWork/provider_registry_checks.cpp'),'-o',str(executable)],check=True)
 check=subprocess.run([str(executable)],text=True,capture_output=True,check=True);(out/'registry.log').write_text(check.stdout+check.stderr)
 files=['TlsMpc/TlsProviderGate.lean','handshake_backend/WebSocketWork/EmitProviderGate.lean','handshake_backend/WebSocketWork/PrivateProviderRegistry.h','handshake_backend/WebSocketWork/provider_registry_checks.cpp','scripts/check_private_provider.py','.lake/build/bin/provider_gate_emitter']
 report={'passed':True,'gate_pairs':len(rows),'proof_endpoints':names,'registry_checks':check.stdout.strip(),'native_mpc_executed':False,
  'scope':'embedding-only opaque ownership/phase/failure and computed validity propagation; authenticated bootstrap/normal-worker/native composition separate',
  'sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files}}
 (ROOT/'benchmarks/results/tls-private-provider-checks.json').write_text(json.dumps(report,indent=2)+'\n');print(check.stdout.strip())
if __name__=='__main__':main()
