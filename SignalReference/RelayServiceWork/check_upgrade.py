#!/usr/bin/env python3
"""Local HTTP upgrade syntax/credential tests, not account authentication."""
import base64,hashlib,json,subprocess,sys,uuid
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
HERE=Path(__file__).resolve().parent;ART=ROOT/'.deps/relay-service-artifacts';ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 path=ART/'upgrade-22.json'
 with path.open('w') as out:subprocess.run(['lake','env','lean','--run',str(HERE/'UpgradeExport.lean'),'22'],cwd=ROOT,stdout=out,check=True)
 values=[uuid.UUID(int=i).bytes+b'x'*22+hashlib.sha256(str(i).encode()).digest()[:16] for i in range(4)]
 output=evaluate_lanes(load(path),values)
 result=subprocess.run([str(ORACLE)],input=''.join(json.dumps({'mode':'upgrade','wire':x.hex()})+'\n' for x in output),capture_output=True,text=True,check=True)
 answers=[json.loads(x) for x in result.stdout.splitlines()]
 for raw,answer in zip(values,answers):
  assert answer['status']==101
  assert bytes.fromhex(answer['credentials'])==(str(uuid.UUID(bytes=raw[:16]))+':').encode()+raw[16:38]
  assert answer['key']==base64.b64encode(raw[38:]).decode()
 report={'local_upgrade_syntax_cases':4,'native_tungstenite_response_created':True,'credentials_match':True,
  'real_account_authentication_tested':False,'server_http101_validation_in_mpc':False,'network_side_effects':False,
  'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__),HERE/'UpgradeExport.lean',ROOT/'TlsMpc/Signal/RelayUpgrade.lean',ROOT/'signal_backend/Oracle/src/relay.rs']},
  'oracle_sha256':sha(ORACLE),'artifact_sha256':sha(path)}
 (HERE/'upgrade-report.json').write_text(json.dumps(report,indent=2)+'\n');print('4 local upgrade/credential syntax cases passed; no account authentication claim')
if __name__=='__main__':main()
