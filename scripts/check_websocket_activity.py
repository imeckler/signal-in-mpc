#!/usr/bin/env python3
"""Check proved private-length activity extraction against independent masks."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
def main():
    out=ROOT/'benchmarks/results/raw/websocket-activity';out.mkdir(parents=True,exist_ok=True)
    subprocess.run(['lake','build','websocket_activity_emitter'],cwd=ROOT,check=True)
    audit=out/'Audit.lean';endpoints=['activity_valid','activity_masks','run_map','run_correct','compiled_run_correct']
    audit.write_text('import TlsMpc.TlsWebSocketActivity\n'+''.join('#print axioms TlsMpc.TlsWebSocketActivity.'+n+'\n' for n in endpoints))
    proof=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,text=True,capture_output=True,check=True)
    (out/'proof.log').write_text(proof.stdout+proof.stderr)
    for line in proof.stdout.splitlines():
        if 'depends on axioms:' in line:assert set(re.search(r'\[(.*)\]',line).group(1).replace(' ','').split(','))<=set(['propext','Classical.choice','Quot.sound']),line
    total=0;results=[]
    for cap in (0,1,16,128,900,16385):
        artifact=out/f'activity-{cap}.json'
        with artifact.open('w') as stream:subprocess.run([str(ROOT/'.lake/build/bin/websocket_activity_emitter'),str(cap)],stdout=stream,check=True)
        cases=[];expected=[]
        for flag in (0,254,255):
            for length in sorted(set([0,1,15,16,127,128,255,256,cap,cap+1,65535])):
                cases.append(bytes([flag])+length.to_bytes(2,'big'))
                valid=flag==255 and length<=cap
                expected.append(bytes([255 if valid else 0])+bytes(255 if valid and i<length else 0 for i in range(cap)))
        assert evaluate_lanes(load(artifact),cases)==expected,(cap,'activity mismatch')
        total+=len(cases);results.append({'capacity':cap,'cases':len(cases),'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest()})
    names=['TlsMpc/TlsWebSocketActivity.lean','handshake_backend/WebSocketWork/EmitActivity.lean','scripts/check_websocket_activity.py','.lake/build/bin/websocket_activity_emitter']
    report={'passed':True,'cases':total,'capacities':results,'proof_endpoints':endpoints,'native_mpc_executed':False,
      'scope':'exact private bounds/source validity and active-byte predicates; no length opening',
      'sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names}}
    (ROOT/'benchmarks/results/tls-websocket-activity-checks.json').write_text(json.dumps(report,indent=2)+'\n');print('activity cases passed',total)
if __name__=='__main__':main()
