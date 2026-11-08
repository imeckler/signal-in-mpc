#!/usr/bin/env python3
"""Bounded private control queue and masked frame encoding checks."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
def main():
    out=ROOT/'benchmarks/results/raw/websocket-control';out.mkdir(parents=True,exist_ok=True)
    subprocess.run(['lake','build','websocket_control_checks','websocket_control_emitter'],cwd=ROOT,check=True)
    tape=out/'tape.txt';encoded=out/'encoded.txt'
    checked=subprocess.run([str(ROOT/'.lake/build/bin/websocket_control_checks'),str(tape),str(encoded)],cwd=ROOT,text=True,capture_output=True,check=True)
    (out/'checks.log').write_text(checked.stdout+checked.stderr)
    audit=out/'Audit.lean';endpoints=['step_map','run_map','encode_map','addSix_value','compiled_run_correct','compiled_encode_correct']
    audit.write_text('import TlsMpc.TlsWebSocketControl\n'+''.join('#print axioms TlsMpc.TlsWebSocketControl.'+n+'\n' for n in endpoints))
    proof=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,text=True,capture_output=True,check=True)
    (out/'proof.log').write_text(proof.stdout+proof.stderr)
    for line in proof.stdout.splitlines():
        if 'depends on axioms:' in line:assert set(re.search(r'\[(.*)\]',line).group(1).replace(' ','').split(','))<=set(['propext','Classical.choice','Quot.sound']),line
    results=[]
    for mode,vectors in [('collect',tape),('encode',encoded)]:
        artifact=out/(mode+'.json')
        with artifact.open('w') as stream:subprocess.run([str(ROOT/'.lake/build/bin/websocket_control_emitter'),mode],stdout=stream,check=True)
        rows=[line.split() for line in vectors.read_text().splitlines()]
        inputs=[bytes.fromhex(row[0]) for row in rows];expected=[bytes.fromhex(row[1]) for row in rows]
        actual=evaluate_lanes(load(artifact),inputs);assert actual==expected,(mode,'numeric control mismatch')
        if mode=='encode':
            for raw,result in zip(inputs,actual):
                length=int.from_bytes(raw[1:3],'big');valid=raw[0]==255 and length<=125 and raw[3] in (8,10)
                assert bool(result[0])==valid
                if valid:
                    wire=result[3:3+int.from_bytes(result[1:3],'big')]
                    assert len(wire)==length+6 and wire[:2]==bytes([128|raw[3],128|length])
                    assert wire[2:6]==raw[4:8]
                    assert bytes(byte^wire[2+i%4] for i,byte in enumerate(wire[6:]))==raw[8:8+length]
                else:assert result==bytes(134)
        results.append({'mode':mode,'vectors':len(rows),'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest()})
    names=['TlsMpc/TlsWebSocketControl.lean','handshake_backend/WebSocketWork/EmitControl.lean',
      'handshake_backend/WebSocketWork/ControlFixture.lean','scripts/check_websocket_control.py','.lake/build/bin/websocket_control_emitter']
    report={'passed':True,'vectors':results,'proof_endpoints':endpoints,'native_mpc_executed':False,
      'scope':'private control collection/overflow and independent WebSocket header/mask checks; fresh joint randomness/native TLS composition separate',
      'sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names}}
    (ROOT/'benchmarks/results/tls-websocket-control-checks.json').write_text(json.dumps(report,indent=2)+'\n');print(checked.stdout)
if __name__=='__main__':main()
