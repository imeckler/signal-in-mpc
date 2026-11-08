#!/usr/bin/env python3
"""Public streaming HTTP101 fixtures; compiler/native equivalence is separate."""
from pathlib import Path
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[1]
def main():
    started=time.monotonic()
    out=ROOT/'benchmarks/results/raw/websocket-upgrade';out.mkdir(parents=True,exist_ok=True)
    status='HTTP/1.1 101 Switching Protocols\r\n'
    accept='s3pPLMBiTxaQ9kYGzzhZRbK+xOo='
    fields=['Upgrade: websocket','Connection: Upgrade','Sec-WebSocket-Accept: '+accept]
    def header(fs=fields,s=status):return (s+'\r\n'.join(fs)+'\r\n\r\n').encode()
    records=[]
    def add(raw,valid=255,done=255,rest=b'',splits=None):
        splits=splits or [len(raw)]
        records.append(' '.join([raw.hex(),','.join(map(str,splits)),str(valid),str(done),rest.hex() or '-']))
    valid=[header(),header(list(reversed(fields))),header(['uPgRaDe:\t WebSocket \t','connection: keep-alive, UpGrade','SEC-WEBSOCKET-ACCEPT:\t'+accept+' \t','Date: fixture','X-Extra: foo:bar'])]
    for h in valid:
        body=b'\x82\x04test\x89\x00'
        add(h+body,rest=body)
        add(h+body,rest=body,splits=[1]*(len(h)+len(body)))
        for split in range(1,len(h)):
            add(h+body,rest=body,splits=[split,len(h)+len(body)-split])
    for bad in [header(s='HTTP/1.1 401 Unauthorized\r\n'),header(s='HTTP/1.1 101\r\n'),
                header(fields+[fields[0]]),header(fields+[fields[1]]),header(fields+[fields[2]]),
                header(fields+['Sec-WebSocket-Extensions: permessage-deflate']),
                header(fields+['Sec-WebSocket-Protocol: unoffered']),
                header([fields[0],fields[1],'Sec-WebSocket-Accept: wrong']),
                header(['Upgrade: websocketX',*fields[1:]]),
                header([fields[0],'Connection: keep-alive',fields[2]]),
                header([fields[0],'Connection: Upgrade,',fields[2]]),
                header([fields[0],'Connection: Up grade',fields[2]]),
                header([fields[0],' bad: obsfold',*fields[1:]]),
                header([fields[0],'X bad: malformed',*fields[1:]]),
                header([fields[0],fields[1]])]:
        add(bad,0,255)
        add(bad,0,255,splits=[1]*len(bad))
    h=header()
    for split in range(1,len(h)):add(h[:split],255,0)
    fixture=out/'cases.txt';fixture.write_text('\n'.join(records)+'\n')
    subprocess.run(['lake','build','websocket_upgrade_checks'],cwd=ROOT,check=True)
    audit=out/'Audit.lean';audit.write_text('import TlsMpc.TlsWebSocketUpgrade\n'+''.join(
        '#print axioms TlsMpc.TlsWebSocketUpgrade.'+name+'\n' for name in
        ['step_map','feed_map','run_map','runByte_map','compiled_run_correct','compiled_runByte_correct']))
    proof=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,text=True,capture_output=True,check=True)
    (out/'proof.log').write_text(proof.stdout+proof.stderr)
    for line in proof.stdout.splitlines():
        if 'depends on axioms:' in line:
            axioms=line.split('[',1)[1].split(']',1)[0].replace(' ','').split(',')
            assert set(axioms)<=set(['propext','Classical.choice','Quot.sound']),line
    with (out/'checks.log').open('w') as log:
        subprocess.run([str(ROOT/'.lake/build/bin/websocket_upgrade_checks'),str(fixture)],cwd=ROOT,check=True,stdout=log,stderr=subprocess.STDOUT,timeout=900)
    print((out/'checks.log').read_text())
    oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
    probes=[(header()+b'\x82\x04test',True),(header(list(reversed(fields))),True),
      (header([fields[0],fields[1],'Sec-WebSocket-Accept: wrong']),False),
      (header(s='HTTP/1.1 401 Unauthorized\r\n'),False),
      (header([fields[0],'Connection: keep-alive, Upgrade',fields[2]]),False)]
    request=''.join(json.dumps({'mode':'check101','key':'dGhlIHNhbXBsZSBub25jZQ==','wire':raw.hex()})+'\n' for raw,_ in probes)
    actual=subprocess.run([str(oracle)],input=request,text=True,capture_output=True,check=True)
    answers=[json.loads(line) for line in actual.stdout.splitlines()]
    assert len(answers)==len(probes)
    for response,(_,accepted) in zip(answers,probes):assert response['accepted']==accepted,response
    (out/'pinned-oracle.json').write_text(json.dumps(answers,indent=2)+'\n')
    names=['TlsMpc/TlsWebSocketUpgrade.lean','handshake_backend/WebSocketWork/UpgradeFixture.lean',
      'scripts/check_websocket_upgrade.py','lakefile.toml','.lake/build/bin/websocket_upgrade_checks']
    report={'passed':True,'streaming_cases':len(records),'pinned_tungstenite_checks':len(probes),
      'intentional_divergence':'RFC Connection token lists accepted by this parser; pinned client exact-value verifier rejects list',
      'proof_endpoints':['step_map','feed_map','run_map','runByte_map','compiled_run_correct','compiled_runByte_correct'],
      'scope':'bounded algorithm/compilation mapping and public stream fixtures; no full HTTP grammar refinement theorem or native/live TLS evidence',
      'native_mpc_executed':False,'private_bodies_opened':False,'elapsed_seconds':time.monotonic()-started,
      'sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in names},
      'log_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in out.glob('*.log')}}
    (ROOT/'benchmarks/results/tls-websocket-upgrade-checks.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
