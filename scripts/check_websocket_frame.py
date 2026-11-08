#!/usr/bin/env python3
"""Public binary-frame/control/fragmentation cases for the private frame DFA."""
from pathlib import Path
import subprocess,json,hashlib,time
ROOT=Path(__file__).resolve().parents[1]
def frame(op,data=b'',fin=True):
    n=len(data);length=bytes([n]) if n<126 else b'\x7e'+n.to_bytes(2,'big')
    return bytes([(128 if fin else 0)|op])+length+data
def main():
    started=time.monotonic();out=ROOT/'benchmarks/results/raw/websocket-frame';out.mkdir(parents=True,exist_ok=True)
    records=[]
    def add(raw,valid=255,frames=1,messages=1,controls=0,data=b'',control=b''):
        records.append(' '.join([raw.hex() or '-',str(valid),str(frames),str(messages),str(controls),data.hex() or '-',control.hex() or '-']))
    for n in [0,1,2,15,125,126,127,128,255,256,900,4095,4096]:
        data=bytes((i*73+19)%256 for i in range(n));add(frame(2,data),data=data)
    add(frame(2,b'ab',False)+frame(9,b'ping')+frame(0,b'cd'),frames=3,controls=1,data=b'abcd',control=b'ping')
    add(frame(2,b'',False)+frame(10,b'')+frame(0,b'',True),frames=3,controls=1)
    add(frame(9,b'ping')+frame(2,b'body')+frame(10,b'pong'),frames=3,controls=2,data=b'body',control=b'pingpong')
    for reason in [b'',b'normal','snowman \u2603'.encode(),'\U0001f600'.encode()]:
        payload=(1000).to_bytes(2,'big')+reason;add(frame(8,payload),messages=0,controls=1,control=payload)
    add(frame(8),messages=0,controls=1)
    for code in [1001,1002,1003,1007,1014,3000,3071,3072,4863,4864,4999]:
        payload=code.to_bytes(2,'big');add(frame(8,payload),messages=0,controls=1,control=payload)
    for code in [0,999,1004,1005,1006,1015,2000,2999,5000,65535]:add(frame(8,code.to_bytes(2,'big')),0)
    invalid=[frame(0,b'x'),frame(2,b'a',False)+frame(2,b'b'),frame(9,b'x',False),frame(9,bytes(126)),
      b'\x82\x80'+bytes(4),b'\xc2\x00',frame(1,b'text'),frame(3,b'x'),b'\x82\x7e\x00\x7d'+bytes(125),
      b'\x82\x7f'+(65536).to_bytes(8,'big'),frame(8,b'x'),frame(8)+frame(2,b''),
      frame(2,bytes(4097)),frame(2,bytes(3000),False)+frame(0,bytes(2000))]
    invalid += [frame(8,b'\x03\xe8'+reason) for reason in [b'\xc0\x80',b'\xe0\x80\x80',b'\xed\xa0\x80',b'\xf4\x90\x80\x80',b'\xf5\x80\x80\x80',b'\xc2',b'\xe2\x82']]
    for raw in invalid:add(raw,0)
    for raw in [b'\x82',b'\x82\x05ab',b'\x82\x7e\x01',frame(2,b'ab',False)]:
        add(raw,frames=1 if raw.endswith(b'ab') and raw[0]==2 else 0,messages=0,data=b'ab' if raw.endswith(b'ab') else b'')
    fixture=out/'cases.txt';fixture.write_text('\n'.join(records)+'\n')
    subprocess.run(['lake','build','websocket_frame_checks'],cwd=ROOT,check=True)
    with (out/'checks.log').open('w') as log:
        subprocess.run([str(ROOT/'.lake/build/bin/websocket_frame_checks'),str(fixture)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=900)
    audit=out/'Audit.lean';audit.write_text('import TlsMpc.TlsWebSocketFrame\n'+''.join('#print axioms TlsMpc.TlsWebSocketFrame.'+n+'\n' for n in ['step_map','decByte_value','dec_value','runByte_map','compiled_runByte_correct']))
    proof=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,text=True,capture_output=True,check=True)
    (out/'proof.log').write_text(proof.stdout+proof.stderr)
    for line in proof.stdout.splitlines():
        if 'depends on axioms:' in line:assert set(line.split('[',1)[1].split(']',1)[0].replace(' ','').split(','))<=set(['propext','Classical.choice','Quot.sound']),line
    close=frame(8)
    probes=[(frame(2,b'hello')+close,True),
      (frame(2,b'ab',False)+frame(9,b'ping')+frame(0,b'cd')+close,True),
      (frame(2,bytes(126))+close,True),(b'\x82\x80'+bytes(4)+close,False),
      (b'\xc2\x00'+close,False),(frame(8,b'\x03\xe8\xc0\x80'),False),
      (frame(8,(1005).to_bytes(2,'big')),'protocol_close')]
    oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
    actual=subprocess.run([str(oracle)],input=''.join(json.dumps({'mode':'check_ws_frames','wire':raw.hex()})+'\n' for raw,_ in probes),text=True,capture_output=True,check=True)
    responses=[json.loads(line) for line in actual.stdout.splitlines()];assert len(responses)==len(probes)
    for response,(_,accepted) in zip(responses,probes):
        if accepted=='protocol_close':assert response['closed'] and response['messages'][-1]['code']==1002,response
        else:assert response['closed']==accepted,response
    (out/'pinned-oracle.json').write_text(json.dumps(responses,indent=2)+'\n')
    names=['TlsMpc/TlsWebSocketFrame.lean','handshake_backend/WebSocketWork/FrameFixture.lean','scripts/check_websocket_frame.py','lakefile.toml','.lake/build/bin/websocket_frame_checks']
    report={'passed':True,'cases':len(records),'pinned_tungstenite_cases':len(probes),'native_mpc_executed':False,
      'scope':'private frame algorithm tests and map/kernel byte-decrement proofs; no full frame refinement theorem, native or TLS integration yet',
      'intentional_divergence':'invalid close code rejected directly; pinned tungstenite converts it to protocol-violation close1002',
      'elapsed_seconds':time.monotonic()-started,'sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names}}
    (ROOT/'benchmarks/results/tls-websocket-frame-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print((out/'checks.log').read_text())
if __name__=='__main__':main()
