#!/usr/bin/env python3
"""Public in-memory handshake fixtures against pinned tungstenite client."""
import base64,hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def main():
 key='dGhlIHNhbXBsZSBub25jZQ=='
 accept=base64.b64encode(hashlib.sha1((key+'258EAFA5-E914-47DA-95CA-C5AB0DC85B11').encode()).digest()).decode()
 good=f'HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: {accept}\r\n\r\n'
 cases=[good,good.replace(accept,'wrong'),good.replace('101','200'),good.replace('Connection: Upgrade','Connection: keep-alive, Upgrade'),good+'\x82\x00']
 result=subprocess.run([str(ORACLE)],input=''.join(json.dumps(dict(mode='check101',key=key,wire=w.encode().hex()))+'\n' for w in cases),text=True,capture_output=True,check=True)
 answers=[json.loads(x) for x in result.stdout.splitlines()]
 assert [x['accepted'] for x in answers]==[True,False,False,False,True]
 files=[Path(__file__),ROOT/'signal_backend/Oracle/src/relay.rs',ROOT/'signal_backend/Oracle/src/main.rs',ROOT/'signal_backend/Oracle/Cargo.lock']
 report={'actual_tungstenite_client':True,'network_side_effects':False,'cases':answers,
  'connection_token_lists':'Pinned client rejects; RFC token-list acceptance is a separate deliberate implementation choice.',
  'private_validator_proved':False,'oracle_sha256':hashlib.sha256(ORACLE.read_bytes()).hexdigest(),
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 Path(__file__).with_name('check101-report.json').write_text(json.dumps(report,indent=2)+'\n')
 print('5 pinned-client HTTP101 fixtures passed')
if __name__=='__main__':main()
