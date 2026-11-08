#!/usr/bin/env python3
"""Actual prost response semantics + explicit copied target validator boundary."""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-chat-response-oracle'
def varint(n):
 out=bytearray()
 while n>127:out.append((n&127)|128);n>>=7
 out.append(n);return bytes(out)
def field(tag,data):return bytes([tag])+varint(len(data))+data
def message(response,extra=b''):return b'\x08\x02'+field(26,response)+extra
def main():
 id=b'\x08'+varint(127);status=b'\x10'+varint(200)
 good=id+status+field(42,b'X-test:  ok\t')+field(34,b'\x00abc')
 cases=[message(good),message(id),message(status),message(good,field(18,b'')),message(id+b'\x10'+varint(70000)),
  message(id+b'\x10'+varint(999)),message(id+status+field(42,b'bad name: value')),message(id+status+field(26,b'\xff')),
  message(id+status+b'\x10'+varint(201)),message(id+status+field(34,b'')),message(id+b'\x10'+varint(404)),message(id+status+field(26,b'first')+field(26,'last🙂'.encode()))]
 output=subprocess.run([str(ORACLE)],input=''.join(json.dumps(dict(wire=b.hex(),expected_id=127))+'\n' for b in cases),text=True,capture_output=True,check=True)
 values=[json.loads(x) for x in output.stdout.splitlines()]
 assert [v['accepted'] for v in values]==[True,False,False,False,False,True,False,False,True,True,True,True]
 assert values[0]['body']=='00616263' and values[0]['correlated'] and values[0]['is_success']
 assert values[5]['status']==999 and not values[5]['is_success']
 assert values[8]['status']==201 and values[9]['body_present'] and values[9]['body']==''
 assert not values[10]['is_success']
 assert values[11]['message_present'] and values[11]['message_hex']=='last🙂'.encode().hex()
 files=[Path(__file__),ROOT/'signal_backend/Oracle/src/bin/signal-chat-response-oracle.rs',ROOT/'signal_backend/Oracle/build.rs',ROOT/'.deps/libsignal-v0.106.1/rust/net/src/chat.rs',ROOT/'.deps/libsignal-v0.106.1/rust/net/src/chat/ws.rs',ROOT/'.deps/libsignal-v0.106.1/rust/net/src/proto/chat_websocket.proto']
 report={'cases':len(cases),'actual_generated_prost_decoder':True,'actual_private_net_conversion_api_called':False,
  'validation_boundary':'Explicit copied inspected chat/ws.rs envelope/id checks and chat.rs HTTP status/header conversion, using actual http types.',
  'network_side_effects':False,'results':values,'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
  'oracle_sha256':hashlib.sha256(ORACLE.read_bytes()).hexdigest()}
 Path(__file__).with_name('chat-response-report.json').write_text(json.dumps(report,indent=2)+'\n');print('12 public response decoder/copied-validation fixtures passed')
if __name__=='__main__':main()
