#!/usr/bin/env python3
"""PUBLIC DISPOSABLE FIXTURE ONLY: TLS1.3/H1/WS over a memory-BIO line channel.
No live network/account operations. Server receives only disposable recipient
keys and expected public message wires, never client identity/chain shares.
"""
import argparse,base64,json,ssl,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
DEFAULT_ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
DEFAULT_RESPONSE_ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-chat-response-oracle'
def varint(n):
 b=bytearray()
 while n>127:b.append((n&127)|128);n>>=7
 b.append(n);return bytes(b)
def field(tag,payload):return bytes([tag])+varint(len(payload))+payload
def frame(payload,opcode=2,fin=True,mask=None):
 n=len(payload);assert n<65536
 h=bytes([(128 if fin else 0)|opcode])+(bytes([(128 if mask else 0)|n]) if n<126 else bytes([(128 if mask else 0)|126])+n.to_bytes(2,'big'))
 if mask is None:return h+payload
 assert len(mask)==4
 return h+mask+bytes(x^mask[i%4] for i,x in enumerate(payload))
def run_oracle(path,row):
 r=subprocess.run([str(path)],input=json.dumps(row)+'\n',text=True,capture_output=True,check=True)
 lines=r.stdout.splitlines();assert len(lines)==1,'oracle response framing'
 return json.loads(lines[0])
class Peer:
 def __init__(self,cert,key,fixture,oracle=DEFAULT_ORACLE,response_oracle=DEFAULT_RESPONSE_ORACLE,fragment=127,require_aes128=True):
  assert 8<=fragment<=127
  self.fixture=fixture;self.oracle=oracle;self.response_oracle=response_oracle;self.fragment=fragment;self.require_aes128=require_aes128
  context=ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER);context.minimum_version=context.maximum_version=ssl.TLSVersion.TLSv1_3
  context.load_cert_chain(cert,key);context.set_alpn_protocols(['http/1.1']);context.set_ecdh_curve('X25519');context.num_tickets=0
  self.incoming=ssl.MemoryBIO();self.outgoing=ssl.MemoryBIO();self.tls=context.wrap_bio(self.incoming,self.outgoing,server_side=True)
  self.ready=False;self.upgraded=False;self.closed=False;self.buffer=bytearray();self.fragments=None;self.pending_pings=[]
  self.requests=0;self.pongs=0;self.fragmented_requests=0;self.client_pings=0
 def write_app(self,data):
  assert len(data)<=self.fragment
  assert self.tls.write(data)==len(data),'TLS write failed'
 def ping(self,data):self.pending_pings.append(data);return frame(data,9)
 def upgrade(self):
  end=self.buffer.find(b'\r\n\r\n')
  if end<0:assert len(self.buffer)<=8192,'HTTP header capacity';return False
  request=bytes(self.buffer[:end+4]);del self.buffer[:end+4]
  answer=run_oracle(self.oracle,dict(mode='upgrade',wire=request.hex()))
  expected=(self.fixture['upgrade_username']+':'+self.fixture['upgrade_password']).encode()
  assert answer['status']==101 and bytes.fromhex(answer['credentials'])==expected,'fixture HTTP authentication failed'
  response=('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: '+answer['accept']+'\r\n\r\n').encode()
  ping=self.ping(b'u0')
  # Exact HTTP terminator + first WS control can share one authenticated chunk.
  while len(response)>self.fragment-len(ping):self.write_app(response[:self.fragment]);response=response[self.fragment:]
  self.write_app(response+ping);self.upgraded=True;return True
 def handle_binary(self,payload):
  assert self.requests<len(self.fixture['expected_inner']),'unexpected extra request'
  # Actual generated protobuf + JSON/base64 decoder. The harness reconstructs
  # one normalized masked frame after independently validating fragmentation.
  answer=run_oracle(self.oracle,dict(mode='relay',wire=frame(payload,mask=bytes(4)).hex()))
  f=self.fixture;body=answer['body'];messages=body['messages'];assert len(messages)==1
  assert answer['path']=='/v1/messages/'+f['recipient_uuid']+'?story=false' and answer['access_key']==f['access_key'],'recipient/access binding'
  assert answer['id']==f['request_ids'][self.requests],'request ID progression'
  assert body['online'] is False and body['urgent'] is True and body['timestamp']==f['timestamp'],'request flags/timestamp'
  message=messages[0];assert message['type']==6 and message['destinationDeviceId']==f['device_id'] and message['destinationRegistrationId']==f['registration_id'],'device metadata'
  decoded=run_oracle(self.oracle,dict(mode='sealed_decrypt',wire=answer['ciphertext'],recipient_secret=f['recipient_secret'],root_public=f['root_public']))
  assert decoded==dict(inner=f['expected_inner'][self.requests],certificate_valid=True),'actual sealed/inner verification'
  response=b'\x08'+varint(answer['id'])+b'\x10'+varint(200)+field(26,b'OK')+field(34,b'{}')+field(42,b'content-type: application/json')
  payload=b'\x08\x02'+field(26,response)
  checked=run_oracle(self.response_oracle,dict(wire=payload.hex(),expected_id=answer['id']))
  assert checked['accepted'] and checked['correlated'] and checked['is_success'],'response construction'
  # Fragment binary response around an interleaved ping. No fabricated client
  # parser result or decrypted client shares are accepted by this server.
  ping=self.ping(('r'+str(self.requests)).encode())
  self.write_app(frame(payload[:3],2,False)+ping)
  rest=payload[3:]
  while len(rest)>self.fragment-2:self.write_app(frame(rest[:self.fragment-2],0,False));rest=rest[self.fragment-2:]
  self.write_app(frame(rest,0,True));self.requests+=1
 def parse_frames(self):
  while len(self.buffer)>=2:
   first,second=self.buffer[:2];assert first&0x70==0,'RSV bits';opcode=first&15;fin=bool(first&128)
   assert second&128,'unmasked client frame';n=second&127;offset=2
   if n==127:raise AssertionError('64-bit frame length outside bounded fixture')
   if n==126:
    if len(self.buffer)<4:return
    n=int.from_bytes(self.buffer[2:4],'big');offset=4;assert n>=126,'noncanonical length'
   assert n<=16384 and opcode in [0,2,8,9,10],'frame domain'
   if opcode>=8:assert fin and n<=125,'fragmented/oversized control'
   if len(self.buffer)<offset+4+n:return
   mask=self.buffer[offset:offset+4];payload=bytes(x^mask[i%4] for i,x in enumerate(self.buffer[offset+4:offset+4+n]));del self.buffer[:offset+4+n]
   if opcode==10:
    if payload in self.pending_pings:self.pending_pings.remove(payload);self.pongs+=1
    continue
   if opcode==9:self.client_pings+=1;self.write_app(frame(payload,10));continue
   if opcode==8:
    assert len(payload)!=1,'short close'
    if payload:
     code=int.from_bytes(payload[:2],'big');assert code in [1000,1001,1002,1003,1007,1008,1009,1010,1011,1012,1013,1014] or 3000<=code<5000,'close code'
     payload[2:].decode('utf-8')
    self.write_app(frame(payload,8));self.closed=True;return
   assert not self.closed,'data after close'
   if opcode==2:
    assert self.fragments is None,'new data during fragment'
    if fin:self.handle_binary(payload)
    else:self.fragments=bytearray(payload);self.fragmented_requests+=1
   else:
    assert self.fragments is not None,'unexpected continuation';self.fragments.extend(payload);assert len(self.fragments)<=16384,'message capacity'
    if fin:payload=bytes(self.fragments);self.fragments=None;self.handle_binary(payload)
 def plaintext(self,data):
  self.buffer.extend(data)
  if not self.upgraded and not self.upgrade():return
  self.parse_frames()
 def feed(self,data):
  if data:self.incoming.write(data)
  if not self.ready:
   try:
    self.tls.do_handshake();self.ready=True
    assert self.tls.version()=='TLSv1.3' and self.tls.selected_alpn_protocol()=='http/1.1','TLS profile'
    if self.require_aes128:assert self.tls.cipher()[0]=='TLS_AES_128_GCM_SHA256','TLS AES128 profile'
   except (ssl.SSLWantReadError,ssl.SSLWantWriteError):pass
  if self.ready:
   while True:
    try:
     plain=self.tls.read(16384)
     if not plain:break
     self.plaintext(plain)
    except (ssl.SSLWantReadError,ssl.SSLWantWriteError,ssl.SSLZeroReturnError):break
  return self.ready,self.outgoing.read()
 def finish(self):
  assert self.upgraded and self.requests==2 and not self.pending_pings and self.fragments is None,'incomplete fixture exchange'
  return dict(tls13_h1=True,upgrade_authenticated=True,upgrade_split_and_ws_coalesced=True,requests_validated=self.requests,
   actual_sealed_decrypt_certificate_and_inner_verified=True,response_ids_copied=True,response_binary_fragmentation=True,
   interleaved_pongs_validated=self.pongs,client_pings=self.client_pings,fragmented_client_requests=self.fragmented_requests,
   client_signal_key_inputs=False,live_account_side_effects=False)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('cert');parser.add_argument('key');parser.add_argument('fragment',nargs='?',type=int,default=127);parser.add_argument('request_cert',nargs='?',default='no');parser.add_argument('alpn',nargs='?',default='http/1.1')
 parser.add_argument('--fixture',type=Path,default=HERE/'server-fixture.json');parser.add_argument('--oracle',type=Path,default=DEFAULT_ORACLE);parser.add_argument('--response-oracle',type=Path,default=DEFAULT_RESPONSE_ORACLE);parser.add_argument('--report',type=Path)
 args=parser.parse_args();assert args.request_cert=='no' and args.alpn=='http/1.1','fixture H1/no client-certificate only'
 peer=Peer(args.cert,args.key,json.loads(args.fixture.read_text()),args.oracle,args.response_oracle,args.fragment)
 for line in sys.stdin:
  line=line.strip()
  if line=='quit':
   report=peer.finish()
   if args.report:args.report.write_text(json.dumps(report,indent=2)+'\n')
   return
  ready,output=peer.feed(bytes.fromhex(line) if line!='-' else b'')
  print(('ready ' if ready else 'waiting ')+(output.hex() if output else '-'),flush=True)
 raise AssertionError('fixture closed without completion command')
if __name__=='__main__':
 try:main()
 except Exception:
  print('protocol fixture failed',file=sys.stderr);sys.exit(1)
