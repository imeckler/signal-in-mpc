#!/usr/bin/env python3
"""Public local standard-TLS test of native-frame→actual-service fixture peer."""
import base64,hashlib,json,re,ssl,subprocess,tempfile
from pathlib import Path
from fixture_server import Peer,frame,run_oracle,DEFAULT_ORACLE,DEFAULT_RESPONSE_ORACLE
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
class Client:
 def __init__(self,peer):
  self.peer=peer;context=ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT);context.check_hostname=False;context.verify_mode=ssl.CERT_NONE
  context.minimum_version=context.maximum_version=ssl.TLSVersion.TLSv1_3;context.set_alpn_protocols(['http/1.1'])
  self.input=ssl.MemoryBIO();self.output=ssl.MemoryBIO();self.tls=context.wrap_bio(self.input,self.output,server_side=False,server_hostname='chat.signal.org')
  self.buffer=bytearray();self.upgraded=False;self.messages=[];self.partial=None;self.key=base64.b64encode(bytes(range(16))).decode();self.pings=0;self.pongs=0
  for _ in range(100):
   try:self.tls.do_handshake()
   except ssl.SSLWantReadError:pass
   wire=self.output.read()
   ready,reply=peer.feed(wire)
   if reply:self.input.write(reply)
   if ready:
    try:self.tls.do_handshake();break
    except ssl.SSLWantReadError:pass
  else:raise AssertionError('TLS handshake budget')
 def receive(self,data):
  self.buffer.extend(data)
  if not self.upgraded:
   end=self.buffer.find(b'\r\n\r\n')
   if end<0:return
   answer=run_oracle(DEFAULT_ORACLE,dict(mode='check101',key=self.key,wire=bytes(self.buffer[:end+4]).hex()));assert answer['accepted']
   del self.buffer[:end+4];self.upgraded=True
  while len(self.buffer)>=2:
   b0,b1=self.buffer[:2];assert b0&0x70==0 and b1&128==0;n=b1&127;offset=2
   if n==126:
    if len(self.buffer)<4:return
    n=int.from_bytes(self.buffer[2:4],'big');offset=4;assert n>=126
   assert n<65536
   if len(self.buffer)<offset+n:return
   payload=bytes(self.buffer[offset:offset+n]);del self.buffer[:offset+n];op=b0&15;fin=bool(b0&128)
   if op==9:self.pings+=1;self.tls.write(frame(payload,10,mask=b'1234'));continue
   if op==10:self.pongs+=1;continue
   if op==8:continue
   if op==2:assert not fin and self.partial is None;self.partial=bytearray(payload)
   else:
    assert op==0 and self.partial is not None;self.partial.extend(payload)
    if fin:self.messages.append(bytes(self.partial));self.partial=None
 def pump(self):
  for _ in range(100):
   progress=False;wire=self.output.read()
   if wire:
    progress=True;_,reply=self.peer.feed(wire)
    if reply:self.input.write(reply)
   while True:
    try:
     data=self.tls.read(16384)
     if not data:break
     progress=True;self.receive(data)
    except (ssl.SSLWantReadError,ssl.SSLZeroReturnError):break
   if not progress:return
  raise AssertionError('TLS exchange budget')
 def send(self,data):self.tls.write(data);self.pump()
def decode_frame(wire):
 n=wire[1]&127;offset=2
 if n==126:n=int.from_bytes(wire[2:4],'big');offset=4
 mask=wire[offset:offset+4];assert len(wire)==offset+4+n
 return bytes(x^mask[i%4] for i,x in enumerate(wire[offset+4:]))
def main():
 fixture=json.loads((HERE/'server-fixture.json').read_text());native=json.loads((HERE/'native-report.json').read_text())
 header=(HERE/'PublicFixtureProducer.h').read_text().split('const std::string text=',1)[1].split(';',1)[0]
 initial=''.join(re.findall(r'"([0-9a-f]+)"',header))
 assert initial==(ROOT/native['logs']/'public-fixtures.txt').read_text().splitlines()[0]
 log=(ROOT/native['logs']/'party-0.log').read_text();frames=[bytes.fromhex(line.split()[2]) for line in log.splitlines() if line.startswith('FRAME ')]
 assert len(frames)==2
 with tempfile.TemporaryDirectory(prefix='signal-service-peer-') as directory:
  directory=Path(directory);cert=directory/'cert.pem';key=directory/'key.pem'
  subprocess.run(['openssl','req','-x509','-newkey','rsa:2048','-nodes','-keyout',str(key),'-out',str(cert),'-subj','/CN=chat.signal.org','-days','1'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True)
  # Standard Python TLS client selects its default TLS1.3 cipher. The native
  # controller integration separately enforces AES128 via Peer CLI's default.
  peer=Peer(cert,key,fixture,require_aes128=False);client=Client(peer)
  credentials=(fixture['upgrade_username']+':'+fixture['upgrade_password']).encode()
  request=('GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nAuthorization: Basic '+base64.b64encode(credentials).decode()+'\r\nSec-WebSocket-Key: '+client.key+'\r\nSec-WebSocket-Version: 13\r\n\r\n').encode()
  client.send(request[:53]);assert not peer.upgraded
  client.send(request[53:]);assert peer.upgraded and client.upgraded
  client.send(frames[0]);assert len(client.messages)==1
  payload=decode_frame(frames[1]);fragmented=frame(payload[:31],2,False,b'abcd')+frame(b'cp',9,True,b'efgh')+frame(payload[31:],0,True,b'ijkl')
  for i in range(0,len(fragmented),87):client.send(fragmented[i:i+87])
  assert len(client.messages)==2 and client.pings==3 and client.pongs==1
  answers=[run_oracle(DEFAULT_RESPONSE_ORACLE,dict(wire=p.hex(),expected_id=127+i)) for i,p in enumerate(client.messages)]
  assert all(x['accepted'] and x['correlated'] and x['is_success'] and x['body']=='7b7d' for x in answers)
  client.send(frame((1000).to_bytes(2,'big'),8,mask=b'clos'))
  result=peer.finish();assert result['fragmented_client_requests']==1 and result['client_pings']==1 and result['interleaved_pongs_validated']==3
 files=[Path(__file__),HERE/'fixture_server.py',HERE/'server-fixture.json',HERE/'PublicFixtureProducer.h']
 report={'local_standard_tls13_memory_bio_passed':True,'actual_native_producer_frames_used':True,'native_tls_controller_executed':False,
  'aes128_native_profile_tested':False,'peer_result':result,'no_client_signal_keys_given_to_server':True,'public_helper_initial_matches_native_test':True,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'native_receipt_sha256':hashlib.sha256((HERE/'native-report.json').read_bytes()).hexdigest()}
 (HERE/'server-report.json').write_text(json.dumps(report,indent=2)+'\n');print('Local TLS13/H1/WS peer validated two actual native frames and correlated fragmented responses')
if __name__=='__main__':main()
