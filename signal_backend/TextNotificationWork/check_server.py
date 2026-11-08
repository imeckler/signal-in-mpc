#!/usr/bin/env python3
"""PUBLIC standard TLS test of 4 text sends, actual recipient, reordered replies."""
import base64,hashlib,importlib.util,json,ssl,subprocess,sys,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'signal_backend/VariableServiceWork'))
from check_fixture_server import Client
spec=importlib.util.spec_from_file_location('signal_text_fixture_server',HERE/'fixture_server.py')
server=importlib.util.module_from_spec(spec);spec.loader.exec_module(server)
base=server.base

def request(c,step,slot,request_id):
 sealed=base.run_oracle(base.DEFAULT_ORACLE,dict(mode='sealed',seed=slot,inner=c['expected_inner'][step]))['wire']
 body={'messages':[{'type':6,'destinationDeviceId':c['device_id'],'destinationRegistrationId':c['registration_id'],'content':base64.b64encode(bytes.fromhex(sealed)).decode()}],
  'online':False,'urgent':True,'timestamp':c['timestamps'][step]}
 payload=base.field(10,b'PUT')+base.field(18,('/v1/messages/'+c['recipient_uuid']+'?story=false').encode())+base.field(26,json.dumps(body,separators=(',',':')).encode())+b'\x20'+base.varint(request_id)+base.field(42,b'content-type: application/json')+base.field(42,b'unidentified-access-key: '+base64.b64encode(bytes.fromhex(c['access_key'])))
 return base.frame(b'\x08\x01'+base.field(18,payload),mask=b'abcd')
def main():
 fixture=json.loads((HERE/'server-fixtures.json').read_text());assert all('initial'not in c for c in fixture['conversations'])
 with tempfile.TemporaryDirectory(prefix='signal-text-server-')as directory:
  directory=Path(directory);cert=directory/'cert.pem';key=directory/'key.pem'
  subprocess.run(['openssl','req','-x509','-newkey','rsa:2048','-nodes','-keyout',str(key),'-out',str(cert),'-subj','/CN=chat.signal.org','-days','1'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True)
  peer=server.TextPeer(cert,key,fixture,require_aes128=False,batch=2)
  try:
   client=Client(peer);credentials=(fixture['upgrade_username']+':'+fixture['upgrade_password']).encode()
   upgrade=('GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nAuthorization: Basic '+base64.b64encode(credentials).decode()+'\r\nSec-WebSocket-Key: '+client.key+'\r\nSec-WebSocket-Version: 13\r\n\r\n').encode()
   client.send(upgrade[:53]);client.send(upgrade[53:]);assert peer.upgraded and client.upgraded
   expected=[];id_base=2**63+0x123456789
   for step in range(2):
    for slot in range(2):
     wire=request(fixture['conversations'][slot],step,slot,id_base+2*step+slot)
     # Arbitrary TLS chunk boundaries include extended WS length/mask/payload.
     for i in range(0,len(wire),87):client.send(wire[i:i+87])
    expected.extend([id_base+2*step+1,id_base+2*step])
    assert len(client.messages)==2*(step+1)
   assert peer.response_order==expected and client.pings==5
   for wire,request_id in zip(client.messages,expected):
    answer=base.run_oracle(base.DEFAULT_RESPONSE_ORACLE,dict(wire=wire.hex(),expected_id=request_id));assert answer['accepted']and answer['correlated']and answer['is_success']
   report=peer.finish()
  finally:peer.close_recipient()
 files=[Path(__file__),HERE/'fixture_server.py',HERE/'server-fixtures.json',HERE/'PublicTextFixture.h',HERE/'prepare_fixtures.py',ROOT/'signal_backend/Oracle/src/bin/signal-text-recipient-oracle.rs']
 report.update(standard_local_TLS_only=True,native_MPC_executed_here=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'server-report.json').write_text(json.dumps(report,indent=2)+'\n');print('4 nonempty text requests through ordinary TLS/WS and actual recipient session; reversed response pairs passed',flush=True)
if __name__=='__main__':main()
