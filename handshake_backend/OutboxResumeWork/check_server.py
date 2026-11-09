#!/usr/bin/env python3
"""Ordinary local TLS smoke; actual serialized receiver replay/text, no MPC."""
import argparse,base64,hashlib,importlib.util,json,os,pathlib,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'signal_backend/VariableServiceWork'));import check_fixture_server as client_module
# Every prepared client frame, including automatic control replies, uses a fresh
# unpredictable mask. Only this test module's imported helper is replaced.
original_frame=client_module.frame
def fresh_frame(payload,opcode=2,fin=True,mask=None):return original_frame(payload,opcode,fin,os.urandom(4)if mask is not None else None)
client_module.frame=fresh_frame
spec=importlib.util.spec_from_file_location('restored_fixture_server',HERE/'fixture_server.py');server=importlib.util.module_from_spec(spec);spec.loader.exec_module(server);base=server.base
def request(c,event,request_id):
 body={'messages':[{'type':6,'destinationDeviceId':c['device_id'],'destinationRegistrationId':c['registration_id'],'content':base64.b64encode(bytes.fromhex(event['sealed_wire'])).decode()}],'online':False,'urgent':True,'timestamp':event['timestamp']}
 payload=base.field(10,b'PUT')+base.field(18,('/v1/messages/'+c['recipient_uuid']+'?story=false').encode())+base.field(26,json.dumps(body,separators=(',',':')).encode())+b'\x20'+base.varint(request_id)+base.field(42,b'content-type: application/json')+base.field(42,b'unidentified-access-key: '+base64.b64encode(bytes.fromhex(c['access_key'])))
 return base.frame(b'\x08\x01'+base.field(18,payload),mask=os.urandom(4))
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--fixture',type=pathlib.Path,required=True);parser.add_argument('--recipient',type=pathlib.Path,default=server.DEFAULT_RECIPIENT);args=parser.parse_args();fixture=json.loads(args.fixture.read_text())
 with tempfile.TemporaryDirectory(prefix='tls-restored-server-')as directory:
  directory=pathlib.Path(directory);cert=directory/'cert.pem';key=directory/'key.pem';subprocess.run(['openssl','req','-x509','-newkey','rsa:2048','-nodes','-keyout',str(key),'-out',str(cert),'-subj','/CN=chat.signal.org','-days','1'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True)
  peer=server.RestoredPeer(cert,key,fixture,recipient=args.recipient,require_aes128=False)
  try:
   client=client_module.Client(peer);credentials=fixture['client_uuid'].encode()+b':'+bytes.fromhex(fixture['client_password_hex'])
   upgrade=('GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nAuthorization: Basic '+base64.b64encode(credentials).decode()+'\r\nSec-WebSocket-Key: '+client.key+'\r\nSec-WebSocket-Version: 13\r\n\r\n').encode()
   client.send(upgrade[:53]);client.send(upgrade[53:]);assert peer.upgraded and client.upgraded
   expected=[];request_id=2**63+0x5abcd
   for step in range(max(len(c['events'])for c in fixture['conversations'])):
    for c in fixture['conversations']:
     if step>=len(c['events']):continue
     event=c['events'][step];wire=request(c,event,request_id)
     for start in range(0,len(wire),87):client.send(wire[start:start+87])
     expected.append(request_id);request_id+=1
   assert peer.response_ids==expected and len(client.messages)==len(expected)
   for payload,wanted in zip(client.messages,expected):
    answer=base.run_oracle(base.DEFAULT_RESPONSE_ORACLE,dict(wire=payload.hex(),expected_id=wanted));assert answer['accepted']and answer['correlated']and answer['is_success']
   result=peer.finish()
  finally:peer.close_recipient()
 files=[pathlib.Path(__file__),HERE/'fixture_server.py',args.fixture,args.recipient,ROOT/'signal_backend/VariableServiceWork/fixture_server.py',ROOT/'signal_backend/VariableServiceWork/check_fixture_server.py']
 result.update(standard_TLS_smoke_only=True,aes128_native_profile_tested=False,native_tls_controller_executed=False,source_sha256={str(p.resolve().relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'server-report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['actual_recipient_replay_rejections','fresh_texts_decrypted','service_acceptance_for_duplicate','unique_recipient_delivery_for_resumed']}))
if __name__=='__main__':main()
