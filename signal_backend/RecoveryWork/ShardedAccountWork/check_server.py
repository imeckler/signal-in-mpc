#!/usr/bin/env python3
"""Ordinary TLS peer preflight: cut + replay/continued ten texts; no MPC."""
import base64,hashlib,importlib.util,json,os,pathlib,subprocess,sys,tempfile
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'signal_backend/VariableServiceWork'));import check_fixture_server as client_module
original_frame=client_module.frame
def fresh_frame(payload,opcode=2,fin=True,mask=None):return original_frame(payload,opcode,fin,os.urandom(4)if mask is not None else None)
client_module.frame=fresh_frame
spec=importlib.util.spec_from_file_location('sharded_peer_smoke',HERE/'fixture_server.py');server=importlib.util.module_from_spec(spec);spec.loader.exec_module(server);base=server.base

def request(c,event,ident):
 body={'messages':[{'type':6,'destinationDeviceId':c['device_id'],'destinationRegistrationId':c['registration_id'],'content':base64.b64encode(bytes.fromhex(event['sealed_wire'])).decode()}],'online':False,'urgent':True,'timestamp':event['timestamp']}
 payload=base.field(10,b'PUT')+base.field(18,('/v1/messages/'+c['recipient_uuid']+'?story=false').encode())+base.field(26,json.dumps(body,separators=(',',':')).encode())+b'\x20'+base.varint(ident)+base.field(42,b'content-type: application/json')+base.field(42,b'unidentified-access-key: '+base64.b64encode(bytes.fromhex(c['access_key'])))
 return base.frame(b'\x08\x01'+base.field(18,payload),mask=os.urandom(4))
def upgrade(client,fixture):
 auth=base64.b64encode(fixture['client_uuid'].encode()+b':'+bytes.fromhex(fixture['client_password_hex'])).decode();wire=('GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nAuthorization: Basic '+auth+'\r\nSec-WebSocket-Key: '+client.key+'\r\nSec-WebSocket-Version: 13\r\n\r\n').encode();client.send(wire[:53]);client.send(wire[53:]);assert client.upgraded
def main():
 cut=json.loads((HERE/'peer-cut.json').read_text());restored=json.loads((HERE/'peer-restored.json').read_text());reports=[];first=2**63+0x990000
 with tempfile.TemporaryDirectory(prefix='sharded-peer-')as tmp:
  tmp=pathlib.Path(tmp);cert=tmp/'cert.pem';key=tmp/'key.pem';subprocess.run(['openssl','req','-x509','-newkey','rsa:2048','-nodes','-keyout',str(key),'-out',str(cert),'-subj','/CN=chat.signal.org','-days','1'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True)
  peer=server.Peer(cert,key,cut,'cut',require_aes128=False)
  try:
   client=client_module.Client(peer);upgrade(client,cut)
   for slot in [0,1]:client.send(request(cut['conversations'][slot],cut['conversations'][slot]['events'][0],first+slot))
   assert len(client.messages)==1;answer=base.run_oracle(base.DEFAULT_RESPONSE_ORACLE,dict(wire=client.messages[0].hex(),expected_id=first+1));assert answer['accepted']and answer['correlated'];reports.append(peer.finish())
  finally:peer.close_recipient()
  expected=reports[0]['application_sha256']['0'];peer=server.Peer(cert,key,restored,'restored',require_aes128=False,expected_resume=expected)
  try:
   client=client_module.Client(peer);upgrade(client,restored);steps=[0,0]
   def send(slot,ident):
    c=restored['conversations'][slot];event=c['events'][steps[slot]];wire=request(c,event,ident);steps[slot]+=1
    for start in range(0,len(wire),87):client.send(wire[start:start+87])
   send(0,first);ident=first+2
   for group in [[0],[0],[1],[0,1],[0],[1],[0,1],[1]]:
    for slot in group:send(slot,ident);ident+=1
   assert len(client.messages)==11;reports.append(peer.finish())
  finally:peer.close_recipient()
 files=[pathlib.Path(__file__),HERE/'fixture_server.py',HERE/'peer-cut.json',HERE/'peer-restored.json',ROOT/'signal_backend/Oracle/src/bin/signal-sharded-peer-fixture-oracle.rs']
 result=dict(passed=True,standard_TLS_only=True,native_MPC=False,native_AES128_profile_tested=False,actual_recipient_fresh_texts=12,actual_replay_rejections=1,cut_withheld0_acknowledged1=True,restored_reordered_pairs=2,original_application_bytes_and_ID_preserved=True,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files},cases=reports);(HERE/'server-report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ['source_sha256','cases']},indent=2))
if __name__=='__main__':main()
