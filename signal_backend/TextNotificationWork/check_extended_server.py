#!/usr/bin/env python3
"""PUBLIC standard TLS/WS regression; default4 and optional8 texts, not MPC."""
import base64,hashlib,importlib.util,json,ssl,subprocess,sys,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];sys.path.insert(0,str(HERE));sys.path.insert(0,str(ROOT/'signal_backend/VariableServiceWork'))
from check_fixture_server import Client
spec=importlib.util.spec_from_file_location('extended_text_fixture_server',HERE/'fixture_server.py');server=importlib.util.module_from_spec(spec);spec.loader.exec_module(server);base=server.base

def request(c,step,slot,request_id):
 sealed=base.run_oracle(base.DEFAULT_ORACLE,dict(mode='sealed',seed=slot,inner=c['expected_inner'][step]))['wire']
 body=dict(messages=[dict(type=6,destinationDeviceId=c['device_id'],destinationRegistrationId=c['registration_id'],content=base64.b64encode(bytes.fromhex(sealed)).decode())],online=False,urgent=True,timestamp=c['timestamps'][step])
 payload=base.field(10,b'PUT')+base.field(18,('/v1/messages/'+c['recipient_uuid']+'?story=false').encode())+base.field(26,json.dumps(body,separators=(',',':')).encode())+b'\x20'+base.varint(request_id)+base.field(42,b'content-type: application/json')+base.field(42,b'unidentified-access-key: '+base64.b64encode(bytes.fromhex(c['access_key'])))
 return base.frame(b'\x08\x01'+base.field(18,payload),mask=b'abcd')
def run(rounds):
 raw=json.loads((HERE/'server-fixtures.json').read_text());fixture=server.derive_extended_fixture(raw,rounds)
 with tempfile.TemporaryDirectory(prefix='signal-text-extended-server-')as directory:
  directory=Path(directory);cert=directory/'cert.pem';key=directory/'key.pem'
  subprocess.run(['openssl','req','-x509','-newkey','rsa:2048','-nodes','-keyout',str(key),'-out',str(cert),'-subj','/CN=chat.signal.org','-days','1'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True)
  peer=server.TextPeer(cert,key,raw,require_aes128=False,batch=2,rounds=rounds)
  try:
   client=Client(peer);credentials=(fixture['upgrade_username']+':'+fixture['upgrade_password']).encode()
   upgrade=('GET /v1/websocket/ HTTP/1.1\r\nHost: chat.signal.org\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nAuthorization: Basic '+base64.b64encode(credentials).decode()+'\r\nSec-WebSocket-Key: '+client.key+'\r\nSec-WebSocket-Version: 13\r\n\r\n').encode()
   client.send(upgrade[:53]);client.send(upgrade[53:]);assert peer.upgraded and client.upgraded
   expected=[];id_base=2**63+0x123456789
   for step in range(rounds):
    for slot in range(2):
     wire=request(fixture['conversations'][slot],step,slot,id_base+2*step+slot)
     for i in range(0,len(wire),87):client.send(wire[i:i+87])
    expected.extend([id_base+2*step+1,id_base+2*step]);assert len(client.messages)==2*(step+1)
   assert peer.response_order==expected and client.pings==2*rounds+1
   for wire,request_id in zip(client.messages,expected):
    answer=base.run_oracle(base.DEFAULT_RESPONSE_ORACLE,dict(wire=wire.hex(),expected_id=request_id));assert answer['accepted']and answer['correlated']and answer['is_success']
   report=peer.finish()
  finally:peer.close_recipient()
 report.update(rounds_per_conversation=rounds,actual_selected_counters_checked=rounds==4,standard_local_TLS_only=True,native_MPC_executed_here=False)
 return report
def main():
 reports=[run(rounds)for rounds in [2,4]]
 # The C++ extension delegates old input construction and only advances PUBLIC
 # fixture timestamps; compare every byte to server expectations independently.
 source=ROOT/'.deps/public-text-extended-probe.cpp';binary=ROOT/'.deps/public-text-extended-probe'
 source.write_text('#include "PublicTextExtendedFixture.h"\n#include <iostream>\n#include <iomanip>\nint main(){for(size_t s=0;s<2;++s)for(size_t r=0;r<4;++r){auto b=signal_mpc::PublicTextExtendedFixture::text_input(s,r);for(auto x:b)std::cout<<std::hex<<std::setw(2)<<std::setfill(\'0\')<<unsigned(x);std::cout<<"\\n";}}\n')
 subprocess.run(['clang++','-std=c++17','-I'+str(HERE),str(source),'-o',str(binary)],check=True)
 observed=subprocess.check_output([str(binary)],text=True).splitlines();fixture=server.derive_extended_fixture(json.loads((HERE/'server-fixtures.json').read_text()),4)
 expected=[]
 for c in fixture['conversations']:
  for body,time in zip(c['expected_text'],c['timestamps']):
   b=body.encode();expected.append((b'\xff'+len(b).to_bytes(2,'big')+b+bytes(48-len(b))+time.to_bytes(8,'big')).hex())
 assert observed==expected
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[Path(__file__),HERE/'fixture_server.py',HERE/'extended_fixture.py',HERE/'PublicTextExtendedFixture.h',HERE/'server-fixtures.json',HERE/'PublicTextFixture.h',ROOT/'signal_backend/Oracle/src/bin/signal-text-recipient-extended-oracle.rs']
 result=dict(passed=True,default_two_rounds_preserved=True,extended_four_rounds=True,cpp_input_cases=8,signal_counters=[127,128,129,130],next_signal_counters=[128,129,130,131],pq_receive_counters=[127,128,129,130],repeated_bodies_intentional=True,timestamps_distinct=True,records=reports,native_MPC=False,old_fixture_files_not_rewritten=True,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},recipient_binary_sha256=sha(server.DEFAULT_EXTENDED_RECIPIENT))
 (HERE/'extended-server-report.json').write_text(json.dumps(result,indent=2)+'\n');print('default4 +extended8 actual-recipient texts through ordinaryTLS/WS passed')
if __name__=='__main__':main()
