#!/usr/bin/env python3
"""Local PUBLIC fixture TLS server/actual recipient; no deployed account calls.
Receiver fixture has only receiving-side session state and disposable recipient
identity. Sender initialization/private identity and final cipher/MAC keys are
absent. Ordinary SSL owns only its local endpoint transport keys.
"""
import argparse,importlib.util,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('signal_variable_fixture_server',ROOT/'signal_backend/VariableServiceWork/fixture_server.py')
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
DEFAULT_RECIPIENT=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-text-recipient-oracle'
class TextPeer(base.Peer):
 def __init__(self,*args,recipient=DEFAULT_RECIPIENT,batch=2,**kwargs):
  super().__init__(*args,**kwargs);assert batch in [1,2];self.batch=batch
  assert len(self.fixture['conversations'])==2
  self.steps=[0,0];self.response_queue=[];self.response_order=[];self.request_base=None
  self.recipient=subprocess.Popen([str(recipient)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,text=True)
  try:
   for slot,c in enumerate(self.fixture['conversations']):
    assert 'initial'not in c
    assert self.recipient_call(dict(mode='init',slot=slot,receiving_state=c['receiving_state'],recipient_secret=c['recipient_secret']))=={'initialized':True}
  except BaseException:
   self.close_recipient();raise
 def recipient_call(self,row):
  self.recipient.stdin.write(json.dumps(row)+'\n');self.recipient.stdin.flush()
  return json.loads(self.recipient.stdout.readline())
 def handle_binary(self,payload):
  base.stage('relay_oracle')
  answer=base.run_oracle(self.oracle,dict(mode='relay',wire=base.frame(payload,mask=bytes(4)).hex()))
  base.stage('relay_binding')
  matches=[(slot,c)for slot,c in enumerate(self.fixture['conversations'])if answer['path']=='/v1/messages/'+c['recipient_uuid']+'?story=false']
  assert len(matches)==1;slot,c=matches[0];step=self.steps[slot];assert step<2
  body=answer['body'];assert answer['access_key']==c['access_key']
  if self.request_base is None:
   self.request_base=answer['id'];assert 2**63<=self.request_base<=2**64-5
  assert answer['id']==self.request_base+self.requests
  assert body['timestamp']==c['timestamps'][step] and body['online']is False and body['urgent']is True
  assert len(body['messages'])==1;message=body['messages'][0]
  assert message['type']==6 and message['destinationDeviceId']==c['device_id'] and message['destinationRegistrationId']==c['registration_id']
  base.stage('sealed_oracle')
  decoded=base.run_oracle(self.oracle,dict(mode='sealed_decrypt',wire=answer['ciphertext'],recipient_secret=c['recipient_secret'],root_public=c['root_public']))
  base.stage('sealed_verification')
  assert decoded==dict(inner=c['expected_inner'][step],certificate_valid=True)
  # Actual retained receiver SessionRecord derives both Signal and SPQR keys,
  # verifies Signal MAC and decrypts, then actual Content/minimal DataMessage.
  recovered=self.recipient_call(dict(slot=slot,wire=decoded['inner']))
  assert recovered==dict(accepted=True,body=c['expected_text'][step],timestamp=c['timestamps'][step],padded_bytes=80)
  self.steps[slot]+=1;self.requests+=1;self.response_queue.append(answer['id'])
  if len(self.response_queue)==self.batch:
   # Deliberately reverse independent conversation responses.
   for request_id in reversed(self.response_queue):self.respond(request_id)
   self.response_queue.clear()
 def respond(self,request_id):
  response=b'\x08'+base.varint(request_id)+b'\x10'+base.varint(200)+base.field(26,b'OK')+base.field(34,b'{}')+base.field(42,b'content-type: application/json')
  payload=b'\x08\x02'+base.field(26,response)
  base.stage('response_oracle')
  checked=base.run_oracle(self.response_oracle,dict(wire=payload.hex(),expected_id=request_id))
  assert checked['accepted']and checked['correlated']and checked['is_success']
  base.stage('response_write');ping=self.ping(('t'+str(len(self.response_order))).encode())
  self.write_app(base.frame(payload[:3],2,False)+ping)
  rest=payload[3:]
  while len(rest)>self.fragment-2:self.write_app(base.frame(rest[:self.fragment-2],0,False));rest=rest[self.fragment-2:]
  self.write_app(base.frame(rest,0,True));self.response_order.append(request_id)
 def close_recipient(self):
  if self.recipient.poll()is None:
   self.recipient.stdin.close()
   try:self.recipient.wait(timeout=5)
   except subprocess.TimeoutExpired:self.recipient.kill();self.recipient.wait()
 def finish(self):
  base.stage('finish')
  assert self.upgraded and self.steps==[2,2]and self.requests==4 and not self.pending_pings and self.fragments is None and not self.response_queue
  self.close_recipient();assert self.recipient.returncode==0
  return dict(tls13_h1=True,upgrade_authenticated=True,actual_session_texts_recovered=4,independent_conversations=2,
   actual_sealed_certificate_verified=True,same_body_request_timestamp_verified=True,private_client_plaintext_opened=False,
   receiver_only_disposable_state=True,responses_reordered=self.batch==2,response_ids_copied=True,
   interleaved_pongs_validated=self.pongs,live_account_side_effects=False)
def main():
 p=argparse.ArgumentParser();p.add_argument('cert');p.add_argument('key');p.add_argument('fragment',nargs='?',type=int,default=127);p.add_argument('request_cert',nargs='?',default='no');p.add_argument('alpn',nargs='?',default='http/1.1')
 p.add_argument('--fixture',type=Path,default=HERE/'server-fixtures.json');p.add_argument('--report',type=Path);p.add_argument('--batch',type=int,default=2)
 args=p.parse_args();assert args.request_cert=='no'and args.alpn=='http/1.1'
 peer=TextPeer(args.cert,args.key,json.loads(args.fixture.read_text()),fragment=args.fragment,batch=args.batch)
 try:
  for line in sys.stdin:
   line=line.strip()
   if line=='quit':
    report=peer.finish()
    if args.report:args.report.write_text(json.dumps(report,indent=2)+'\n')
    return
   base.stage('input_decode');ready,output=peer.feed(bytes.fromhex(line)if line!='-'else b'')
   print(('ready 'if ready else'waiting ')+(output.hex()if output else'-'),flush=True)
  raise AssertionError('fixture closed without completion command')
 finally:peer.close_recipient()
if __name__=='__main__':
 try:main()
 except Exception as error:print(base.failure_diagnostic(error),file=sys.stderr);sys.exit(1)
