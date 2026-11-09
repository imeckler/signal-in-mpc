#!/usr/bin/env python3
"""Loopback fixture peer: actual Bob SessionRecord replay rejection then text.
No deployed service/account. Receiver-only disposable fixture data remains here;
no MPC sender state or secret shares are requested, reconstructed or logged.
"""
import argparse,importlib.util,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
spec=importlib.util.spec_from_file_location('restored_peer_base',ROOT/'signal_backend/VariableServiceWork/fixture_server.py')
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
base.STAGES=base.STAGES|frozenset(["recipient_init","recipient_check"])
DEFAULT_RECIPIENT=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-restored-recipient-oracle'
class RestoredPeer(base.Peer):
 def __init__(self,cert,key,fixture,*args,recipient=DEFAULT_RECIPIENT,**kwargs):
  # This disposable fixture uses the real chat UUID +22 ASCII password bytes.
  password=bytes.fromhex(fixture['client_password_hex']);assert len(password)==22 and password.isascii()
  fixture=dict(fixture,upgrade_username=fixture['client_uuid'],upgrade_password=password.decode('ascii'))
  super().__init__(cert,key,fixture,*args,**kwargs)
  assert 1<=len(fixture['conversations'])<=4
  self.steps=[0]*len(fixture['conversations']);self.replay_rejections=0;self.texts=0;self.response_ids=[]
  self.recipient=subprocess.Popen([str(recipient)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,text=True)
  try:
   for slot,c in enumerate(fixture['conversations']):
    assert 'initial'not in c and 'sender_identity_secret'not in c
    assert len(bytes.fromhex(c['bob_identity_key_pair']))==65 and len(c['events'])>=2
    assert c['events'][0]['kind']=='duplicate'and any(e['kind']=='text'for e in c['events'])
    base.stage('recipient_init')
    initialized=self.recipient_call(dict(mode='init',slot=slot,session_record=c['bob_session_record'],identity_key_pair=c['bob_identity_key_pair'],sender_uuid=c['sender_uuid'],recipient_uuid=c['recipient_uuid'],sender_device=c.get('sender_device',1),recipient_device=c['device_id'],registration_id=c['registration_id']))
    assert initialized=={'initialized':True}
  except BaseException:self.close_recipient();raise
 def recipient_call(self,row):
  self.recipient.stdin.write(json.dumps(row)+'\n');self.recipient.stdin.flush()
  line=self.recipient.stdout.readline();assert line,'recipient subprocess closed';return json.loads(line)
 def handle_binary(self,payload):
  base.stage('relay_oracle');answer=base.run_oracle(self.oracle,dict(mode='relay',wire=base.frame(payload,mask=bytes(4)).hex()))
  base.stage('relay_binding');matches=[(slot,c)for slot,c in enumerate(self.fixture['conversations'])if answer['path']=='/v1/messages/'+c['recipient_uuid']+'?story=false']
  assert len(matches)==1;slot,c=matches[0];step=self.steps[slot];assert step<len(c['events']);event=c['events'][step]
  assert answer['access_key']==c['access_key']and 2**63<=answer['id']<2**64 and answer['id']not in self.response_ids
  body=answer['body'];assert body['timestamp']==event['timestamp']and body['online']is False and body['urgent']is True
  assert len(body['messages'])==1;message=body['messages'][0]
  assert message['type']==6 and message['destinationDeviceId']==c['device_id']and message['destinationRegistrationId']==c['registration_id']
  base.stage('sealed_oracle');decoded=base.run_oracle(self.oracle,dict(mode='sealed_decrypt',wire=answer['ciphertext'],recipient_secret=c['recipient_secret'],root_public=c['root_public']))
  base.stage('sealed_verification');assert decoded['certificate_valid']is True
  if 'expected_inner'in event:assert decoded['inner']==event['expected_inner']
  if event['kind']=='duplicate':assert 'expected_inner'in event
  base.stage('recipient_check');recovered=self.recipient_call(dict(slot=slot,wire=decoded['inner']))
  if event['kind']=='duplicate':
   assert recovered==dict(accepted=False,error='duplicate',state_preserved=True);self.replay_rejections+=1
  else:
   assert event['kind']=='text'and recovered==dict(accepted=True,body=event['body'],timestamp=event['timestamp'],padded_bytes=80);self.texts+=1
  self.steps[slot]+=1;self.requests+=1;self.respond(answer['id'])
 def respond(self,request_id):
  response=b'\x08'+base.varint(request_id)+b'\x10'+base.varint(200)+base.field(26,b'OK')+base.field(34,b'{}')+base.field(42,b'content-type: application/json')
  payload=b'\x08\x02'+base.field(26,response)
  base.stage('response_oracle');checked=base.run_oracle(self.response_oracle,dict(wire=payload.hex(),expected_id=request_id))
  assert checked['accepted']and checked['correlated']and checked['is_success']
  base.stage('response_write');ping=self.ping(('s'+str(len(self.response_ids))).encode())
  self.write_app(base.frame(payload[:3],2,False)+ping);rest=payload[3:]
  while len(rest)>self.fragment-2:self.write_app(base.frame(rest[:self.fragment-2],0,False));rest=rest[self.fragment-2:]
  self.write_app(base.frame(rest,0,True));self.response_ids.append(request_id)
 def close_recipient(self):
  if self.recipient.poll()is None:
   self.recipient.stdin.close()
   try:self.recipient.wait(timeout=5)
   except subprocess.TimeoutExpired:self.recipient.kill();self.recipient.wait()
 def finish(self):
  base.stage('finish');assert self.upgraded and self.steps==[len(c['events'])for c in self.fixture['conversations']]and not self.pending_pings and self.fragments is None
  assert self.replay_rejections>=1 and self.texts>=1
  self.close_recipient();assert self.recipient.returncode==0
  return dict(tls13_h1=True,upgrade_authenticated=True,actual_serialized_bob_session=True,actual_recipient_replay_rejections=self.replay_rejections,duplicate_state_preserved=True,fresh_texts_decrypted=self.texts,service_acceptance_for_duplicate=True,unique_recipient_delivery_for_resumed=False,response_ids_copied=True,response_fragmented_with_control_ping=True,interleaved_pongs_validated=self.pongs,client_plaintext_opened=False,receiver_only_disposable_state=True,native_MPC_executed_here=False,authorized_account_restore_executed_here=False,live_account_side_effects=False)
def main():
 p=argparse.ArgumentParser();p.add_argument('cert');p.add_argument('key');p.add_argument('fragment',nargs='?',type=int,default=127);p.add_argument('request_cert',nargs='?',default='no');p.add_argument('alpn',nargs='?',default='http/1.1');p.add_argument('--fixture',type=Path,required=True);p.add_argument('--recipient',type=Path,default=DEFAULT_RECIPIENT);p.add_argument('--report',type=Path)
 args=p.parse_args();assert args.request_cert=='no'and args.alpn=='http/1.1'
 peer=RestoredPeer(args.cert,args.key,json.loads(args.fixture.read_text()),recipient=args.recipient,fragment=args.fragment)
 try:
  for line in sys.stdin:
   line=line.strip()
   if line=='quit':
    report=peer.finish()
    if args.report:args.report.write_text(json.dumps(report,indent=2)+'\n')
    return
   base.stage('input_decode');ready,out=peer.feed(bytes.fromhex(line)if line!='-'else b'');print(('ready 'if ready else'waiting ')+(out.hex()if out else'-'),flush=True)
  raise AssertionError('fixture closed without completion')
 finally:peer.close_recipient()
if __name__=='__main__':
 try:main()
 except Exception as error:print(base.failure_diagnostic(error),file=sys.stderr);sys.exit(1)
