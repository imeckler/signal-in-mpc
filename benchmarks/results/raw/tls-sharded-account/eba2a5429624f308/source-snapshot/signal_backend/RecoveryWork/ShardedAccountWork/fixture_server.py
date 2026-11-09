#!/usr/bin/env python3
"""Local cut/restart peer. Actual Bob records, no live Signal/account effects."""
import argparse,hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
spec=importlib.util.spec_from_file_location('sharded_receiver_base',ROOT/'handshake_backend/OutboxResumeWork/fixture_server.py');old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old);base=old.base
class Peer(old.RestoredPeer):
 def __init__(self,cert,key,fixture,phase,fragment=127,require_aes128=True,expected_resume=None):
  password=bytes.fromhex(fixture['client_password_hex']);assert len(password)==22 and password.isascii();fixture=dict(fixture,upgrade_username=fixture['client_uuid'],upgrade_password=password.decode())
  base.Peer.__init__(self,cert,key,fixture,fragment=fragment,require_aes128=require_aes128)
  assert phase in ['cut','restored']and len(fixture['conversations'])==2;self.phase=phase;self.steps=[0,0];self.previous_steps=[0,0];self.replay_rejections=0;self.texts=0;self.response_ids=[];self.seen=set();self.withheld=0;self.response_queue=[];self.response_plan=[1,1,1,1,2,1,1,2,1];self.response_batch=0;self.application_hashes={};self.current_hash=None;self.expected_resume=expected_resume;self.resume_hash_matches=False
  self.recipient=subprocess.Popen([str(old.DEFAULT_RECIPIENT)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,text=True)
  try:
   for slot,c in enumerate(fixture['conversations']):
    assert 'initial'not in c and 'sender_identity_secret'not in c
    base.stage('recipient_init');answer=self.recipient_call(dict(mode='init',slot=slot,session_record=c['bob_session_record'],identity_key_pair=c['bob_identity_key_pair'],sender_uuid=c['sender_uuid'],recipient_uuid=c['recipient_uuid'],sender_device=1,recipient_device=c['device_id'],registration_id=c['registration_id']));assert answer=={'initialized':True}
  except BaseException:self.close_recipient();raise
 def handle_binary(self,payload):
  self.current_hash=hashlib.sha256(payload).hexdigest()
  # Actual target SS decoder additionally binds certificate UUID/key to this
  # fixture's actual Bob session address/remote identity, not a substituted one.
  decoded=base.run_oracle(self.oracle,dict(mode='relay',wire=base.frame(payload,mask=bytes(4)).hex()))
  peers=[c for c in self.fixture['conversations']if decoded['path']=='/v1/messages/'+c['recipient_uuid']+'?story=false'];assert len(peers)==1;c=peers[0]
  checked=base.run_oracle(ROOT/'.deps/signal-established-send-oracle-target/debug/signal-sharded-peer-fixture-oracle',dict(mode='decrypt',wire=decoded['ciphertext'],recipient_secret=c['recipient_secret'],root_public=c['root_public']))
  assert checked['certificate_valid']and checked['sender_uuid']==c['sender_uuid']and checked['sender_key']==c['sender_public']
  super().handle_binary(payload)
 def respond(self,request_id):
  assert request_id not in self.seen;self.seen.add(request_id)
  changed=[i for i in range(2)if self.steps[i]!=self.previous_steps[i]];assert len(changed)==1;slot=changed[0];self.previous_steps=self.steps[:]
  self.application_hashes[str(slot)]=self.current_hash
  if self.phase=='restored'and slot==0 and self.steps[0]==1:
   assert self.expected_resume is not None and self.current_hash==self.expected_resume;self.resume_hash_matches=True
  if self.phase=='cut':
   assert self.steps[slot]==1
   if slot==0:self.withheld+=1;return
   self.send_response(request_id);return
  self.response_queue.append(request_id);assert self.response_batch<len(self.response_plan)
  if len(self.response_queue)==self.response_plan[self.response_batch]:
   for value in reversed(self.response_queue):self.send_response(value)
   self.response_queue=[];self.response_batch+=1
 def send_response(self,request_id):
  response=b'\x08'+base.varint(request_id)+b'\x10'+base.varint(200)+base.field(26,b'OK')+base.field(34,b'{}')+base.field(42,b'content-type: application/json');payload=b'\x08\x02'+base.field(26,response)
  base.stage('response_oracle');checked=base.run_oracle(self.response_oracle,dict(wire=payload.hex(),expected_id=request_id));assert checked['accepted']and checked['correlated']and checked['is_success']
  base.stage('response_write');ping=self.ping(b'P'+bytes([len(self.response_ids)]));self.write_app(base.frame(payload[:3],2,False)+ping);rest=payload[3:]
  while len(rest)>self.fragment-2:self.write_app(base.frame(rest[:self.fragment-2],0,False));rest=rest[self.fragment-2:]
  self.write_app(base.frame(rest,0,True));self.response_ids.append(request_id)
 def finish(self):
  base.stage('finish');assert self.upgraded and not self.pending_pings and self.fragments is None
  if self.phase=='cut':assert self.steps==[1,1]and self.withheld==1 and len(self.response_ids)==1 and self.texts==2 and self.replay_rejections==0
  else:assert self.resume_hash_matches and self.steps==[6,5]and self.response_batch==len(self.response_plan)and not self.response_queue and self.texts==10 and self.replay_rejections==1
  self.close_recipient();assert self.recipient.returncode==0
  return dict(passed=True,phase=self.phase,actual_serialized_bob_session=True,fresh_texts_decrypted=self.texts,replays_rejected_state_preserved=self.replay_rejections,withheld_responses=self.withheld,response_count=len(self.response_ids),application_sha256=self.application_hashes,resume_application_hash_matches=self.resume_hash_matches,reordered_response_pairs=2 if self.phase=='restored'else 0,pongs_validated=self.pongs,private_client_IDs_opened=False,unique_delivery_claim=False,live_account_effects=False)
def main():
 p=argparse.ArgumentParser();p.add_argument('cert');p.add_argument('key');p.add_argument('fragment',nargs='?',type=int,default=127);p.add_argument('request_cert',nargs='?',default='no');p.add_argument('alpn',nargs='?',default='http/1.1');p.add_argument('--fixture',type=Path,required=True);p.add_argument('--phase',choices=['cut','restored'],required=True);p.add_argument('--report',type=Path);p.add_argument('--expected-resume');args=p.parse_args();assert args.request_cert=='no'and args.alpn=='http/1.1'
 peer=Peer(args.cert,args.key,json.loads(args.fixture.read_text()),args.phase,fragment=args.fragment,expected_resume=args.expected_resume)
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
