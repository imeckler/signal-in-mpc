#!/usr/bin/env python3
"""NEW PUBLIC disposable two-peer six-text source fixture; never recovery input by itself."""
import hashlib,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[3];HERE=pathlib.Path(__file__).resolve().parent
BIN=ROOT/'.deps/signal-established-send-oracle-target/debug'
def ask(binary,values):
 return [json.loads(x) for x in subprocess.check_output([str(BIN/binary)],input=''.join(json.dumps(v)+'\n' for v in values),text=True).splitlines()]
def main():
 oracle='signal-sharded-session-fixture-oracle';receiver='signal-restored-recipient-oracle'
 sender='a1000000-0000-4000-8000-000000000091';peers=['b1000000-0000-4000-8000-000000000091','b1000000-0000-4000-8000-000000000097']
 identities=ask(oracle,[dict(mode='identity',seed=s,sender_uuid=sender)for s in [91,97]])
 assert identities[0]['recipient_identity65']!=identities[1]['recipient_identity65']
 client=[];server=[]
 for slot,seed in enumerate([91,97]):
  bodies=[f'Fresh account conversation {slot+1}, text {i+1}.' for i in range(6)]
  times=[1900000200000+slot*1000+i for i in range(6)]
  padded=ask(receiver,[dict(mode='text',body=b.encode().hex(),timestamp=t)for b,t in zip(bodies,times)])
  result=ask(oracle,[dict(seed=seed,steps=6,sender_uuid=sender,recipient_uuid=peers[slot],alice_secret=identities[0]['sender_secret'],bob_secret=identities[slot]['recipient_secret'],plaintext=padded[0]['padded'],plaintexts=[p['padded']for p in padded],extra_trusted_peers=[dict(name=peers[1-slot],identity=identities[1-slot]['recipient_identity65'][64:])])])[0]
  rows=result['rows'];assert len(rows)==6
  assert result['global_stores']['actual_whole_global_store_codec_reload']
  assert len(result['global_stores']['trusted_peers'])==2
  wires=[]
  for row in rows:
   assert row['account_identity']==identities[0]['sender_identity65'] and row['peer_identity']==identities[slot]['recipient_identity65']
   data=bytes.fromhex(row['input'])[-259:];assert data[0]==255
   wires.append(data[3:3+int.from_bytes(data[1:3],'big')].hex())
  init=dict(mode='init',slot=slot,session_record=rows[0]['record_before'],identity_key_pair=rows[0]['peer_identity'],sender_uuid=sender,recipient_uuid=peers[slot],sender_device=1,recipient_device=1,registration_id=2)
  answers=ask(receiver,[init]+[dict(slot=slot,wire=w)for w in wires]+[dict(slot=slot,wire=wires[-1])])
  assert answers[0]=={'initialized':True}
  for a,b,t in zip(answers[1:7],bodies,times):assert a==dict(accepted=True,body=b,timestamp=t,padded_bytes=80),a
  assert answers[-1]==dict(accepted=False,error='duplicate',state_preserved=True)
  events=[dict(kind='text',body=b,timestamp=t,expected_inner=w)for b,t,w in zip(bodies,times,wires)]
  server.append(dict(slot=slot,sender_uuid=sender,recipient_uuid=peers[slot],access_key=hashlib.sha256(f'fresh-uak-{seed}'.encode()).digest()[:16].hex(),device_id=1,registration_id=2,recipient_secret=identities[slot]['recipient_secret'],root_public=identities[0]['root_public'],bob_session_record=init['session_record'],bob_identity_key_pair=init['identity_key_pair'],events=events))
  client.append(dict(slot=slot,seed=seed,rows=rows,text_inputs=[(b'\xff'+len(b.encode()).to_bytes(2,'big')+b.encode().ljust(48,b'\0')+t.to_bytes(8,'big')).hex()for b,t in zip(bodies,times)],padded_plaintexts=[p['padded']for p in padded],global_stores=result['global_stores']))
 common=dict(public_disposable_fixture_only=True,domain='fresh-sharded-account-v1-seeds91-97',client_uuid=sender,client_password_hex=b'abcdefghijklmnopqrstuv'.hex())
 (HERE/'client.json').write_text(json.dumps(dict(**common,certificate=identities[0]['certificate'],sender_identity65=identities[0]['sender_identity65'],conversations=client,account_global_store=client[0]['global_stores']),indent=2)+'\n')
 (HERE/'recipient.json').write_text(json.dumps(dict(**common,conversations=server),indent=2)+'\n')
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 report=dict(passed=True,actual_recipient_texts=12,actual_replay_rejections=2,actual_trusted_peers=2,actual_global_codec_reload=True,selected_SPQR_phase_override=True,MPC_fresh_bootstrap=False,private_activation=False,public_disposable_fixture_only=True,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),ROOT/'signal_backend/Oracle/src/bin'/f'{oracle}.rs',HERE/'client.json',HERE/'recipient.json']},binary_sha256={n:sha(BIN/n)for n in [oracle,receiver]})
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS 12 actual recipient texts, two replay rejections, two-peer global reload')
if __name__=='__main__':main()
