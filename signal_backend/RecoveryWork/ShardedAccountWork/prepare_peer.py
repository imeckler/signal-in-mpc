#!/usr/bin/env python3
"""Receiver-only cut/restart fixtures and PUBLIC ordinary-TLS smoke envelopes."""
import copy,hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def main():
 source=HERE.parent/'FreshShardedFixtureWork';client=json.loads((source/'client.json').read_text());receiver=json.loads((source/'recipient.json').read_text());oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-sharded-peer-fixture-oracle'
 queries=[]
 for slot,c in enumerate(receiver['conversations']):
  for step,event in enumerate(c['events']):queries.append(dict(mode='seal',sender_identity65=client['sender_identity65'],sender_uuid=c['sender_uuid'],certificate=client['certificate'],recipient_uuid=c['recipient_uuid'],recipient_public=c['bob_identity_key_pair'][64:],inner=event['expected_inner'],seed=99100+slot*100+step))
 result=subprocess.check_output([str(oracle)],input=''.join(json.dumps(q)+'\n'for q in queries),text=True);wires=[json.loads(line)['wire']for line in result.splitlines()];assert len(wires)==12
 cut=copy.deepcopy(receiver);restart=copy.deepcopy(receiver)
 for slot,c in enumerate(receiver['conversations']):
  events=[dict(e,sealed_wire=wires[6*slot+i])for i,e in enumerate(c['events'])]
  cut['conversations'][slot]['events']=events[:1]
  restart['conversations'][slot]['bob_session_record']=client['conversations'][slot]['rows'][0]['record_after']
  restart['conversations'][slot]['events']=([dict(events[0],kind='duplicate')]if slot==0 else[])+events[1:]
  for target in [cut,restart]:target['conversations'][slot]['sender_public']=client['sender_identity65'][64:]
 (HERE/'peer-cut.json').write_text(json.dumps(cut,indent=2)+'\n');(HERE/'peer-restored.json').write_text(json.dumps(restart,indent=2)+'\n')
 files=[pathlib.Path(__file__),source/'client.json',source/'recipient.json',HERE/'peer-cut.json',HERE/'peer-restored.json',ROOT/'signal_backend/Oracle/src/bin/signal-sharded-peer-fixture-oracle.rs']
 report=dict(prepared=True,receiver_only_outputs=True,NEW_public_disposable_fixture=True,ordinary_smoke_envelopes=12,restart_bob_after_message0=True,private_MPC=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files},oracle_binary_sha256=hashlib.sha256(oracle.read_bytes()).hexdigest());(HERE/'peer-fixture-report.json').write_text(json.dumps(report,indent=2)+'\n');print('prepared receiver-only cut/restart fixtures')
if __name__=='__main__':main()
