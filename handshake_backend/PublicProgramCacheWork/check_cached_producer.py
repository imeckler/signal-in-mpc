#!/usr/bin/env python3
"""Actual cached B2 producer+epoch component, not a TLS/application run."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time,secrets
root=Path(__file__).resolve().parents[2];work=Path(__file__).parent;sys.path.insert(0,str(root))
from SignalReference.RelayServiceWork.check import oracle
runtime=root/'.deps/tls-public-program-cache-runtime-v2/MP-SPDZ';binary=runtime.parent/'tls-native-cached-producer-fixture-v2'
base=root/'.deps/native-cached-text-producer-v1';base.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
source_manifests=[root/'.deps/private-variable-conversation-native/260-80-0-0/batch-2-sha-gate-efficient/service.manifest',root/'.deps/private-text-notification-native/text.manifest']
files={}
for manifest in source_manifests:
 for line in manifest.read_text().splitlines()[1:]:
  digest,name=line.split(' ',1);source=manifest.parent/name;assert sha(source)==digest
  if name in files:assert files[name][0]==digest
  else:files[name]=(digest,source)
for name,(digest,source)in files.items():
 target=base/name;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert target.is_symlink()and target.resolve()==source.resolve()and sha(target)==digest
 else:target.symlink_to(source.resolve())
manifest=base/'producer.manifest';encoded='tls-mpc-pinned-files-v1\n'+''.join(digest+' '+name+'\n'for name,(digest,_)in sorted(files.items()))
if manifest.exists():assert manifest.read_text()==encoded
else:manifest.write_text(encoded)
fixture=root/'signal_backend/TextNotificationWork/server-fixtures.json';recipient=root/'.deps/signal-established-send-oracle-target/debug/signal-text-recipient-extended-oracle';sealed_oracle=root/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
tracked=[Path(__file__),work/'cached_producer_fixture.cpp',work/'CachedBatchService.h',work/'PinnedCacheAdmission.h',work/'PinnedPublicCode.h',work/'PublicCodeCache.h',binary,runtime/'libSPDZ.so',manifest,fixture,recipient,sealed_oracle]+source_manifests
tracked +=[root/p for p in ['handshake_backend/NativeWorker.h','handshake_backend/OwnedSecrets.h','handshake_backend/SessionWork/NativeLifecycle.h','handshake_backend/SessionWork/ErasedHostCall.h','signal_backend/VariableServiceWork/VariableSendStore.h','signal_backend/VariableServiceWork/VariableSendBatch.h','signal_backend/VariableServiceWork/VariableShape.h','signal_backend/TextNotificationWork/PublicTextFixture.h','signal_backend/TextNotificationWork/TextNotificationInput.h','signal_backend/Oracle/src/bin/signal-text-recipient-extended-oracle.rs']]
tracked +=[runtime/p for p in ['Processor/BaseMachine.h','Processor/BaseMachine.cpp','Processor/Program.h','Processor/Program.cpp','Processor/Machine.h','Processor/Machine.hpp','Tools/PublicCodeCache.h','Tools/PinnedPublicCode.h']]
hashes={str(p.relative_to(root)):sha(p)for p in tracked};products={name:digest for name,(digest,_)in files.items()}
out=root/'benchmarks/results/raw/private-native-cached-producer'/secrets.token_hex(8);out.mkdir(parents=True);print(out,flush=True)
with(out/'ssl.log').open('w')as log:subprocess.run(['bash',str(root/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),'5'],cwd=base,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
library=base/'libSPDZ.so'
if not library.exists():library.symlink_to(runtime/'libSPDZ.so')
assert library.resolve()==(runtime/'libSPDZ.so').resolve();hosts=out/'hosts';hosts.write_text('127.0.0.1\n'*5)
clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW);started=clock();children=[];streams=[];cleanup=[]
report={'passed':False,'scope':'two real B2 producer calls/four nonempty texts, independent conversation state and epoch renewal; not full TLS/application throughput, production admission, authenticated response, MAC-tamper or complete failure-erasure claim','source_product_sha256':hashes,'compiled_closure_sha256':products,'raw':str(out.relative_to(root)),'synthetic_component_response_ack':True,'statistical_security':128,'parties':5,'threshold':2,'messages':4,'cache_free_eight_text_baseline_preserved':True,'runtime_consumption_semantics':'post-function job-local usage, never subtract previous function'}
(out/'launch-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
try:
 for party in range(5):
  stream=(out/f'party-{party}.log').open('w');streams.append(stream)
  child=subprocess.Popen([str(binary),str(party),str(hosts),'30700',str(manifest),str(out/'fence')],cwd=base,stdout=stream,stderr=subprocess.STDOUT);children.append(child);print('party='+str(party)+' pid='+str(child.pid),flush=True)
 deadline=started+1200
 while any(p.poll()is None for p in children):
  if any(p.poll()not in [None,0]for p in children):raise RuntimeError('fixed-party-failure')
  if clock()>deadline:raise TimeoutError('cached-producer-bound')
  time.sleep(.2)
 for stream in streams:stream.flush()
 rows=[];allframes=[];rss=[]
 for party in range(5):
  text=(out/f'party-{party}.log').read_text();assert 'private cached producer fixture passed'in text
  frames=[line.split()[1:]for line in text.splitlines()if line.startswith('FRAME ')];allframes.append(frames)
  metrics=[json.loads(line.split(' ',1)[1])for line in text.splitlines()if line.startswith('CACHED_PRODUCER_METRIC ')];assert len(metrics)==2 and metrics[0]['cache_loads_delta']==1 and metrics[1]['cache_loads_delta']==0 and metrics[1]['load_calls']==0 and [m['epoch']for m in metrics]==[0,1];rows.append(metrics)
  memory=[json.loads(line.split(' ',1)[1])for line in text.splitlines()if line.startswith('CACHED_PRODUCER_RSS ')];assert len(memory)==1;rss.append(memory[0]['maxrss_bytes'])
 assert len(allframes[0])==4 and all(frames==allframes[0]for frames in allframes)
 fixture_data=json.loads(fixture.read_text());peer=subprocess.Popen([str(recipient)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,text=True)
 def ask(value):peer.stdin.write(json.dumps(value)+'\n');peer.stdin.flush();return json.loads(peer.stdout.readline())
 recovered=[];ephemerals=[];masks=[];inner_wires=[[],[]]
 try:
  for slot,c in enumerate(fixture_data['conversations']):assert ask(dict(mode='init',slot=slot,receiving_state=c['receiving_state'],recipient_secret=c['recipient_secret']))=={'initialized':True}
  for round_text,slot_text,frame in allframes[0]:
   round=int(round_text);slot=int(slot_text);c=fixture_data['conversations'][slot];answer=oracle([dict(mode='relay',wire=frame)])[0]
   assert answer['path']=='/v1/messages/'+c['recipient_uuid']+'?story=false'and answer['access_key']==c['access_key']and answer['id']==2**63+2*round+slot
   assert answer['body']['timestamp']==c['timestamps'][round]
   decoded=oracle([dict(mode='sealed_decrypt',wire=answer['ciphertext'],recipient_secret=c['recipient_secret'],root_public=c['root_public'])])[0];assert decoded==dict(inner=c['expected_inner'][round],certificate_valid=True)
   raw=bytes.fromhex(answer['ciphertext']);assert raw[0]==17 and raw[1:4]==bytes([10,33,5]);ephemerals.append(raw[3:36].hex())
   wire=bytes.fromhex(frame);assert wire[1]&128;offset=2+(2 if wire[1]&127==126 else 8 if wire[1]&127==127 else 0);masks.append(wire[offset:offset+4].hex())
   actual=ask(dict(slot=slot,wire=decoded['inner'],inspect_counters=True));initial=bytes.fromhex(c['receiving_state']);counter=int.from_bytes(initial[1:5],'big')+round
   expected=dict(accepted=True,body=c['expected_text'][round],timestamp=c['timestamps'][round],padded_bytes=80,signal_counter=counter,next_signal_counter=counter+1,pq_receive_counter=int.from_bytes(initial[105:109],'big')+round+1)
   assert actual==expected;recovered.append({'round':round,'slot':slot,'actual_recipient_matches':True,'signal_counter':counter,'next_signal_counter':counter+1});inner_wires[slot].append(decoded['inner'])
  assert len(set(ephemerals))==4
  for slot in range(2):assert ask(dict(slot=slot,wire=inner_wires[slot][0]))['accepted']is False
 finally:
  peer.stdin.close()
  try:peer.wait(timeout=10)
  except subprocess.TimeoutExpired:peer.kill();peer.wait();raise
 report.update(passed=True,producer_metrics=rows,actual_recipient=recovered,observed_distinct_ephemeral_publics=len(set(ephemerals)),observed_distinct_ws_masks=len(set(masks)),recipient_replays_rejected=2,party_maxrss_bytes=rss,sum_party_peak_rss_bytes=sum(rss),sum_peak_scope='sum of individual process peaks, not simultaneous whole-system RSS')
except Exception as exc:report['failure_category']=type(exc).__name__;report['fixed_public_failure']=str(exc)if str(exc).startswith(('fixed-','cached-'))else'component-validation-failed'
finally:
 for p in children:
  if p.poll()is None:
   try:p.kill()
   except Exception as exc:cleanup.append(type(exc).__name__)
 for p in children:
  try:p.wait(timeout=10)
  except Exception as exc:cleanup.append(type(exc).__name__)
 for stream in streams:stream.close()
 report.update(elapsed_seconds=clock()-started,pids=[p.pid for p in children],exit_codes=[p.returncode for p in children],cleanup_errors=cleanup,integrity_verified=all(sha(p)==hashes[str(p.relative_to(root))]for p in tracked)and all(sha(base/name)==digest for name,digest in products.items()))
 report['passed']=report['passed']and not cleanup and report['integrity_verified'];encoded=json.dumps(report,indent=2)+'\n';(out/'report.json').write_text(encoded);(work/'cached-producer-report.json').write_text(encoded);print(json.dumps({k:report[k]for k in ['passed','exit_codes','elapsed_seconds','cleanup_errors']}),flush=True)
if not report['passed']:raise SystemExit(1)
