#!/usr/bin/env python3
"""Actual MPC canonical-owner/local-archive component; NOT full recovery."""
import hashlib,json,pathlib,shutil,subprocess,sys,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'SignalReference/PrivateRecordWork'))
from SignalReference.RelayServiceWork.check import oracle,metadata
from check import make,record
from check_send import flatten
from check_binding import service
HERE=pathlib.Path(__file__).resolve().parent

def main():
 stage=ROOT/'.deps/private-canonical-owner-native/v1-candidate-1';manifest=stage/'owner.manifest';binary=ROOT/'.deps/private-canonical-owner-fixture';runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 fixture=oracle([dict(mode='sealed',seed=19,inner='')])[0]
 target=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-canonical-owner-oracle'
 query=dict(seed=19,steps=2,alice_secret=fixture['sender_secret'],bob_secret=fixture['recipient_secret'],plaintext=(b'E'*79+b'\x80').hex())
 def ask(value):return json.loads(subprocess.check_output([str(target)],input=json.dumps(value)+'\n',text=True))
 rows=ask(query)['rows'];raw=service(rows[0]);f=bytes.fromhex(fixture['input']);raw[32:292]=f[160:420];raw[474:554]=bytes.fromhex(query['plaintext']);raw[554:611]=metadata(19,2**63)
 initial=bytes(raw);lines=[bytes(flatten(make(bytes.fromhex(rows[0]['sender_record_before']),record))),bytes.fromhex(rows[0]['sender_selected_before']),initial]
 for i,row in enumerate(rows):
  prefix=bytes.fromhex(row['sender_result']);updated=bytearray(initial)
  updated[333:365]=prefix[1:33];updated[293:297]=prefix[33:37];updated[365:397]=prefix[37:69];updated[397:401]=prefix[69:73];updated[594:602]=(2**63+i+1).to_bytes(8,'big')
  expected=bytes(flatten(make(bytes.fromhex(row['sender_record_after']),record)))+bytes.fromhex(row['sender_selected_after'])+bytes(updated)
  assert len(expected)==6686
  lines.extend([b'\0'+bytes.fromhex(query['plaintext']),bytes(raw[586:594]),(2**63+i).to_bytes(8,'big'),expected])
 files=[pathlib.Path(__file__),HERE/'canonical_owner_fixture.cpp',HERE/'NativeCanonicalSendOwner.h',HERE/'NativeRecordBinding.h',HERE/'NativeOwnShareArchive.h',HERE/'OwnShareBox.h',HERE/'CiphertextStore.h',ROOT/'signal_backend/VariableServiceWork/VariableSendStore.h',ROOT/'signal_backend/VariableServiceWork/VariableSendBatch.h',ROOT/'signal_backend/VariableServiceWork/NativeVariableService.h',ROOT/'handshake_backend/NativeWorker.h']
 before={str(p.relative_to(ROOT)):sha(p)for p in files};binary_hash=sha(binary);manifest_hash=sha(manifest)
 data=stage/'Player-Data';data.mkdir(exist_ok=True)
 for pattern in ['*.pem','*.key','*.0']:
  for path in (runtime/'Player-Data').glob(pattern):shutil.copyfile(path,data/path.name)
 logs=pathlib.Path(tempfile.mkdtemp(prefix='run-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5);inputs=logs/'public-fixture.txt';inputs.write_text(''.join(x.hex()+'\n'for x in lines))
 (logs/'launch-receipt.json').write_text(json.dumps(dict(source_sha256=before,binary_sha256=binary_hash,manifest_sha256=manifest_hash),indent=2)+'\n')
 procs=[];streams=[];start=time.monotonic()
 try:
  for party in range(5):
   stream=(logs/f'party-{party}.log').open('w');streams.append(stream)
   procs.append(subprocess.Popen([str(binary),str(party),str(hosts),'29350',str(manifest),str(inputs)],cwd=stage,stdout=stream,stderr=subprocess.STDOUT))
  print('LIVE logs='+str(logs)+' pids='+','.join(str(p.pid)for p in procs),flush=True)
  deadline=time.monotonic()+1800
  while any(p.poll()is None for p in procs):
   if any(p.poll()not in [None,0]for p in procs):raise RuntimeError('canonical owner party failed: '+str(logs))
   if time.monotonic()>deadline:raise TimeoutError('canonical owner component bound')
   time.sleep(.2)
  assert all(p.returncode==0 for p in procs)
 finally:
  for p in procs:
   if p.poll()is None:p.kill()
  for p in procs:p.wait()
  for stream in streams:stream.close()
 frames=[]
 for party in range(5):
  text=(logs/f'party-{party}.log').read_text();assert 'canonical owner fixture passed' in text
  frames.append([line.split()[2]for line in text.splitlines()if line.startswith('FRAME ')])
 assert all(x==frames[0]for x in frames)and len(frames[0])==2
 wires=[]
 for i,frame in enumerate(frames[0]):
  relay=oracle([dict(mode='relay',wire=frame)])[0];assert relay['id']==2**63+i
  decoded=oracle([dict(mode='sealed_decrypt',wire=relay['ciphertext'],recipient_secret=fixture['recipient_secret'],root_public=fixture['root_public'])])[0]
  assert decoded['certificate_valid'];wires.append(decoded['inner'])
 actual=ask(dict(query,wires=wires));assert actual['rows']==rows
 assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}and sha(binary)==binary_hash and sha(manifest)==manifest_hash
 report=dict(passed=True,parties=5,threshold=2,sends=2,actual_MPC_service_computed_DH_binding_store=True,actual_Rust_peer_decrypt_and_whole_record_projection=True,private_state_equality_aggregate_only=True,encrypted_local_reserve_commit_fsynced=True,local_archive_only_no_quorum_certificate=True,full_account=False,restart_or_import=False,epoch_retirement=False,provider_admission=False,synthetic_component_response_ack=True,opened_outputs='Disposable final wire and aggregate state equality only; never state/key/DH shares.',elapsed_seconds=time.monotonic()-start,not_throughput_measurement=True,logs=str(logs.relative_to(ROOT)),source_sha256=before,binary_sha256=binary_hash,manifest_sha256=manifest_hash,oracle_binary_sha256=sha(target),sealed_oracle_binary_sha256=sha(ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'))
 (HERE/'canonical-native-report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: actual private canonical owner sends/store/local archive; actual recipient decrypted both',flush=True)
if __name__=='__main__':main()
