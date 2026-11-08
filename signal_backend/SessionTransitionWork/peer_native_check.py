#!/usr/bin/env python3
"""PUBLIC fixture only: native received keys never opened; final sealed frames only."""
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
from SignalReference.PrivateNewDhReceiveWork.check_model import invoke,TEXT
HERE=Path(__file__).resolve().parent
PEER=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-new-dh-native-peer-oracle'
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def main():
 stage=ROOT/'.deps/private-new-dh-staged-native';runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 assert(stage/'receive.manifest').exists(),'staged receive compile must pass first'
 service=ROOT/'.deps/private-variable-conversation-native/260-80-0-0'
 for folder in ['Bytecode','Schedules']:
  for p in(service/'Programs'/folder).iterdir():
   if not p.is_file():continue
   target=stage/'Programs'/folder/p.name
   if target.exists():assert sha(target)==sha(p)
   else:shutil.copy2(p,target)
 shutil.copy2(ROOT/'programs/signal_new_dh_fixture_check.mpc',stage/'Programs/Source/signal_new_dh_fixture_check.mpc')
 subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_new_dh_fixture_check'],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),check=True,timeout=120)
 descriptors=['signal_private_new_dh_summary_256_5-sbv:[2072x1]-sbv:[600x1]','signal_private_dh_receive_candidate-sbv:[512x1]-sbv:[1024x1]','signal_private_new_dh_crypto_256_5-sbv:[8408x1]-sbv:[4864x1]','signal_new_dh_fixture_equal_4864-sbv:[9728x1]-sbv:[8x1]','signal_private_variable_conversation_260_80_0_0-sbv:[4888x1]-sbv:[10984x1]']
 manifest=stage/'peer-fixture.manifest';manifest.write_text(build(stage,descriptors))
 binary=ROOT/'.deps/private-new-dh-peer-fixture'
 subprocess.run(['make','-C',str(runtime),'-f',str(HERE/'Makefile'),'TRANSITION_WORK='+str(HERE),'PEER_DH_FIXTURE='+str(binary),str(binary)],check=True)
 sources=[Path(__file__),HERE/'peer_native_fixture.cpp',HERE/'NativeNewDhReceive.h',HERE/'NativeComputedDh.h',HERE/'Makefile',ROOT/'signal_backend/VariableServiceWork/NativeVariableService.h',ROOT/'signal_backend/VariableServiceWork/VariableShape.h',ROOT/'programs/signal_new_dh_stage.mpc',ROOT/'programs/signal_dh_receive_candidate.mpc',ROOT/'programs/signal_new_dh_fixture_check.mpc',ROOT/'handshake_backend/NativeWorker.h',ROOT/'signal_backend/Oracle/src/bin/signal-new-dh-native-peer-oracle.rs',ROOT/'signal_backend/Oracle/src/relay.rs']
 before={str(p.relative_to(ROOT)):sha(p)for p in sources};executables={p.name:sha(p)for p in [PEER,TEXT,binary]}
 logs=Path(tempfile.mkdtemp(prefix='peer-fixture-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5)
 data=stage/'Player-Data';data.mkdir(exist_ok=True)
 for pattern in ['*.pem','*.key','*.0']:
  for p in(runtime/'Player-Data').glob(pattern):shutil.copy2(p,data/p.name)
 peer=subprocess.Popen([str(PEER)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=(logs/'peer.log').open('w'),text=True)
 def ask(row):
  peer.stdin.write(json.dumps(row)+'\n');peer.stdin.flush();line=peer.stdout.readline();assert line,'actual peer failed';return json.loads(line)
 processes=[];streams=[];start=time.monotonic();cleanup=[]
 try:
  init=ask(dict(mode='init',seed=731));initial=bytes.fromhex(init['initial_state']+init['remote_identity']+init['local_identity']+init['local_identity_fixture_secret']+init['certificate']+init['sending_pq'])
  metadata=bytes.fromhex('00112233445566778899aabbccddeeff')+bytes([113])*16+(1900000000100).to_bytes(8,'big')+(2**63).to_bytes(8,'big')+bytes([1])+(12345).to_bytes(4,'big')+bytes(4)
  initial+=metadata;assert len(initial)==982
  inputs=logs/'public-initial.txt';inputs.write_text(initial.hex()+'\n')
  for party in range(5):
   stream=(logs/f'party-{party}.log').open('w');streams.append(stream)
   processes.append(subprocess.Popen([str(binary),str(party),str(hosts),'20170',str(manifest),str(inputs)],cwd=stage,stdin=subprocess.PIPE,stdout=stream,stderr=subprocess.STDOUT,text=True))
  for round in range(2):
   incoming=bytes.fromhex(invoke(TEXT,[dict(mode='text',body=f'Native incoming root {round} ☕'.encode().hex(),timestamp=1900000000000+round)])[0]['padded'])
   outgoing=bytes.fromhex(invoke(TEXT,[dict(mode='text',body=f'Native reply from root {round}'.encode().hex(),timestamp=1900000000100+round)])[0]['padded'])
   message=ask(dict(mode='send',plaintext=incoming.hex()));line=message['wire']+' '+incoming.hex()+' '+outgoing.hex()+'\n'
   for p in processes:p.stdin.write(line);p.stdin.flush()
   deadline=time.monotonic()+1500;frame=None
   while frame is None:
    if any(p.poll()is not None for p in processes):raise RuntimeError('native peer party exited early: '+str(logs))
    for text in(logs/'party-0.log').read_text().splitlines():
     if text.startswith(f'FRAME {round} '):frame=text.split(' ',2)[2]
    if time.monotonic()>deadline:raise TimeoutError('native peer round timeout: '+str(logs))
    time.sleep(.1)
   result=ask(dict(mode='frame',wire=frame,timestamp=1900000000100+round));assert result['accepted'] and bytes.fromhex(result['plaintext'])==outgoing
   print(f'Actual peer decrypted native reply {round}',flush=True)
  for p in processes:p.stdin.close()
  for p in processes:assert p.wait(timeout=30)==0
 finally:
  for p in processes:
   if p.poll()is None:p.kill();cleanup.append('party-killed')
  for p in processes:p.wait()
  for stream in streams:stream.close()
  peer.stdin.close()
  try:peer.wait(timeout=5)
  except subprocess.TimeoutExpired:peer.kill();peer.wait();cleanup.append('peer-killed')
 for party in range(5):
  text=(logs/f'party-{party}.log').read_text();assert 'REJECTIONS passed'in text and 'native receive peer fixture passed'in text
 assert before=={str(p.relative_to(ROOT)):sha(p)for p in sources}
 assert executables=={p.name:sha(p)for p in [PEER,TEXT,binary]}
 report=dict(passed=True,parties=5,threshold=2,actual_peer_receive_reply_ratchet_cycles=2,actual_sealed_sender_certificate_and_session_decrypt=True,PQ_both_directions_127_to_128=True,computed_DH_bound_to_same_actual_private_parser_point=True,fresh_root_private_and_all_chain_states_unopened=True,selected_state_committed_before_reply=True,rejections=['badMAC','loworderpoint0','retainedPQcounterexceedsprofile'],rejection_all_old525bytes_preserved=True,opened='5 secure equality bits and2 final disposable sealed WebSocket ciphertext frames with validity/length; no state/key/private plaintext values.',public_fixture_initialization=True,selected_established_PQR_phase_override=True,full_fresh_session_or_SPQR_KEM=False,recoverable_persistence=False,full_actual_source_refinement=False,runtime_epoch_retirement_not_exercised=True,elapsed_seconds=time.monotonic()-start,timing_scope='Startup,5 receive candidates,5 comparisons,2 sealed replies,actual local peer; not service throughput.',cleanup=cleanup,logs=str(logs.relative_to(ROOT)),manifest_sha256=sha(manifest),binary_sha256=executables,source_sha256=before)
 (HERE/'peer-native-report.json').write_text(json.dumps(report,indent=2)+'\n');print('5party retained fresh-key receive/reply passed',flush=True)
if __name__=='__main__':main()
