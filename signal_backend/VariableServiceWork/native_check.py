#!/usr/bin/env python3
"""Five-party selected-chain private DH/service store fixture; no live service."""
import hashlib,json,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from signal_backend.VariableServiceWork.shape import VariableShape
from scripts.pin_tls_worker import build
from scripts.check_lean_signal_spqr_send import cases
from SignalReference.PrivateConversationWork.check import native_inner
from SignalReference.RelayServiceWork.check import metadata,oracle
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 shape=VariableShape(260,0,0,0);stage=ROOT/'.deps/private-variable-conversation-native/260-0-0-0'
 manifest=stage/'service.manifest';assert manifest.read_text()==build(stage,[shape.descriptor])
 runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';binary=ROOT/'.deps/private-variable-fixture'
 sources=[Path(__file__),HERE/'native_fixture.cpp',HERE/'NativeVariableService.h',HERE/'VariableShape.h',HERE/'VariableSendStore.h',HERE/'shape.py',HERE/'prepare.py',
  ROOT/'signal_backend/PersistentSendFence.h',ROOT/'programs/signal_variable_service.mpc',ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/mixed.py',ROOT/'handshake_backend/field_dag.py']
 before={str(p.relative_to(ROOT)):sha(p) for p in sources}
 subprocess.run(['make','-C',str(runtime),'-f',str(HERE/'Makefile'),'SIGNAL_WORK='+str(HERE),'SIGNAL_OUTPUT='+str(binary),str(binary)],check=True)
 assert before=={str(p.relative_to(ROOT)):sha(p) for p in sources}
 fixture=oracle([dict(mode='sealed',seed=0,inner='')])[0];f=bytes.fromhex(fixture['input'])
 initial=bytearray(next(cases())[1][0]);assert len(initial)==182
 initial[1:5]=(127).to_bytes(4,'big');initial[5:9]=(127).to_bytes(4,'big');initial[105:109]=(126).to_bytes(4,'big');initial[109:117]=(127).to_bytes(8,'big')
 initial[118:150]=f[64:96];initial[150:182]=f[:32]
 raw=bytes.fromhex(fixture['sender_secret'])+f[160:420]+bytes(initial)+metadata(0,127);assert len(raw)==shape.input_bytes
 bad=bytearray(raw);bad[shape.spqr_offset+118]^=1
 data=stage/'Player-Data';data.mkdir(exist_ok=True)
 for pattern in ['*.pem','*.key','*.0']:
  for p in (runtime/'Player-Data').glob(pattern):shutil.copy2(p,data/p.name)
 # Fresh directory per run preserves the restart-refusal fence. Never erase a
 # prior slot to retry a conversation state.
 logs=Path(tempfile.mkdtemp(prefix='fixture-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5)
 inputs=logs/'public-fixtures.txt';inputs.write_text(raw.hex()+'\n'+bytes(bad).hex()+'\n')
 procs=[];streams=[];start=time.monotonic()
 try:
  for party in range(5):
   stream=(logs/f'party-{party}.log').open('w');streams.append(stream)
   procs.append(subprocess.Popen([str(binary),str(party),str(hosts),'19940',str(manifest),str(inputs)],cwd=stage,stdout=stream,stderr=subprocess.STDOUT))
  deadline=time.monotonic()+2400
  while any(p.poll() is None for p in procs):
   if time.monotonic()>deadline:raise TimeoutError('private variable conversation timeout')
   if any(p.poll() not in [None,0] for p in procs):raise RuntimeError('private conversation party failed; inspect '+str(logs))
   time.sleep(.1)
  assert all(p.returncode==0 for p in procs)
 finally:
  for p in procs:
   if p.poll() is None:p.kill()
  for p in procs:p.wait()
  for s in streams:s.close()
 frames=[]
 for party in range(5):
  text=(logs/f'party-{party}.log').read_text();assert 'REJECT 1' in text
  frames.append([line.split()[2] for line in text.splitlines() if line.startswith('FRAME ')])
 assert all(x==frames[0] for x in frames) and len(frames[0])==2 and frames[0][0]!=frames[0][1]
 i=bytes(initial);steps=[]
 for step,wire in enumerate(frames[0]):
  expected,state=native_inner(i);d=oracle([dict(mode='relay',wire=wire)])[0]
  assert d['id']==127+step and d['access_key']==metadata(0,127)[16:32].hex()
  decrypted=oracle([dict(mode='sealed_decrypt',wire=d['ciphertext'],recipient_secret=fixture['recipient_secret'],root_public=fixture['root_public'])])[0]
  assert decrypted==dict(inner=expected.hex(),certificate_valid=True)
  corrupt=bytearray.fromhex(d['ciphertext']);corrupt[-1]^=1
  assert 'error' in oracle([dict(mode='sealed_decrypt',wire=corrupt.hex(),recipient_secret=fixture['recipient_secret'],root_public=fixture['root_public'])])[0]
  steps.append(dict(signal_counter=int.from_bytes(i[1:5],'big'),pq_counter_before=int.from_bytes(i[105:109],'big'),request_id=d['id'],inner_bytes=len(expected),websocket_bytes=len(bytes.fromhex(wire))))
  mutable=bytearray(i);mutable[41:73]=state[:32];mutable[1:5]=state[32:36];mutable[73:105]=state[36:68];mutable[105:109]=state[68:72];i=bytes(mutable)
 assert before=={str(p.relative_to(ROOT)):sha(p) for p in sources},'native sources changed during test'
 report={'passed':True,'parties':5,'threshold':2,'public_synthetic_fixture_only':True,'steps':steps,
  'native_computed_dh_and_fresh_ephemeral':True,'fresh_independent_websocket_mask':True,'raw_dh_scalar_inputs':False,
  'unopened_state_and_request_id_reused_in_native_store':True,'actual_pinned_decrypt_certificate_tamper_and_relay_schema_verified':True,
  'sender_binding_rejected':True,'temporary_fsynced_attempt_fence_used':True,'recoverable_shared_store':False,
  'opened_outputs':'Synthetic final payload/status only; no state, DH, scalar or request-ID share opening.',
  'synthetic_response_acknowledgement_only':True,'actual_response_parser_or_tls_executed':False,
  'elapsed_seconds':time.monotonic()-start,'timing_scope':'Startup plus three component invocations; not persistent delivery throughput.',
  'source_sha256':before,'fixture_binary_sha256':sha(binary),'manifest_sha256':sha(manifest),
  'oracle_sha256':sha(ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'),
  'logs':str(logs.relative_to(ROOT)),'integer_semantic_refinements_proved':False,'full_rust_aeneas_refinement':False,'production_ready':False}
 (HERE/'native-report.json').write_text(json.dumps(report,indent=2)+'\n');print('Five-party private variable conversation store passed; actual target decrypt and width transitions',flush=True)
if __name__=='__main__':main()
