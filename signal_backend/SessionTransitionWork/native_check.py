#!/usr/bin/env python3
"""5-party public fixture, unopened receiving state/key; open comparison bit only."""
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
from signal_backend.SessionTransitionWork.check_active_spqr import varint,BIN
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 stage=ROOT/'.deps/private-active-spqr-receive-native';runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 descriptor='signal_active_spqr_receive_next_32-sbv:[632x1]-sbv:[616x1]'
 check='signal_transition_fixture_equal_616-sbv:[1232x1]-sbv:[8x1]'
 shutil.copy2(ROOT/'programs/signal_transition_fixture_check.mpc',stage/'Programs/Source/signal_transition_fixture_check.mpc')
 subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_transition_fixture_check'],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),check=True,timeout=120)
 manifest=stage/'fixture.manifest';manifest.write_text(build(stage,[descriptor,check]))
 binary=ROOT/'.deps/private-session-transition-fixture'
 sources=[Path(__file__),HERE/'native_fixture.cpp',HERE/'NativeActiveSpqrReceive.h',HERE/'Makefile',ROOT/'programs/signal_active_spqr_receive.mpc',ROOT/'programs/signal_transition_fixture_check.mpc',ROOT/'handshake_backend/NativeWorker.h',ROOT/'TlsMpc/Signal/ActiveSpqrReceive.lean']
 before={str(p.relative_to(ROOT)):sha(p)for p in sources}
 subprocess.run(['make','-C',str(runtime),'-f',str(HERE/'Makefile'),'TRANSITION_WORK='+str(HERE),'TRANSITION_FIXTURE='+str(binary),str(binary)],check=True)
 def oracle(row):
  p=subprocess.run([str(BIN)],input=json.dumps(row)+'\n',text=True,capture_output=True,check=True);return json.loads(p.stdout)
 key=hashlib.sha256(b'public-native-receiving-chain').digest();epoch=127;counter=126;rows=[]
 for step in range(3):
  wire=b'\1'+varint(epoch)+varint(counter+1)+(b'\0'if step<2 else b'')
  answer=oracle(dict(epoch=epoch,counter=counter,chain=key.hex(),wire=wire.hex()))
  state=epoch.to_bytes(8,'big')+key+counter.to_bytes(4,'big')
  raw=state+b'\xff'+len(wire).to_bytes(2,'big')+wire+bytes(32-len(wire))
  if step<2:
   assert answer['accepted'];key=bytes.fromhex(answer['chain']);counter=answer['counter']
   expected=b'\xff'+epoch.to_bytes(8,'big')+key+counter.to_bytes(4,'big')+bytes.fromhex(answer['key'])
  else:assert not answer['accepted'];expected=b'\0'+state+bytes(32)
  rows.append((raw,expected))
 data=stage/'Player-Data';data.mkdir(exist_ok=True)
 for pattern in ['*.pem','*.key','*.0']:
  for p in(runtime/'Player-Data').glob(pattern):shutil.copy2(p,data/p.name)
 logs=Path(tempfile.mkdtemp(prefix='fixture-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5)
 inputs=logs/'public-fixtures.txt';inputs.write_text(''.join(raw.hex()+' '+expected.hex()+'\n'for raw,expected in rows))
 processes=[];streams=[];start=time.monotonic()
 try:
  for party in range(5):
   stream=(logs/f'party-{party}.log').open('w');streams.append(stream)
   processes.append(subprocess.Popen([str(binary),str(party),str(hosts),'19980',str(manifest),str(inputs)],cwd=stage,stdout=stream,stderr=subprocess.STDOUT))
  deadline=start+900
  while any(p.poll()is None for p in processes):
   if time.monotonic()>deadline:raise TimeoutError('active receive native timeout')
   if any(p.poll()not in[None,0]for p in processes):raise RuntimeError('active receive party failed;inspect '+str(logs))
   time.sleep(.1)
  assert all(p.returncode==0 for p in processes)
 finally:
  for p in processes:
   if p.poll()is None:p.kill()
  for p in processes:p.wait()
  for stream in streams:stream.close()
 for party in range(5):
  text=(logs/f'party-{party}.log').read_text();assert all(f'STEP {step} equality passed'in text for step in range(3))
 assert before=={str(p.relative_to(ROOT)):sha(p)for p in sources},'native source changed'
 report=dict(passed=True,parties=5,threshold=2,public_disposable_receiving_fixture_only=True,actual_locked_spqr_receive_oracle=True,
  receiving_chain_counter_key_unopened=True,output_state_reused_as_next_input=True,successful_receives=2,counter_boundary='126→127→128',truncated_private_wire_rejection=True,
  opened='Only secure equality against independently computed PUBLIC oracle constants; never receiving state or message-key shares.',
  full_Signal_MAC_or_DH_transition=False,full_SPQR_state_or_KEM_transition=False,elapsed_seconds=time.monotonic()-start,timing_scope='Startup plus3 candidate operations and3 comparison checks; not service throughput.',
  logs=str(logs.relative_to(ROOT)),manifest_sha256=sha(manifest),binary_sha256=sha(binary),oracle_sha256=sha(BIN),source_sha256=before)
 (HERE/'native-report.json').write_text(json.dumps(report,indent=2)+'\n');print('5party receiving candidate2steps+truncation, unopened state/key passed',flush=True)
if __name__=='__main__':main()
