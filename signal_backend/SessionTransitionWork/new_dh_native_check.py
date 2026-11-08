#!/usr/bin/env python3
"""5-party new-DH candidate public fixture; never open root/private/state/key."""
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
from SignalReference.PrivateNewDhReceiveWork.check_model import BIN,TEXT,invoke
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 stage=ROOT/'.deps/private-new-dh-receive-native';runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 descriptor='signal_private_new_dh_receive_256_5-sbv:[6784x1]-sbv:[4864x1]'
 check='signal_new_dh_fixture_equal_4864-sbv:[9728x1]-sbv:[8x1]'
 shutil.copy2(ROOT/'programs/signal_new_dh_fixture_check.mpc',stage/'Programs/Source/signal_new_dh_fixture_check.mpc')
 subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_new_dh_fixture_check'],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),check=True,timeout=120)
 manifest=stage/'fixture.manifest';manifest.write_text(build(stage,[descriptor,check]))
 binary=ROOT/'.deps/private-new-dh-transition-fixture'
 sources=[Path(__file__),HERE/'new_dh_native_fixture.cpp',HERE/'NativeNewDhReceive.h',HERE/'Makefile',ROOT/'programs/signal_private_new_dh_receive.mpc',ROOT/'programs/signal_new_dh_fixture_check.mpc',ROOT/'handshake_backend/NativeWorker.h',ROOT/'TlsMpc/Signal/PrivateNewDhReceiveSplit.lean']
 before={str(p.relative_to(ROOT)):sha(p)for p in sources}
 subprocess.run(['make','-C',str(runtime),'-f',str(HERE/'Makefile'),'TRANSITION_WORK='+str(HERE),'NEW_DH_FIXTURE='+str(binary),str(binary)],check=True)
 text=invoke(TEXT,[dict(mode='text',body='Native received private text ☕'.encode().hex(),timestamp=1900000000000)])[0]
 fixture=invoke(BIN,[dict(seed=7,plaintext=text['padded'])])[0]
 raw=bytes.fromhex(fixture['input']);want=bytes.fromhex(fixture['expected'])
 input=raw[:589]+raw[717:];assert len(input)==848
 bad=bytearray(input);n=int.from_bytes(bad[590:592],'big');bad[592+n-1]^=1
 rows=[(input,want),(bytes(bad),b'\0'+raw[:525]+bytes(82))]
 data=stage/'Player-Data';data.mkdir(exist_ok=True)
 for pattern in ['*.pem','*.key','*.0']:
  for p in(runtime/'Player-Data').glob(pattern):shutil.copy2(p,data/p.name)
 logs=Path(tempfile.mkdtemp(prefix='fixture-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5)
 inputs=logs/'public-fixtures.txt';inputs.write_text(''.join(raw.hex()+' '+expected.hex()+'\n'for raw,expected in rows))
 processes=[];streams=[];start=time.monotonic()
 try:
  for party in range(5):
   stream=(logs/f'party-{party}.log').open('w');streams.append(stream)
   processes.append(subprocess.Popen([str(binary),str(party),str(hosts),'20070',str(manifest),str(inputs)],cwd=stage,stdout=stream,stderr=subprocess.STDOUT))
  deadline=start+900
  while any(p.poll()is None for p in processes):
   if time.monotonic()>deadline:raise TimeoutError('new-DH receive native timeout')
   if any(p.poll()not in[None,0]for p in processes):raise RuntimeError('new-DH receive party failed;inspect '+str(logs))
   time.sleep(.1)
  assert all(p.returncode==0 for p in processes)
 finally:
  for p in processes:
   if p.poll()is None:p.kill()
  for p in processes:p.wait()
  for stream in streams:stream.close()
 for party in range(5):
  text=(logs/f'party-{party}.log').read_text();assert all(f'STEP {step} equality passed'in text for step in range(2))
 assert before=={str(p.relative_to(ROOT)):sha(p)for p in sources},'native source changed'
 report=dict(passed=True,parties=5,threshold=2,public_disposable_fixture_only=True,
  actual_libsignal_receive_oracle=True,joint_private_scalar_and_computed_agreements=True,
  first_receive_checked='Computed status,345 receiving-chain bytes,44 receiving-PQ bytes,82 private-plaintext bytes. Fresh sender/root136 omitted from equality, never opened.',
  MAC_rejection_checked='All608 bytes: old525 state preserved and plaintext zero.',
  opened='Two secure equality bits against public actual-oracle fixtures only; no root/private/state/key values.',
  native_two_way_reply_or_retained_fresh_key_test=False,full_actual_source_refinement=False,full_SPQR_or_bootstrap=False,
  elapsed_seconds=time.monotonic()-start,timing_scope='Startup plus2 receive transactions and2 comparisons; not service throughput.',
  logs=str(logs.relative_to(ROOT)),manifest_sha256=sha(manifest),binary_sha256=sha(binary),oracle_sha256=sha(BIN),source_sha256=before)
 (HERE/'new-dh-native-report.json').write_text(json.dumps(report,indent=2)+'\n');print('5party actual new-DH receive+MAC rejection, comparison bits only passed',flush=True)
if __name__=='__main__':main()
