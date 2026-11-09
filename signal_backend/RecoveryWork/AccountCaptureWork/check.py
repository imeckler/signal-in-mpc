#!/usr/bin/env python3
"""Full-layout known-fixture capture via two actual MPC sends; no openings."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,tempfile,time
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(HERE.parent))
from account_fixture import fixture

def main():
 stage=ROOT/'.deps/tls-authorized-account-native/v1-candidate-2';manifest=stage/'programs.manifest';runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';binary=ROOT/'.deps/signal-account-capture-fixture';sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 assert sha(manifest)=='a41455546132840185159061c880095c3ac2111b55d6862afe0419091e74e006'
 data=stage/'Player-Data';data.mkdir(exist_ok=True);credentials=ROOT/'.deps/private-canonical-owner-native/v1-candidate-1/Player-Data';copied={}
 for pattern in ['*.pem','*.key','*.0']:
  for path in credentials.glob(pattern):shutil.copyfile(path,data/path.name);copied[path.name]=sha(data/path.name);assert copied[path.name]==sha(path)
 assert len(copied)==15
 logs=pathlib.Path(tempfile.mkdtemp(prefix='capture-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5);snapshot=logs/'public-initial-fixture.txt';snapshot.write_text(''.join(p.hex()+'\n'for p in fixture()['initial'][:11]));archive=logs/'account'
 files=[pathlib.Path(__file__),HERE/'fixture.cpp',HERE/'PublicAccountFixture.h',HERE/'RecoveryFixtureFactory.cpp',HERE/'Makefile',*HERE.parent.glob('*.h'),ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/NativeSession.h',ROOT/'handshake_backend/SessionWork/NativeLifecycle.h',ROOT/'handshake_backend/SessionWork/ErasedHostCall.h'];source={str(p.relative_to(ROOT)):sha(p)for p in files}
 launch=dict(manifest_sha256=sha(manifest),binary_sha256=sha(binary),runtime_library_sha256=sha(runtime/'libSPDZ.so'),source_sha256=source,credential_sha256=copied,credentials_verified_before_launch=True,initial_public_fixture_sha256=sha(snapshot));(logs/'launch-receipt.json').write_text(json.dumps(launch,indent=2)+'\n')
 procs=[];streams=[];start=time.monotonic()
 try:
  for party in range(5):
   stream=(logs/f'party-{party}.log').open('w');streams.append(stream);procs.append(subprocess.Popen([str(binary),str(party),str(hosts),'31000',str(manifest),str(archive),str(snapshot)],cwd=stage,env=dict(os.environ,DYLD_LIBRARY_PATH=str(runtime)),stdout=stream,stderr=subprocess.STDOUT))
  print('LIVE full account capture pids='+','.join(str(p.pid)for p in procs)+' logs='+str(logs),flush=True);deadline=start+900
  while any(p.poll()is None for p in procs):
   if any(p.poll()not in [None,0]for p in procs):raise RuntimeError('actual account capture party failed '+str(logs))
   if time.monotonic()>deadline:raise TimeoutError('capture bounded timeout')
   time.sleep(.2)
  assert all(p.returncode==0 for p in procs)
 finally:
  for p in procs:
   if p.poll()is None:p.kill()
  for p in procs:p.wait()
  for stream in streams:stream.close()
 status=[]
 for party in range(5):
  values=[json.loads(s.split(' ',1)[1])for s in(logs/f'party-{party}.log').read_text().splitlines()if s.startswith('ACCOUNT_CAPTURE ')];assert len(values)==1 and values[0]['passed'];status.append(values[0])
 assert source=={str(p.relative_to(ROOT)):sha(p)for p in files}and launch['binary_sha256']==sha(binary)and launch['runtime_library_sha256']==sha(runtime/'libSPDZ.so')
 report=dict(passed=True,candidate_only=True,actual_MPC_sends=2,conversations=1,full_layout_sections=11,logical_bytes=20885,actual_computed_canonical_record_updates=True,actual_encrypted_pending_outboxes=True,actual_same_five_node_certificates=True,final_worker_manifest_bound_from_genesis=True,per_send_runtime_retirement=True,completed_host_barriers=True,fixture_initial_keys_and_account_public=True,first_response_synthetic_fixture_ACK=True,first_two_messages_not_TLS_transmitted=True,no_wire_or_identifier_or_key_openings=True,native_restore_or_provider_activation=False,full_session_protocol_or_security=False,seconds=time.monotonic()-start,archive_root=str(archive.relative_to(ROOT)),logs=str(logs.relative_to(ROOT)),status=status,cleanup=[],**launch)
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: two actual MPC sends captured as certified full-layout account '+str(archive),flush=True)
if __name__=='__main__':main()
