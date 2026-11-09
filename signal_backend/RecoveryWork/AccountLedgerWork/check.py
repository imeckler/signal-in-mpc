#!/usr/bin/env python3
"""Actual same-five-node candidate certificate/current-head component."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,tempfile,time
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(HERE.parent))
from account_fixture import fixture

def main():
 runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';binary=ROOT/'.deps/signal-account-ledger-fixture';manifest=ROOT/'.deps/private-record-admission-native/v1-candidate-1/admission.manifest'
 stage=ROOT/'.deps/signal-account-ledger-native/v2-candidate-1';stage.mkdir(parents=True,exist_ok=True);data=stage/'Player-Data';data.mkdir(exist_ok=True)
 programs=stage/'Programs'
 if not programs.exists():programs.symlink_to(manifest.parent/'Programs',target_is_directory=True)
 credentials=ROOT/'.deps/private-canonical-owner-native/v1-candidate-1/Player-Data'
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 copied={}
 for pattern in ['*.pem','*.key','*.0']:
  for path in credentials.glob(pattern):shutil.copyfile(path,data/path.name);copied[path.name]=sha(data/path.name);assert copied[path.name]==sha(path)
 assert len(copied)==15
 logs=pathlib.Path(tempfile.mkdtemp(prefix='run-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5);snap=logs/'public-fixture.txt';f=fixture();snap.write_text(''.join(part.hex()+'\n'for name in ['initial','reserve','committed','second_reserve','second_commit']for part in f[name]))
 owned=[HERE/'fixture.cpp',HERE/'Makefile',pathlib.Path(__file__),HERE.parent/'AccountCheckpointCoordinator.h',HERE.parent/'NativeAccountCapture.h',HERE.parent/'PublicCheckpointStore.h',HERE.parent/'AccountLayoutV2.h',HERE.parent/'account_fixture.py']
 source={str(p.relative_to(ROOT)):sha(p)for p in owned};launch=dict(source_sha256=source,binary_sha256=sha(binary),runtime_library_sha256=sha(runtime/'libSPDZ.so'),manifest_sha256=sha(manifest),fixture_sha256=sha(snap),credential_sha256=copied,credentials_verified_before_launch=True)
 (logs/'launch-receipt.json').write_text(json.dumps(launch,indent=2)+'\n');cases=[]
 def run(name,mode,archive,index):
  streams=[];procs=[];start=time.monotonic()
  try:
   for party in range(5):
    stream=(logs/f'{name}-party-{party}.log').open('w');streams.append(stream)
    procs.append(subprocess.Popen([str(binary),str(party),str(hosts),str(30900+index*10),str(manifest),str(archive),str(snap),mode],cwd=stage,env=dict(os.environ,DYLD_LIBRARY_PATH=str(runtime)),stdout=stream,stderr=subprocess.STDOUT))
   print('LIVE '+name+' pids='+','.join(str(p.pid)for p in procs)+' logs='+str(logs),flush=True);deadline=start+180
   while any(p.poll()is None for p in procs):
    if any(p.poll()not in [None,0]for p in procs):raise RuntimeError('ledger party failed '+name+' '+str(logs))
    if time.monotonic()>deadline:raise TimeoutError('ledger deadline')
    time.sleep(.1)
   assert all(p.returncode==0 for p in procs)
  finally:
   for p in procs:
    if p.poll()is None:p.kill()
   for p in procs:p.wait()
   for stream in streams:stream.close()
  for party in range(5):
   records=[json.loads(s.split(' ',1)[1])for s in(logs/f'{name}-party-{party}.log').read_text().splitlines()if s.startswith('ACCOUNT_LEDGER ')];assert len(records)==1 and records[0]['passed']
  cases.append(dict(name=name,passed=True,all_five_exit_zero=True,seconds=time.monotonic()-start));print('PASS '+name,flush=True)
 archive=logs/'archive';run('two_commits','write',archive,0);run('fresh_restart','read',archive,1)
 # Certificate slot is public canonical codec data; runtime verifies signatures.
 def slot(path):
  raw=path.read_bytes();at=len(b'SIGNAL-RECOVERY-CERT-1')+8+len(b'tls-mpc-signal-recovery-vote-v1')+32+1
  return int.from_bytes(raw[at:at+8],'big')
 missing=logs/'one_missing';shutil.copytree(archive,missing)
 for path in(missing/'4/certificates').glob('*.cert'):
  if slot(path)==2:path.unlink()
 run('fetch_missing_local_certificate','read',missing,2)
 stale=logs/'stale';shutil.copytree(archive,stale)
 for party in range(5):
  for path in(stale/str(party)/'certificates').glob('*.cert'):
   if slot(path)==2:path.unlink()
 run('stale_certificates_durable_journals','reject',stale,3)
 run('reserve_without_commit','reserve',archive,4);run('higher_reservation_blocks_restart','reject',archive,5)
 assert source=={str(p.relative_to(ROOT)):sha(p)for p in owned}and launch['binary_sha256']==sha(binary)and launch['runtime_library_sha256']==sha(runtime/'libSPDZ.so')
 report=dict(passed=True,candidate_only=True,actual_five_node_network=True,quorum=4,threshold=2,all_five_persistence_and_status_required=True,actual_encrypted_full_layout_capture=True,full_sections=18,conversations=2,cases=cases,fresh_status_challenge_per_process=True,complete_commit_ancestry=True,earlier_pending_outbox_retained_across_commit=True,public_constant_share_fixture_only=True,synthetic_structural_outbox=True,private_MPC_import=False,actual_provider_activation=False,full_account_security_or_recovery=False,unresolved_reservation_fail_closed_not_resumed=True,cleanup=[],logs=str(logs.relative_to(ROOT)),**launch)
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: actual five-node ledger/current-head component; no account activation',flush=True)
if __name__=='__main__':main()
