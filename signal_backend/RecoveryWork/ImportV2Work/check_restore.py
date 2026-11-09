#!/usr/bin/env python3
"""Fresh-process partial Signal snapshot import/lifecycle/continuation fixture."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,tempfile,time
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'SignalReference/PrivateRecordWork'))
from SignalReference.RelayServiceWork.check import oracle,metadata
from check import make,record
from check_send import flatten
from check_binding import service

def main():
 stage=ROOT/'.deps/private-canonical-restore-native/v1-candidate-1';runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';binary=ROOT/'.deps/signal-canonical-restore-fixture'
 receipt=json.loads((HERE/'restore-prepare-report.json').read_text());previous=json.loads((HERE.parent/'canonical-native-report.json').read_text());old_logs=ROOT/previous['logs'];archive=old_logs/'public-fixture.txt'
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 assert sha(runtime/'libSPDZ.so')==receipt['runtime_library_sha256'] and sha(stage/'base.manifest')==receipt['base_manifest_sha256'] and sha(stage/'extension.manifest')==receipt['extension_manifest_sha256']
 runtime_evidence=json.loads((ROOT/'handshake_backend/ExceptionWork/native-report.json').read_text());runtime_sources={k:v for k,v in runtime_evidence['source_product_sha256'].items()if k.startswith(str(runtime.relative_to(ROOT))+'/')and pathlib.Path(k).suffix in ['.h','.hpp','.cpp']}
 for source,want in runtime_sources.items():assert sha(ROOT/source)==want,('changed exception runtime source',source)
 fixture=oracle([dict(mode='sealed',seed=19,inner='')])[0];target=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-canonical-owner-oracle'
 query=dict(seed=19,steps=3,alice_secret=fixture['sender_secret'],bob_secret=fixture['recipient_secret'],plaintext=(b'E'*79+b'\x80').hex())
 def ask(value):return json.loads(subprocess.check_output([str(target)],input=json.dumps(value)+'\n',text=True))
 rows=ask(query)['rows'];initial=service(rows[0]);f=bytes.fromhex(fixture['input']);initial[32:292]=f[160:420];initial[474:554]=bytes.fromhex(query['plaintext']);initial[554:611]=metadata(19,2**63)
 def expected(index):
  row=rows[index];prefix=bytes.fromhex(row['sender_result']);raw=bytearray(initial);raw[333:365]=prefix[1:33];raw[293:297]=prefix[33:37];raw[365:397]=prefix[37:69];raw[397:401]=prefix[69:73];raw[594:602]=(2**63+index+1).to_bytes(8,'big')
  return bytes(flatten(make(bytes.fromhex(row['sender_record_after']),record)))+bytes.fromhex(row['sender_selected_after'])+bytes(raw)
 old_frames=[line.split()[2]for line in (old_logs/'party-0.log').read_text().splitlines()if line.startswith('FRAME ')];assert len(old_frames)==2
 data=stage/'Player-Data';data.mkdir(exist_ok=True)
 for pattern in ['*.pem','*.key','*.0']:
  for path in (ROOT/'.deps/private-canonical-owner-native/v1-candidate-1/Player-Data').glob(pattern):shutil.copyfile(path,data/path.name)
 assert all((data/f'P{party}.pem').exists()and(data/f'P{party}.key').exists()for party in range(5))
 logs=pathlib.Path(tempfile.mkdtemp(prefix='run-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5);resume=logs/'resume-public.txt';resume.write_text(''.join(x.hex()+'\n'for x in [expected(1),expected(2),b'\0'+bytes.fromhex(query['plaintext']),bytes(initial[586:594])]))
 files=[pathlib.Path(__file__),HERE/'restore_fixture.cpp',HERE/'RawFieldReadmitV2.h',HERE/'WipingAllocator.h',HERE/'RestoreMakefile',HERE/'restore-prepare-report.json',HERE.parent/'NativeRecordAdmission.h',HERE.parent/'NativeOwnShareArchive.h',HERE.parent/'NativeCanonicalSendOwner.h',HERE.parent/'NativeRecordBinding.h',ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/SessionWork/NativeLifecycle.h',ROOT/'handshake_backend/SessionWork/ErasedHostCall.h']
 before={str(p.relative_to(ROOT)):sha(p)for p in files};library_hash=sha(runtime/'libSPDZ.so');binary_hash=sha(binary)
 source_archives={str(p.relative_to(ROOT)):sha(p)for party in range(5)for p in pathlib.Path(str(archive)+'-party'+str(party)).glob('blob-*.box')};assert len(source_archives)==20
 launch=dict(source_sha256=before,runtime_library_sha256=library_hash,binary_sha256=binary_hash,runtime_sources_verified=len(runtime_sources),source_archive_sha256=source_archives)
 (logs/'launch-receipt.json').write_text(json.dumps(launch,indent=2)+'\n');cases=[];start=time.monotonic()
 modes=sys.argv[1:]or ['positive','one','two','nonbit','cancel','semantic','aead']
 for index,mode in enumerate(modes):
  assert mode in ['positive','one','two','nonbit','cancel','semantic','aead'];procs=[];streams=[];case_start=time.monotonic()
  try:
   for party in range(5):
    stream=(logs/f'{mode}-party-{party}.log').open('w');streams.append(stream)
    procs.append(subprocess.Popen([str(binary),str(party),str(hosts),str(29400+10*index),str(stage/'base.manifest'),str(stage/'extension.manifest'),str(archive),str(resume),mode],cwd=stage,env=dict(os.environ,DYLD_LIBRARY_PATH=str(runtime)),stdout=stream,stderr=subprocess.STDOUT))
   print('LIVE mode='+mode+' logs='+str(logs)+' pids='+','.join(str(p.pid)for p in procs),flush=True)
   deadline=time.monotonic()+2400
   while any(p.poll()is None for p in procs):
    if any(p.poll()not in [None,0]for p in procs):raise RuntimeError('restore party failed: '+str(logs)+'/'+mode)
    if time.monotonic()>deadline:raise TimeoutError('restore fixture bounded timeout')
    time.sleep(.2)
   assert all(p.returncode==0 for p in procs)
  finally:
   for p in procs:
    if p.poll()is None:p.kill()
   for p in procs:p.wait()
   for stream in streams:stream.close()
  parsed=[]
  for party in range(5):
   text=(logs/f'{mode}-party-{party}.log').read_text();status=[json.loads(line.split(' ',1)[1])for line in text.splitlines()if line.startswith('RESTORE_FIXTURE ')];assert len(status)==1 and status[0]['passed'];parsed.append(status[0])
   if mode in ['positive','semantic']:assert status[0]['helper_completed']==1 and status[0]['import_host_completed'] and status[0]['epoch_host_completed']
   elif mode=='aead':assert status[0]['helper_completed']==0 and not status[0]['import_host_completed'] and not status[0]['epoch_host_completed']
   else:assert status[0]['helper_completed']==1 and status[0]['import_host_completed'] and not status[0]['epoch_host_completed']
  if mode=='positive':
   new=[]
   for party in range(5):
    text=(logs/f'{mode}-party-{party}.log').read_text();old=[line.split()[1]for line in text.splitlines()if line.startswith('OLD ')];fresh=[line.split()[1]for line in text.splitlines()if line.startswith('NEW ')];assert old==[old_frames[-1]] and len(fresh)==1;new.append(fresh[0])
   assert len(set(new))==1;wires=[]
   for index,frame in enumerate(old_frames+[new[0]]):
    decoded=oracle([dict(mode='relay',wire=frame)])[0];assert decoded['id']==2**63+index
    inner=oracle([dict(mode='sealed_decrypt',wire=decoded['ciphertext'],recipient_secret=fixture['recipient_secret'],root_public=fixture['root_public'])])[0];assert inner['certificate_valid'];wires.append(inner['inner'])
   assert ask(dict(query,wires=wires))['rows']==rows
  case=dict(mode=mode,passed=True,parties=5,seconds=time.monotonic()-case_start,status=parsed);cases.append(case);(logs/(mode+'-receipt.json')).write_text(json.dumps(case,indent=2)+'\n');print('PASS mode='+mode,flush=True)
 assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}and sha(runtime/'libSPDZ.so')==library_hash and sha(binary)==binary_hash
 assert source_archives=={p:sha(ROOT/p)for p in source_archives}
 report=dict(passed=True,candidate_only=True,partial_session_snapshot_only=True,actual_source_encrypted_MPC_snapshot=True,fresh_process_fullGF128_checked_import=True,helper_destroyed_before_completed_host_barrier=True,pinned_validator_initializes_VM=True,separate_epoch_and_completed_host_barrier=True,restored_pending_outbox_preserved_in_new_commit='positive'in modes,actual_Rust_third_send_decrypt='positive'in modes,full_account=False,quorum_or_current_head_validation=False,normal_provider_or_TLS_activation=False,synthetic_component_ack_policy=True,production_runtime_promoted=False,runtime=str(runtime.relative_to(ROOT)),cases=cases,seconds=time.monotonic()-start,logs=str(logs.relative_to(ROOT)),source_sha256=before,runtime_library_sha256=library_hash,binary_sha256=binary_hash,source_archive_sha256=source_archives,oracle_binary_sha256=sha(target))
 name='restore-report.json'if len(modes)>1 else 'restore-'+modes[0]+'-report.json';(HERE/name).write_text(json.dumps(report,indent=2)+'\n');print('PASS: partial fresh-process restore/helper/barriers cases='+str(len(cases)),flush=True)
if __name__=='__main__':main()
