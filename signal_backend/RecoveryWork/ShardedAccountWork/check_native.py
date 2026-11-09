#!/usr/bin/env python3
"""Five-party public directory roots via the actual coordinator/journal."""
import hashlib,json,os,pathlib,shutil,subprocess,tempfile,time
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';binary=ROOT/'.deps/signal-sharded-account-fixture';manifest=ROOT/'.deps/private-record-admission-native/v1-candidate-1/admission.manifest'
 stage=ROOT/'.deps/signal-sharded-account-native/v1-public';stage.mkdir(parents=True,exist_ok=True);data=stage/'Player-Data';data.mkdir(exist_ok=True)
 if not(stage/'Programs').exists():(stage/'Programs').symlink_to(manifest.parent/'Programs',target_is_directory=True)
 credentials=ROOT/'.deps/private-canonical-owner-native/v1-candidate-1/Player-Data'
 copied={}
 for pattern in ['*.pem','*.key','*.0']:
  for path in credentials.glob(pattern):shutil.copyfile(path,data/path.name);copied[path.name]=sha(data/path.name);assert copied[path.name]==sha(path)
 assert len(copied)==15
 logs=pathlib.Path(tempfile.mkdtemp(prefix='run-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5);archive=logs/'account'
 owned=list(HERE.glob('*.h'))+[HERE/'fixture.cpp',HERE/'Makefile',pathlib.Path(__file__),HERE.parent/'AccountCheckpointCoordinator.h',HERE.parent/'Evidence.h',HERE.parent/'CiphertextStore.h',HERE.parent/'PublicCheckpointStore.h']
 pins={str(p.relative_to(ROOT)):sha(p)for p in owned};products={str(p.relative_to(ROOT)):sha(p)for p in [binary,runtime/'libSPDZ.so',manifest]};cases=[];cleanup=[];error=None
 try:
  for index,mode in enumerate(['write','read','invalid','reserve','reject']):
   procs=[];streams=[];start=time.monotonic();case_error=None
   try:
    for party in range(5):
     stream=(logs/f'{mode}-party-{party}.log').open('w');streams.append(stream)
     procs.append(subprocess.Popen([str(binary),str(party),str(hosts),str(31100+10*index),str(manifest),str(archive),mode],cwd=stage,env=dict(os.environ,DYLD_LIBRARY_PATH=str(runtime)),stdout=stream,stderr=subprocess.STDOUT))
    print('LIVE '+mode+' pids='+','.join(str(p.pid)for p in procs),flush=True);deadline=start+90
    while any(p.poll()is None for p in procs):
     if any(p.poll()not in [None,0]for p in procs):raise RuntimeError('party_failure')
     if time.monotonic()>deadline:raise RuntimeError('deadline')
     time.sleep(.1)
    assert all(p.returncode==0 for p in procs)
   except Exception as e:case_error=type(e).__name__;raise
   finally:
    for p in procs:
     if p.poll()is None:p.kill();cleanup.append(dict(mode=mode,action='forced_child_stop'))
    for p in procs:p.wait()
    for stream in streams:stream.close()
    cases.append(dict(mode=mode,exit_codes=[p.returncode for p in procs],seconds=time.monotonic()-start,error=case_error))
   for party in range(5):
    records=[json.loads(line.split(' ',1)[1])for line in(logs/f'{mode}-party-{party}.log').read_text().splitlines()if line.startswith('SHARDED_ACCOUNT ')];assert len(records)==1 and records[0]['passed']
 except Exception as e:error=type(e).__name__
 integrity=all(sha(ROOT/p)==digest for p,digest in {**pins,**products}.items())
 report=dict(passed=error is None and not cleanup and integrity,candidate_only=True,actual_five_node_coordinator=True,actual_journal=True,quorum=4,threshold=2,statistical_parameter=128,public_shards_only=True,private_semantic_validation=False,provider_activation=False,cases=cases,error=error,cleanup=cleanup,integrity=integrity,logs=str(logs.relative_to(ROOT)),source_sha256=pins,product_sha256=products,credential_hashes=copied)
 (HERE/'native-report.json').write_text(json.dumps(report,indent=2)+'\n');(logs/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k not in ['source_sha256','product_sha256','credential_hashes']},indent=2),flush=True)
 if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
