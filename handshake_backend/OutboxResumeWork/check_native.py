#!/usr/bin/env python3
import hashlib,json,os,pathlib,shutil,subprocess,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
stage=ROOT/'.deps/tls-outbox-remask-native/v1-candidate-1';runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';binary=stage/'tls-native-outbox-remask-fixture'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[binary,runtime/'libSPDZ.so',HERE/'native_fixture.cpp',ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/OwnedSecrets.h',ROOT/'handshake_backend/SessionWork/NativeLifecycle.h',stage/'remask.manifest']
for line in(stage/'remask.manifest').read_text().splitlines()[1:]:
 digest,path=line.split(' ',1);assert sha(stage/path)==digest;files.append(stage/path)
pins={str(p.relative_to(ROOT)):sha(p)for p in files}
data=stage/'Player-Data';data.mkdir(exist_ok=True)
for pattern in ['*.pem','*.key','*.0']:
 for p in(ROOT/'.deps/private-canonical-owner-native/v1-candidate-1/Player-Data').glob(pattern):shutil.copyfile(p,data/p.name)
logs=pathlib.Path(tempfile.mkdtemp(prefix='run-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5)
procs=[];streams=[];cleanup=[];error=None;started=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
try:
 for i in range(5):
  out=(logs/f'party-{i}.log').open('wb');streams.append(out);procs.append(subprocess.Popen([str(binary),str(i),str(hosts),'30850',str(stage/'remask.manifest')],cwd=stage,env=dict(os.environ,DYLD_LIBRARY_PATH=str(runtime)),stdout=out,stderr=subprocess.STDOUT))
 deadline=time.monotonic()+120
 for p in procs:p.wait(timeout=max(.1,deadline-time.monotonic()))
except subprocess.TimeoutExpired:error='timeout'
except Exception:error='controller-failure'
finally:
 for p in procs:
  if p.poll()is None:
   p.terminate()
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:p.kill();p.wait();cleanup.append('forced-child-kill')
 for out in streams:out.close()
 codes=[p.returncode for p in procs];party0=(logs/'party-0.log').read_text();masks=[list(map(int,line.split()[2:]))for line in party0.splitlines()if line.startswith('REMASK_PUBLIC_MASK ')]
 report={'passed':codes==[0]*5 and not error and not cleanup and len(masks)==2,'party_exit_codes':codes,'controller_error':error,'cleanup':cleanup,'seconds':time.clock_gettime(time.CLOCK_MONOTONIC_RAW)-started,'integrity':all(sha(ROOT/p)==h for p,h in pins.items()),'source_pins':pins,'logs':str(logs.relative_to(ROOT)),'public_fixture_masks':masks,'sampled_masks_distinct':len(masks)==2 and masks[0]!=masks[1],'cases':['two valid remasks with fresh private VM randomness','computed account validity rejection','noncanonical padding rejection'],'all_five_positive_status':all('private native remask fixture passed'in(logs/f'party-{i}.log').read_text()for i in range(5)),'opened_only_public_synthetic_fixture':True,'malformed_mac_test':False,'account_authorization':False,'tls_restore_interop':False}
 report['passed']=report['passed']and report['integrity']and report['all_five_positive_status'];(HERE/'native-report.json').write_text(json.dumps(report,indent=2)+'\n');(logs/'report.json').write_text(json.dumps(report,indent=2)+'\n');shutil.copyfile(HERE/'native_fixture.cpp',logs/'tested-native_fixture.cpp')
 print(json.dumps({k:report[k]for k in ['passed','party_exit_codes','seconds','sampled_masks_distinct']}));assert report['passed']
