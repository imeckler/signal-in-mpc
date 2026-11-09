#!/usr/bin/env python3
import hashlib,json,os,pathlib,shutil,subprocess,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;stage=ROOT/'.deps/tls-public-constant-native/v1';runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';binary=stage/'tls-public-constant-native-fixture';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[binary,runtime/'libSPDZ.so',HERE/'constant_native_fixture.cpp',ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/OwnedSecrets.h',ROOT/'handshake_backend/NativeSession.h',stage/'constants.manifest']
for line in(stage/'constants.manifest').read_text().splitlines()[1:]:
 digest,name=line.split(' ',1);assert sha(stage/name)==digest;files.append(stage/name)
pins={str(p.relative_to(ROOT)):sha(p)for p in files};data=stage/'Player-Data';data.mkdir(exist_ok=True)
for pattern in['*.pem','*.key','*.0']:
 for p in(ROOT/'.deps/private-canonical-owner-native/v1-candidate-1/Player-Data').glob(pattern):shutil.copyfile(p,data/p.name)
logs=pathlib.Path(tempfile.mkdtemp(prefix='run-',dir=stage));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5);processes=[];streams=[];cleanup=[];error=None;started=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
try:
 for i in range(5):
  out=(logs/f'party-{i}.log').open('wb');streams.append(out);processes.append(subprocess.Popen([str(binary),str(i),str(hosts),'30950',str(stage/'constants.manifest')],cwd=stage,env=dict(os.environ,DYLD_LIBRARY_PATH=str(runtime)),stdout=out,stderr=subprocess.STDOUT))
 deadline=time.monotonic()+60
 for p in processes:p.wait(timeout=max(.1,deadline-time.monotonic()))
except subprocess.TimeoutExpired:error='timeout'
except Exception:error='controller-failure'
finally:
 for p in processes:
  if p.poll()is None:
   p.terminate()
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:p.kill();p.wait();cleanup.append('forced-child-kill')
 for out in streams:out.close()
 codes=[p.returncode for p in processes];integrity=all(sha(ROOT/p)==h for p,h in pins.items());passed=codes==[0]*5 and not error and not cleanup and integrity and all('public exact-cell native fixture passed'in(logs/f'party-{i}.log').read_text()for i in range(5))
 report={'passed':passed,'party_exit_codes':codes,'controller_error':error,'cleanup':cleanup,'integrity':integrity,'seconds':time.clock_gettime(time.CLOCK_MONOTONIC_RAW)-started,'source_product_sha256':pins,'logs':str(logs.relative_to(ROOT)),'scope':'Actual Worker.allocate exact-cell check BEFORE VM overwrite, one-cell input/result/copy/interface and authenticated known-public status across epoch renewal. Existing program closure only; no account authorization or full TLS retry claim.'};(HERE/'constants-native-report.json').write_text(json.dumps(report,indent=2)+'\n');(logs/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k]for k in['passed','party_exit_codes','seconds']}));assert passed
