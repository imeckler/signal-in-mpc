#!/usr/bin/env python3
"""Actual n5 launcher rejection; no private program or account activated."""
import hashlib,json,os,pathlib,shutil,subprocess,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
RUNTIME=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ'
STAGE=ROOT/'.deps/tls-account-admission-launcher';STAGE.mkdir(exist_ok=True)
BINARY=STAGE/'tls-restored-mux-worker'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
with (STAGE/'build.log').open('w') as log:
 subprocess.run(['make','-f',str(ROOT/'handshake_backend/WebSocketWork/Makefile'),'TLS_ROOT='+str(ROOT/'handshake_backend'),'TLS_BUILD='+str(STAGE),str(BINARY)],cwd=RUNTIME,stdout=log,stderr=subprocess.STDOUT,check=True)
public=STAGE/'Worker-Public';public.mkdir(exist_ok=True);marker=public/'admission.txt';marker.write_text('absent resolver control: no private execution\n')
manifest=STAGE/'programs.manifest';manifest.write_text('tls-mpc-pinned-files-v1\n'+sha(marker)+' Worker-Public/admission.txt\n')
data=STAGE/'Player-Data';data.mkdir(exist_ok=True)
for pattern in ['*.pem','*.key','*.0']:
 for p in (ROOT/'.deps/private-canonical-owner-native/v1-candidate-1/Player-Data').glob(pattern):shutil.copyfile(p,data/p.name)
assert all((data/f'P{i}.pem').exists()and(data/f'P{i}.key').exists()for i in range(5))
logs=pathlib.Path(tempfile.mkdtemp(prefix='absent-',dir=STAGE));hosts=logs/'hosts';hosts.write_text('127.0.0.1\n'*5)
sources=[ROOT/'handshake_backend/WebSocketWork/mux_worker_main.cpp',HERE/'RecoveryFactory.h',HERE/'NoAccountRecovery.cpp',ROOT/'signal_backend/RecoveryWork/AccountAdmission.h',RUNTIME/'libSPDZ.so',BINARY]
pins={str(p.relative_to(ROOT)):sha(p) for p in sources};procs=[];streams=[];cleanup=[];codes=[];controller_error=None;started=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
try:
 for i in range(5):
  err=(logs/f'party-{i}.log').open('wb');out=(logs/f'party-{i}.rpc').open('wb');streams.extend([err,out])
  procs.append(subprocess.Popen([str(BINARY),str(i),str(hosts),'30800',str(manifest),'53'*32],cwd=STAGE,env=dict(os.environ,DYLD_LIBRARY_PATH=str(RUNTIME)),stdin=subprocess.DEVNULL,stdout=out,stderr=err))
 deadline=time.monotonic()+60
 for p in procs:codes.append(p.wait(timeout=max(.1,deadline-time.monotonic())))
except subprocess.TimeoutExpired:controller_error="timeout"
except Exception:controller_error="controller-failure"
finally:
 for p in procs:
  if p.poll()is None:
   p.terminate()
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:p.kill();p.wait();cleanup.append('forced-child-kill')
 for s in streams:s.close()
 codes=[p.returncode for p in procs]
 report={'passed':len(codes)==5 and codes==[1]*5 and not cleanup,'party_exit_codes':codes,'cleanup':cleanup,'controller_error':controller_error,'seconds':time.clock_gettime(time.CLOCK_MONOTONIC_RAW)-started,
 'all_reached_absent_resolver':all(b'category=resolver-absent' in(logs/f'party-{i}.log').read_bytes()for i in range(5)),
 'integrity':all(sha(ROOT/p)==h for p,h in pins.items()),'source_pins':pins,'logs':str(logs.relative_to(ROOT)),
 'private_program_executed':False,'authorized_account_created':False,'fresh_tls_positive_validated':False,'production_gate_enabled':False}
 report['passed']=report['passed']and controller_error is None and report['all_reached_absent_resolver']and report['integrity']
 (logs/'report.json').write_text(json.dumps(report,indent=2)+'\n');shutil.copyfile(ROOT/'handshake_backend/WebSocketWork/mux_worker_main.cpp',logs/'tested-mux_worker_main.cpp');shutil.copyfile(BINARY,logs/'tested-worker');(HERE/'absent-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k]for k in ['passed','party_exit_codes','all_reached_absent_resolver','seconds']}))
 assert report['passed']
