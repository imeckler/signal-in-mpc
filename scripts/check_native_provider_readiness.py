#!/usr/bin/env python3
"""Five-party public local-failure convergence before any producer VM."""
from pathlib import Path
import hashlib,json,secrets,subprocess,time
ROOT=Path(__file__).resolve().parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 out=ROOT/'benchmarks/results/raw/provider-readiness'/secrets.token_hex(8);out.mkdir(parents=True);working=out/'working';working.mkdir()
 runtime=ROOT/'.deps/tls-session-runtime';baseline=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 with (out/'certificates.log').open('w') as f:subprocess.run(['bash',str(baseline/'Scripts/setup-ssl.sh'),'5'],cwd=working,stdout=f,stderr=subprocess.STDOUT,check=True)
 hosts=out/'hosts';hosts.write_text('127.0.0.1\n'*5)
 names=[Path(__file__),ROOT/'handshake_backend/NativeCollective.h',ROOT/'handshake_backend/WebSocketWork/readiness_native_fixture.cpp',ROOT/'handshake_backend/SessionWork/NativeLifecycle.h',ROOT/'handshake_backend/SessionWork/ErasedHostCall.h',runtime/'tls-readiness-negative-fixture',runtime/'MP-SPDZ/libSPDZ.so']
 hashes={str(p.relative_to(ROOT)):digest(p) for p in names};processes=[];logs=[];cleanup=[];started=time.monotonic();report={'passed':False,'native_mpc_executed':False,'private_producer_vm_entered':False,'source_and_product_sha256':hashes,'logs':str(out.relative_to(ROOT))}
 try:
  for party in range(5):
   f=(out/f'party-{party}.log').open('w');logs.append(f)
   processes.append(subprocess.Popen([str(runtime/'tls-readiness-negative-fixture'),str(party),str(hosts),'21300'],cwd=working,stdout=f,stderr=subprocess.STDOUT))
  for party,p in enumerate(processes):
   assert p.wait(timeout=max(1,120-(time.monotonic()-started)))==0,('readiness party failed',party)
   assert 'collective local failure rejected; no producerVM; erasure barrier passed' in (out/f'party-{party}.log').read_text()
  assert all(digest(p)==hashes[str(p.relative_to(ROOT))] for p in names),'readiness source changed'
  report.update(passed=True,native_mpc_executed=True,all_five_rejected_local_failure=True,erasure_barrier_passed=True)
 except Exception as error:report['error']=repr(error)
 finally:
  for p in processes:
   if p.poll() is None:
    try:p.terminate()
    except ProcessLookupError:pass
    except Exception as error:cleanup.append(('terminate',p.pid,repr(error)))
  for p in processes:
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:
    try:p.kill();p.wait(timeout=5)
    except Exception as error:cleanup.append(('reap',p.pid,repr(error)))
  for f in logs:f.close()
  report.update(cleanup_errors=cleanup,exit_codes=[p.returncode for p in processes],elapsed_seconds=time.monotonic()-started)
  if cleanup:report['passed']=False
  text=json.dumps(report,indent=2)+'\n';(out/'report.json').write_text(text);(ROOT/'benchmarks/results/tls-native-provider-readiness.json').write_text(text);print(text)
 if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
