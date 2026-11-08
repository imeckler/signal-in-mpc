#!/usr/bin/env python3
"""Five-party private Boolean batch correctness/costs; not full-service throughput."""
from pathlib import Path
import hashlib,json,os,secrets,signal,subprocess,time
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
RUNTIME=ROOT/'.deps/tls-backend-diagnostic-runtime-v4/MP-SPDZ';STAGE=ROOT/'.deps/throughput-batch-tiny-v1'
clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 out=ROOT/'benchmarks/results/raw/private-native-batch'/secrets.token_hex(8);out.mkdir(parents=True);print(out,flush=True)
 library=STAGE/'libSPDZ.so'
 if not library.exists():library.symlink_to(RUNTIME/'libSPDZ.so')
 assert library.resolve()==(RUNTIME/'libSPDZ.so').resolve()
 with (out/'ssl.log').open('w')as log:subprocess.run(['bash',str(ROOT/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),'5'],cwd=STAGE,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
 hosts=out/'hosts';hosts.write_text('127.0.0.1\n'*5)
 tracked=[WORK/'native_batch_fixture.cpp',Path(__file__),ROOT/'backend_adapter/aig_batched.py',RUNTIME/'libSPDZ.so',RUNTIME.parent/'tls-native-batch-fixture',STAGE/'batch.manifest',ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/OwnedSecrets.h']
 hashes={str(p.relative_to(ROOT)):sha(p)for p in tracked};children=[];logs=[];errors=[];started=clock()
 report={'passed':False,'scope':'Private Boolean DAG only, no mixedfield/store/TLS throughput claim; repeated two orders within epoch then renewal per pair; only aggregate equality/rejection flags opened','timing_clock':'CLOCK_MONOTONIC_RAW','source_product_sha256':hashes,'logs':str(out.relative_to(ROOT))}
 try:
  for party in range(5):
   log=(out/f'party-{party}.log').open('w');logs.append(log)
   child=subprocess.Popen([str(RUNTIME.parent/'tls-native-batch-fixture'),str(party),str(hosts),'26900',str(STAGE/'batch.manifest')],cwd=STAGE,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True);children.append(child);print('party='+str(party)+' pid='+str(child.pid),flush=True)
  cases=[]
  for party,child in enumerate(children):
   text,_=child.communicate(timeout=max(1,600-(clock()-started)));(out/f'party-{party}.stdout').write_text(text)
   assert child.returncode==0,(party,child.returncode)
   rows=[json.loads(l.split(' ',1)[1])for l in text.splitlines()if l.startswith('BATCH_METRIC ')]
   assert len(rows)==12 and 'private native batch fixture passed'in text
   assert {(r['count'],r['iteration'],r['mode'])for r in rows}=={(n,i,m)for n in [2,4,8]for i in [0,1]for m in ['sequential','batch']}
   cases.append(rows)
  report.update(passed=True,parties=cases,native_MPC_executed=True)
 except Exception as error:report['error']=repr(error)
 finally:
  for child in children:
   if child.poll()is None:
    try:os.killpg(child.pid,signal.SIGKILL)
    except PermissionError:
     try:child.kill()
     except Exception as error:errors.append(('kill',child.pid,repr(error)))
    except ProcessLookupError:pass
  for child in children:
   try:child.wait(timeout=10)
   except Exception as error:errors.append(('reap',child.pid,repr(error)))
  for log in logs:log.close()
  report.update(elapsed_seconds=clock()-started,controller_pids=[p.pid for p in children],exit_codes=[p.returncode for p in children],cleanup_errors=errors,integrity_verified=all(sha(p)==hashes[str(p.relative_to(ROOT))]for p in tracked))
  report['passed']=report['passed']and not errors and report['integrity_verified'];text=json.dumps(report,indent=2)+'\n';(out/'report.json').write_text(text);(WORK/'native-report.json').write_text(text);print(json.dumps({k:report[k]for k in ['passed','exit_codes','elapsed_seconds','cleanup_errors']}),flush=True)
 if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
