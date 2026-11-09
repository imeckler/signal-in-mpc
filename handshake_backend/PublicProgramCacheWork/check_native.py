#!/usr/bin/env python3
"""Five-party private Boolean batch correctness/costs; not full-service throughput."""
from pathlib import Path
import hashlib,json,os,secrets,signal,subprocess,time,argparse
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
RUNTIME=ROOT/'.deps/tls-public-program-cache-runtime-v2/MP-SPDZ';STAGE=ROOT/'.deps/throughput-public-cache-fixture-v2'
clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--mixed',action='store_true');args=parser.parse_args();mixed=args.mixed
 binary=RUNTIME.parent/'tls-native-public-cache-fixture';manifest=STAGE/'batch.manifest'
 out=ROOT/'benchmarks/results/raw'/'private-native-public-cache'/secrets.token_hex(8);out.mkdir(parents=True);print(out,flush=True)
 library=STAGE/'libSPDZ.so'
 if not library.exists():library.symlink_to(RUNTIME/'libSPDZ.so')
 assert library.resolve()==(RUNTIME/'libSPDZ.so').resolve()
 with (out/'ssl.log').open('w')as log:subprocess.run(['bash',str(ROOT/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),'5'],cwd=STAGE,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
 hosts=out/'hosts';hosts.write_text('127.0.0.1\n'*5)
 tracked=[WORK/'native_cache_fixture.cpp',Path(__file__),WORK/'PinnedCacheAdmission.h',WORK/'PublicCodeCache.h',WORK/'PinnedPublicCode.h',RUNTIME/'libSPDZ.so',binary,manifest,ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/OwnedSecrets.h']
 tracked += [RUNTIME/p for p in ['Processor/BaseMachine.h','Processor/BaseMachine.cpp','Processor/Program.h','Processor/Program.cpp','Processor/Machine.h','Processor/Machine.hpp','Tools/PublicCodeCache.h','Tools/PinnedPublicCode.h']]
 hashes={str(p.relative_to(ROOT)):sha(p)for p in tracked};children=[];logs=[];errors=[];started=clock()
 report={'passed':False,'mixed_field_included':mixed,'scope':'Candidate public-only cache: adjacent/interleaved reuse and epoch renewal with fresh secret execution; aggregate equality only; no application throughput or production promotion','timing_clock':'CLOCK_MONOTONIC_RAW','source_product_sha256':hashes,'logs':str(out.relative_to(ROOT))}
 try:
  for party in range(5):
   log=(out/f'party-{party}.log').open('w');logs.append(log)
   child=subprocess.Popen([str(binary),str(party),str(hosts),'30600',str(manifest)]+(['mixed']if mixed else[]),cwd=STAGE,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True);children.append(child);print('party='+str(party)+' pid='+str(child.pid),flush=True)
  cases=[]
  for party,child in enumerate(children):
   text,_=child.communicate(timeout=max(1,600-(clock()-started)));(out/f'party-{party}.stdout').write_text(text)
   assert child.returncode==0,(party,child.returncode)
   rows=[json.loads(l.split(' ',1)[1])for l in text.splitlines()if l.startswith('CACHE_METRIC ')]
   assert len(rows)==1 and 'private native cache fixture passed'in text and 'CACHE_FAILURE_CLOSED 1'in text
   assert rows[0]['hits']>=5 and rows[0]['loads']==6 and rows[0]['epoch']==1
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
