#!/usr/bin/env python3
"""Five-party local authenticated CCD failure fixture; no live service effects."""
from pathlib import Path
import subprocess,json,hashlib,time,secrets,shutil,os,signal
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
RUNTIME=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ'
STAGE=ROOT/'.deps/tls-caught-failure-programs'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 if not STAGE.exists():
  STAGE.mkdir();shutil.copytree(ROOT/'.deps/tls-backend-diagnostic-programs/Programs',STAGE/'Programs');shutil.copy2(ROOT/'.deps/tls-backend-diagnostic-programs/programs.manifest',STAGE/'programs.manifest');(STAGE/'libSPDZ.so').symlink_to(RUNTIME/'libSPDZ.so')
 out=ROOT/'benchmarks/results/raw/caught-failure'/secrets.token_hex(8);out.mkdir(parents=True);print(out,flush=True)
 with (out/'ssl.log').open('w') as log:subprocess.run(['bash',str(ROOT/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),'5'],cwd=STAGE,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
 hosts=out/'hosts';hosts.write_text('127.0.0.1\n'*5)
 tracked=[WORK/'caught_failure_fixture.cpp',WORK/'caught-failure.patch',WORK/'FailureScope.h',WORK/'SocketCancellation.h',RUNTIME/'libSPDZ.so',RUNTIME.parent/'tls-caught-failure-fixture',STAGE/'programs.manifest']
 prepare=json.loads((WORK/'runtime-prepare.json').read_text())
 for name in prepare['base_source_sha256']:
  p=RUNTIME/name
  if p.is_file():tracked.append(p)
 snapshot=out/'snapshot';snapshot.mkdir()
 for p in tracked:
  rel=p.relative_to(ROOT);target=snapshot/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,target)
 hashes={str(p.relative_to(ROOT)):sha(p) for p in tracked};report=dict(passed=False,candidate_only=True,logs=str(out.relative_to(ROOT)),cases=[],source_product_sha256=hashes,scope='one VM worker, five authenticated parties, CCD128, host-owned inputs cleared; no crash/OS erasure claim')
 try:
  for index,mode in enumerate(['positive','tamper','protocol','teardown','partial']):
   processes=[];logs=[];cleanup=[];started=time.monotonic();case=dict(mode=mode,passed=False)
   try:
    for party in range(5):
     log=(out/f'{mode}-{party}.log').open('w');logs.append(log)
     processes.append(subprocess.Popen([str(RUNTIME.parent/'tls-caught-failure-fixture'),str(party),str(hosts),str(28600+index*100),str(STAGE/'programs.manifest'),mode],cwd=STAGE,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True))
    for party,p in enumerate(processes):
     stdout,_=p.communicate(timeout=max(1,90-(time.monotonic()-started)));(out/f'{mode}-{party}.stdout').write_text(stdout)
     assert p.returncode==0,(mode,party,p.returncode)
     rows=[json.loads(x[16:]) for x in stdout.splitlines() if x.startswith('FAILURE_FIXTURE ')]
     assert len(rows)==1 and rows[0]['passed'] and rows[0]['mode']==mode,(mode,party,'missing receipt')
    case['passed']=True;case['thread_receipts']=[json.loads((out/f'{mode}-{party}.stdout').read_text().split('FAILURE_FIXTURE ')[1].splitlines()[0]) for party in range(5)]
   except Exception as error:case['error']=repr(error)
   finally:
    for p in processes:
     if p.poll() is None:
      try:os.killpg(p.pid,signal.SIGKILL)
      except PermissionError:
       try:p.kill()
       except Exception as e:cleanup.append(repr(e))
      except ProcessLookupError:pass
    for p in processes:
     try:p.wait(timeout=10)
     except Exception as e:cleanup.append(repr(e))
    for log in logs:log.close()
    case.update(exit_codes=[p.returncode for p in processes],elapsed_python_awake_seconds=time.monotonic()-started,cleanup_errors=cleanup)
    case['passed']=case['passed'] and not cleanup;report['cases'].append(case);print(json.dumps(case),flush=True)
   if not case['passed']:break
  report['passed']=len(report['cases'])==5 and all(c['passed'] for c in report['cases'])
 finally:
  report['integrity_verified']=all(sha(ROOT/name)==value for name,value in hashes.items());report['passed'] &= report['integrity_verified']
  (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');(WORK/'native-report.json').write_text(json.dumps(report,indent=2)+'\n')
 if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
