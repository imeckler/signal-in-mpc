"""Matched diagnostic baseline, synthetic fixture only; no application run."""
from pathlib import Path
import hashlib,json,os,signal,subprocess,time,secrets
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent
RUNTIME=ROOT/'.deps/tls-backend-diagnostic-runtime/MP-SPDZ';STAGE=ROOT/'.deps/tls-backend-diagnostic-programs'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 library=STAGE/'libSPDZ.so'
 if not library.exists():library.symlink_to(RUNTIME/'libSPDZ.so')
 assert library.resolve()==(RUNTIME/'libSPDZ.so').resolve()
 out=ROOT/'benchmarks/results/raw/ccd-diagnostic-micro'/secrets.token_hex(8);out.mkdir(parents=True);print(out,flush=True)
 with (out/'ssl.log').open('w') as log:subprocess.run(['bash',str(ROOT/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),'5'],cwd=STAGE,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
 hosts=out/'hosts';hosts.write_text('127.0.0.1\n'*5)
 tracked=[WORK/'ccd_micro_fixture.cpp',WORK/'PublicProtocolMetrics.h',WORK/'diagnostics.patch',RUNTIME/'libSPDZ.so',RUNTIME.parent/'tls-ccd-diagnostic-fixture',STAGE/'programs.manifest']
 hashes={str(p.relative_to(ROOT)):sha(p) for p in tracked};processes=[];logs=[];errors=[];started=time.monotonic()
 report={'passed':False,'scope':'CCD128 diagnostic microfixture, synthetic comparison flags only; no backend switch','source_product_sha256':hashes,'logs':str(out.relative_to(ROOT))}
 try:
  for party in range(5):
   log=(out/f'party-{party}.log').open('w');logs.append(log)
   processes.append(subprocess.Popen([str(RUNTIME.parent/'tls-ccd-diagnostic-fixture'),str(party),str(hosts),'22300',str(STAGE/'programs.manifest')],cwd=STAGE,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True))
  cases=[]
  for party,p in enumerate(processes):
   stdout,_=p.communicate(timeout=max(1,600-(time.monotonic()-started)));(out/f'party-{party}.stdout').write_text(stdout);assert p.returncode==0,(party,p.returncode)
   rows=[json.loads(line[11:]) for line in stdout.splitlines() if line.startswith('DIAGNOSTIC ')];assert len(rows)==3 and 'diagnostic CCD microfixture passed' in stdout;cases.append(rows)
  report.update(passed=True,parties=cases)
 except Exception as error:report['error']=repr(error)
 finally:
  for p in processes:
   if p.poll()is None:
    try:os.killpg(p.pid,signal.SIGKILL)
    except PermissionError:
     try:p.kill()
     except Exception as error:errors.append(repr(error))
    except ProcessLookupError:pass
  for p in processes:
   try:p.wait(timeout=10)
   except Exception as error:errors.append(repr(error))
  for log in logs:log.close()
  report.update(elapsed_python_awake_seconds=time.monotonic()-started,exit_codes=[p.returncode for p in processes],cleanup_errors=errors,integrity_verified=all(sha(p)==hashes[str(p.relative_to(ROOT))] for p in tracked))
  report['passed']=report['passed']and not errors and report['integrity_verified'];(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');(WORK/'ccd-native-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k] for k in ['passed','exit_codes','elapsed_python_awake_seconds','cleanup_errors']},indent=2),flush=True)
 if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
