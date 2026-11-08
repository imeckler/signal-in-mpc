"""Tiny matched binary component experiment; no mixed/session/lifecycle claim."""
from pathlib import Path
import argparse,hashlib,json,os,signal,subprocess,time,secrets
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent;RUNTIME=ROOT/'.deps/tls-bmr128-candidate/MP-SPDZ'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run_backend(backend,out):
 stage=ROOT/f'.deps/tls-{backend}128-pure-and';binary=RUNTIME.parent/f'tls-{backend}128-component'
 library=stage/'libSPDZ.so'
 if not library.exists():library.symlink_to(RUNTIME/'libSPDZ.so')
 assert library.resolve()==(RUNTIME/'libSPDZ.so').resolve()
 with (out/f'{backend}-ssl.log').open('w') as log:subprocess.run(['bash',str(ROOT/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),'5'],cwd=stage,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
 (stage/'Player-Data/Input-P0-0').write_text(str(0x255AA55AA55AA55A)+'\n');(stage/'Player-Data/Input-P1-0').write_text(str(0x0FF00FF00FF00FF0)+'\n')
 tracked=[binary,RUNTIME/'libSPDZ.so',RUNTIME/'BMR/config.h',WORK/'pure_and.mpc',WORK/f'{backend}128_component_main.cpp',WORK/'emit_backend_totals.h']
 tracked += [p for p in (stage/'Programs').rglob('*')if p.is_file()];hashes={str(p.relative_to(ROOT)):sha(p) for p in tracked}
 processes=[];logs=[];errors=[];start=time.monotonic();result={'passed':False,'source_product_sha256':hashes}
 try:
  for party in range(5):
   log=(out/f'{backend}-party-{party}.log').open('w');logs.append(log)
   processes.append(subprocess.Popen([str(binary),'-N','5','-T','2','-S','128','-p',str(party),'-pn',str(25300 if backend=='ccd'else 26300),'-h','127.0.0.1','pure_and'],cwd=stage,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True))
  parties=[]
  for party,p in enumerate(processes):
   stdout,_=p.communicate(timeout=max(1,120-(time.monotonic()-start)));(out/f'{backend}-party-{party}.stdout').write_text(stdout);assert p.returncode==0,(backend,party,p.returncode)
   compare=[l for l in stdout.splitlines()if l.startswith('DIAGNOSTIC_COMPARE ')];assert compare==['DIAGNOSTIC_COMPARE 1']*3 if party==0 else compare in [[],['DIAGNOSTIC_COMPARE 1']*3],compare
   totals=[json.loads(l[len('DIAGNOSTIC_TOTAL '):])for l in stdout.splitlines()if l.startswith('DIAGNOSTIC_TOTAL ')];assert len(totals)==1
   parties.append(totals[0])
  result.update(passed=True,parties=parties)
 except Exception as error:result['error']=repr(error)
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
  result.update(elapsed_python_awake_seconds=time.monotonic()-start,exit_codes=[p.returncode for p in processes],cleanup_errors=errors,integrity_verified=all(sha(p)==hashes[str(p.relative_to(ROOT))]for p in tracked));result['passed']=result['passed']and not errors and result['integrity_verified']
 return result
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--backend',choices=['both','ccd','bmr'],default='both');args=parser.parse_args()
 out=ROOT/'benchmarks/results/raw/pure-and-backend'/secrets.token_hex(8);out.mkdir(parents=True);print(out,flush=True)
 report={'scope':'5party/t2/security128 tiny purebinary comparison;3repeatedstate steps/381ANDs inclcomparison; noFp conversion, secret retirement, tamper, network performance or application capability claim','compiler_flags':'-B64 -M; BMR additionally-G','no_native_workload_overlap':True,'cases':{}}
 backends=['ccd','bmr']if args.backend=='both'else[args.backend]
 for backend in backends:
  report['cases'][backend]=run_backend(backend,out)
  if not report['cases'][backend]['passed']:break
 report['passed']=len(report['cases'])==len(backends) and all(v['passed']for v in report['cases'].values());text=json.dumps(report,indent=2)+'\n';(out/'report.json').write_text(text);(WORK/'pure-and-native-report.json').write_text(text);print(json.dumps({'passed':report['passed'],'cases':{k:{p:v[p]for p in ['passed','elapsed_python_awake_seconds','exit_codes']}for k,v in report['cases'].items()}},indent=2),flush=True)
 if not report['passed']:raise SystemExit(1)
