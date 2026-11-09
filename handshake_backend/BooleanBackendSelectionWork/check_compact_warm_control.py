#!/usr/bin/env python3
"""Optional synthetic weaker-profile comparator; never changes production."""
from pathlib import Path
import hashlib,json,os,secrets,shutil,subprocess,time
root=Path(__file__).resolve().parents[2];work=Path(__file__).parent
runtime=root/'.deps/tls-backend-diagnostic-runtime-v4/MP-SPDZ';program=root/'.deps/compact-boolean-warm-control-v1'
out=root/'benchmarks/results/raw/compact-boolean-warm-control'/secrets.token_hex(8);out.mkdir(parents=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
report={'scope':'OPTIONAL BENCHMARK ONLY: n3/t1/stat40 versus n5/t2/stat128; same430075AND synthetic bytecode,1warmup+4measured86015AND iterations, no mixed Fp bridge/application/lifecycle/tamper claim','cases':{},'raw':str(out.relative_to(root)),'passed':False}
print(out,flush=True)
for backend,n,security,port in [('ccd128',5,128,30400),('rep3-stat40',3,40,30500)]:
 binary=runtime.parent/('tls-ccd128-component'if backend=='ccd128'else'tls-rep3-stat40-benchmark')
 stage=out/backend;stage.mkdir();shutil.copytree(program/'Programs',stage/'Programs');(stage/'libSPDZ.so').symlink_to(runtime/'libSPDZ.so')
 with(stage/'ssl.log').open('w')as log:subprocess.run(['bash',str(root/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),str(n)],cwd=stage,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
 for p,value in [(0,0x255AA55AA55AA55A),(1,0x0FF00FF00FF00FF0)]: (stage/f'Player-Data/Input-P{p}-0').write_text((str(value)+'\n')*64)
 tracked=[binary,runtime/'libSPDZ.so',work/'rep3_stat40.cpp',work/'compact_warm_control.mpc',Path(__file__)]+[p for p in(stage/'Programs').rglob('*')if p.is_file()]
 pins={str(p.relative_to(root)):sha(p)for p in tracked};children=[];logs=[];errors=[];start=clock();case={'passed':False,'n':n,'threshold':2 if n==5 else 1,'statistical_security':security,'source_product_sha256':pins}
 try:
  for party in range(n):
   stdout=(stage/f'party{party}.stdout').open('w');stderr=(stage/f'party{party}.stderr').open('w');logs.extend([stdout,stderr])
   cmd=[str(binary),'-S',str(security),'-p',str(party),'-pn',str(port),'-h','127.0.0.1','-b','64','-B','5']
   if n==5:cmd+=['-N','5','-T','2']
   cmd+=['-v','compact_warm_control'];children.append(subprocess.Popen(cmd,cwd=stage,stdout=stdout,stderr=stderr))
  print(backend+' livepids='+','.join(str(p.pid)for p in children),flush=True)
  for p in children:p.wait(timeout=max(1,120-(clock()-start)))
  for log in logs:log.flush()
  parties=[]
  for party,p in enumerate(children):
   assert p.returncode==0,(backend,party,p.returncode)
   text=(stage/f'party{party}.stdout').read_text();flags=[l for l in text.splitlines()if l.startswith('DIAGNOSTIC_COMPARE ')]
   assert flags==['DIAGNOSTIC_COMPARE 1']*5 if party==0 else flags in [[],['DIAGNOSTIC_COMPARE 1']*5],flags
   metrics=[json.loads(l[len('DIAGNOSTIC_TOTAL '):])for l in text.splitlines()if l.startswith('DIAGNOSTIC_TOTAL ')];assert len(metrics)==1
   parties.append(metrics[0])
  case.update(passed=True,parties=parties)
 except Exception as exc:case['failure_category']=type(exc).__name__;case['failure_public_detail']=str(exc)
 finally:
  for p in children:
   if p.poll()is None:
    try:p.kill()
    except Exception as exc:errors.append(type(exc).__name__)
  for p in children:
   try:p.wait(timeout=10)
   except Exception as exc:errors.append(type(exc).__name__)
  for log in logs:log.close()
  case.update(elapsed_seconds=clock()-start,exit_codes=[p.returncode for p in children],cleanup_errors=errors,integrity_verified=all(sha(p)==pins[str(p.relative_to(root))]for p in tracked))
  case['passed']=case['passed']and not errors and case['integrity_verified'];report['cases'][backend]=case
  (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 if not case['passed']:break
report['passed']=len(report['cases'])==2 and all(c['passed']for c in report['cases'].values())
text=json.dumps(report,indent=2)+'\n';(out/'report.json').write_text(text);(work/'compact-warm-native-report.json').write_text(text)
print(json.dumps({'passed':report['passed'],'raw':report['raw'],'cases':{k:{q:v[q]for q in ['passed','elapsed_seconds','exit_codes','cleanup_errors']}for k,v in report['cases'].items()}},indent=2),flush=True)
if not report['passed']:raise SystemExit(1)
