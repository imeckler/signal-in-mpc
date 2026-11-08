"""CCD128 tiny conversion workload: bounded epochs, not application receipts."""
from pathlib import Path
import hashlib,json,os,re,signal,subprocess,time,secrets,shutil
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent;RUNTIME=ROOT/'.deps/tls-backend-diagnostic-runtime-v3/MP-SPDZ'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(policy,out):
 stage=out/policy;stage.mkdir();shutil.copytree(ROOT/'.deps/tls-backend-diagnostic-programs/Programs',stage/'Programs');shutil.copy2(ROOT/'.deps/tls-backend-diagnostic-programs/programs.manifest',stage/'programs.manifest');(stage/'libSPDZ.so').symlink_to(RUNTIME/'libSPDZ.so')
 with (out/f'{policy}-ssl.log').open('w')as log:subprocess.run(['bash',str(ROOT/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),'5'],cwd=stage,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
 hosts=stage/'hosts';hosts.write_text('127.0.0.1\n'*5);binary=RUNTIME.parent/'tls-ccd-epoch-policy-fixture'
 tracked=[WORK/'ccd_epoch_policy_fixture.cpp',WORK/'PublicProtocolMetrics.h',WORK/'diagnostics-v3.patch',binary,RUNTIME/'libSPDZ.so',stage/'programs.manifest'];hashes={str(p.relative_to(ROOT)):sha(p)for p in tracked}
 ps=[];logs=[];errors=[];start=time.monotonic();result={'passed':False,'source_product_sha256':hashes}
 try:
  for party in range(5):
   log=(out/f'{policy}-party-{party}.log').open('w');logs.append(log)
   ps.append(subprocess.Popen([str(binary),str(party),str(hosts),str(27300 if policy=='record'else 28300),str(stage/'programs.manifest'),policy],cwd=stage,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True))
  parties=[]
  for party,p in enumerate(ps):
   stdout,_=p.communicate(timeout=max(1,120-(time.monotonic()-start)));(out/f'{policy}-party-{party}.stdout').write_text(stdout);assert p.returncode==0,(party,p.returncode)
   rows=[json.loads(l[11:])for l in stdout.splitlines()if l.startswith('DIAGNOSTIC ')];assert len(rows)==3 and 'diagnostic CCD epoch-policy fixture passed'in stdout
   assert all(sum(v['bytes'])==v['original_payload_byte_delta']+v['initialization_reset_bytes']for v in rows)
   parties.append(rows)
  result.update(passed=True,parties=parties)
 except Exception as error:result['error']=repr(error)
 finally:
  for p in ps:
   if p.poll()is None:
    try:os.killpg(p.pid,signal.SIGKILL)
    except PermissionError:
     try:p.kill()
     except Exception as error:errors.append(repr(error))
    except ProcessLookupError:pass
  for p in ps:
   try:p.wait(timeout=10)
   except Exception as error:errors.append(repr(error))
  for log in logs:log.close()
  leftovers=[]
  for party in range(5):
   marker=None
   for line in (out/f'{policy}-party-{party}.log').read_text().splitlines():
    if line.startswith('DIAGNOSTIC_EPOCH '):marker=line
    found=re.fullmatch(r'\s*(\d+) (triples|bits|dabits|squares|inverses) of (.+) left',line)
    if found:leftovers.append({'party':party,'cleanup_stage':marker,'count':int(found[1]),'kind':found[2],'type':found[3]})
  result.update(elapsed_python_awake_seconds=time.monotonic()-start,exit_codes=[p.returncode for p in ps],cleanup_errors=errors,integrity_verified=all(sha(p)==hashes[str(p.relative_to(ROOT))]for p in tracked),unused_buffer_rows_at_destruction=leftovers);result['passed']=result['passed']and not errors and result['integrity_verified']
 return result
if __name__=='__main__':
 out=ROOT/'benchmarks/results/raw/ccd-epoch-policy'/secrets.token_hex(8);out.mkdir(parents=True);print(out,flush=True)
 report={'scope':'same3-call CCD128 conversion/state fixture; record=renew eachcall; epoch=retain preprocessing/VM history until final3-call boundary; no intermediate retirement acknowledgement/application capability or throughput claim','generated_raw_preprocessing_count_available':False,'unused_counts_scope':'actual BufferPrep destructor rows, accepted buffer leftovers; not raw pre-sacrifice generation','cases':{}}
 for policy in ['record','epoch']:
  report['cases'][policy]=run(policy,out)
  if not report['cases'][policy]['passed']:break
 report['passed']=len(report['cases'])==2 and all(v['passed']for v in report['cases'].values());text=json.dumps(report,indent=2)+'\n';(out/'report.json').write_text(text);(WORK/'epoch-policy-native-report.json').write_text(text);print(json.dumps({'passed':report['passed'],'cases':{k:{p:v[p]for p in ['passed','elapsed_python_awake_seconds','exit_codes']}for k,v in report['cases'].items()}},indent=2),flush=True)
 if not report['passed']:raise SystemExit(1)
