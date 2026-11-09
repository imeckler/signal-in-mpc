#!/usr/bin/env python3
"""Conservative observed-closure-set replay, NOT a chronological call trace."""
from pathlib import Path
import argparse,json,hashlib,subprocess,secrets,time
root=Path(__file__).resolve().parents[2];work=Path(__file__).parent
parser=argparse.ArgumentParser();parser.add_argument('--mode',choices=['sequential','batch'],default='sequential');args=parser.parse_args()
mode=args.mode;frozen_path=root/f'benchmarks/results/tls-native-text-throughput-{mode}.json';frozen=json.loads(frozen_path.read_text())
run=root/frozen['logs'];working=run/'working';manifest=run/'programs.manifest';log=run/'party-0.log'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(manifest)==frozen['source_and_product_sha256'][str(manifest.relative_to(root))]
pins={l[65:]:l[:64]for l in manifest.read_text().splitlines()[1:]}
# Runtime-generated public shape extensions are retained with receipts bound
# to the boot-pinned public toolchain. They were not entries in the boot map.
extension_evidence=[]
toolchain='Worker-Public/tls-shape-toolchain.json'
assert sha(working/toolchain)==pins[toolchain]
receipts={}
for receipt in (working/'Worker-Public').glob('*.receipt.json'):
 value=json.loads(receipt.read_text())
 if value.get('toolchain')==pins[toolchain] and isinstance(value.get('manifest'),str):receipts[value['manifest']]=receipt
for extension in (working/'Worker-Public').glob('*.manifest'):
 digest=sha(extension)
 if digest not in receipts:continue
 extension_evidence +=[extension,receipts[digest]]
 for line in extension.read_text().splitlines()[1:]:
  expected,path=line.split(' ',1)
  assert path not in pins or pins[path]==expected
  pins[path]=expected
observed={}
for line in log.read_text().splitlines():
 if line.startswith('TLS_RESOURCE_META '):
  row=json.loads(line.split(' ',1)[1]);observed[row['descriptor']]=max(observed.get(row['descriptor'],0),row['calls'])
observed={k:v for k,v in observed.items()if v>0}
closures=[];tracked=extension_evidence+[Path(__file__),work/'working_set_probe.cpp',work/'PublicCodeCache.h',work/'PinnedPublicCode.h',frozen_path,manifest,log]
for descriptor,calls in sorted(observed.items()):
 function=working/descriptor;assert sha(function)==pins[descriptor]
 program=function.read_text().split()[0];schedule_rel=f'Programs/Schedules/{program}.sch';schedule=working/schedule_rel
 assert sha(schedule)==pins[schedule_rel];tokens=schedule.read_text().split();tapes=[]
 for token in tokens[2:2+int(tokens[1])]:
  path=working/'Programs/Bytecode'/(token.rsplit(':',1)[0]+'.bc');assert sha(path)==pins[str(path.relative_to(working))];tapes.append(path)
 allpaths=[function,schedule,*tapes];tracked+=allpaths
 name=descriptor.split('/')[-1];producer=name.startswith('signal_private_variable_conversation_')or name.startswith('signal_private_variable_batch_')
 identity=hashlib.sha256(('\n'.join(pins[str(p.relative_to(working))]+' '+str(p.relative_to(working))for p in sorted(allpaths))).encode()).hexdigest()
 closures.append({'descriptor':descriptor,'observed_calls':calls,'producer':producer,'identity':identity,'function':function,'schedule':schedule,'tapes':tapes})
assert sum(c['producer']for c in closures)==1
runtime=root/'.deps/tls-public-program-cache-runtime-v2/MP-SPDZ';binary=runtime.parent/'tls-public-working-set-probe';tracked +=[binary,runtime/'libSPDZ.so',runtime/'Processor/Program.cpp',runtime/'Processor/Program.h',runtime/'Tools/PublicCodeCache.h']
hashes={str(p.relative_to(root)):sha(p)for p in tracked}
out=root/'benchmarks/results/raw/public-working-set-replay'/secrets.token_hex(8);out.mkdir(parents=True)
trace=out/'observed-set.tsv';lines=[str(len(closures))]
for c in closures:
 values=[str(int(c['producer'])),c['identity'],str(c['function']),str(c['schedule']),str(len(c['tapes'])),pins[str(c['function'].relative_to(working))],pins[str(c['schedule'].relative_to(working))]]
 for path in c['tapes']:values +=[pins[str(path.relative_to(working))],str(path)]
 assert all(' 'not in x for x in values);lines.append(' '.join(values))
trace.write_text('\n'.join(lines)+'\n');print(out,flush=True)
clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW);start=clock()
with(out/'probe.log').open('w')as output:
 child=subprocess.Popen([str(binary),str(trace)],cwd=runtime,stdout=output,stderr=subprocess.STDOUT);print('public working-set pid='+str(child.pid),flush=True)
 try:code=child.wait(timeout=600)
 except BaseException:child.kill();child.wait();raise
text=(out/'probe.log').read_text();print(text[-2200:],flush=True)
metrics=[json.loads(l.split(' ',1)[1])for l in text.splitlines()if l.startswith('SET_METRIC ')];results=[json.loads(l.split(' ',1)[1])for l in text.splitlines()if l.startswith('SET_RESULT ')]
report={'passed':code==0 and len(results)==1 and results[0]['producer_parse_count']==1,'mode':mode,'scope':'public-only conservative observed descriptor-set stress from frozen8text run, allotherobservedclosures betweenproduceruses; exact chronological descriptor order was not logged; no private execution/application throughput claim','observed_distinct_descriptors':len(closures),'observed_total_calls':sum(observed.values()),'dynamic_extension_binding':'retained public receipts+manifests bound to boot-pinned toolchain; historical per-call extension digests were not logged','producer_reservation_bytes':2*1024**3,'small_cache_budget_bytes':256*1024**2,'source_product_sha256':hashes,'trace_sha256':sha(trace),'closures':[{k:c[k]for k in ['descriptor','observed_calls','producer','identity']}for c in closures],'metrics':metrics,'result':results,'raw':str(out.relative_to(root)),'elapsed_seconds':clock()-start,'pid':child.pid,'exit_code':code,'integrity_verified':all(sha(p)==hashes[str(p.relative_to(root))]for p in tracked)}
report['passed']=report['passed']and report['integrity_verified'];encoded=json.dumps(report,indent=2)+'\n';(out/'report.json').write_text(encoded);(work/f'working-set-{mode}-report.json').write_text(encoded)
if not report['passed']:raise SystemExit(1)
