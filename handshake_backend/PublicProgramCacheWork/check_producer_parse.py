#!/usr/bin/env python3
"""Public-only reuse of actual immutable producer bytecode; no MPC execution."""
from pathlib import Path
import subprocess,json,hashlib,time,secrets,os
root=Path(__file__).resolve().parents[2];work=Path(__file__).parent
runtime=root/'.deps/tls-public-program-cache-runtime/MP-SPDZ';binary=runtime.parent/'tls-public-producer-parse-probe'
producer=root/'.deps/private-variable-conversation-native/260-80-0-0/sha-gate-efficient'
large=max((producer/'Programs/Bytecode').glob('*.bc'),key=lambda p:p.stat().st_size)
small=next((root/'.deps/throughput-public-cache-fixture-v1/Programs/Bytecode').glob('*tiny-sequential-8*-1.bc'),None)
if small is None:small=min((root/'.deps/throughput-public-cache-fixture-v1/Programs/Bytecode').glob('*.bc'),key=lambda p:p.stat().st_size)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={line[65:]:line[:64]for line in(producer/'service.manifest').read_text().splitlines()[1:]}
large_sha=pins[str(large.relative_to(producer))];assert sha(large)==large_sha
small_sha=sha(small)
tracked=[Path(__file__),work/'producer_parse_probe.cpp',work/'PublicCodeCache.h',work/'PinnedPublicCode.h',binary,runtime/'libSPDZ.so',runtime/'Processor/Program.cpp',runtime/'Processor/Program.h',large,small,producer/'service.manifest']
hashes={str(p.relative_to(root)):sha(p)for p in tracked}
out=root/'benchmarks/results/raw/public-producer-parse'/secrets.token_hex(8);out.mkdir(parents=True)
clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW);start=clock()
print(out,flush=True)
with(out/'probe.log').open('w')as log:
 child=subprocess.Popen([str(binary),str(large),large_sha,str(small),small_sha],cwd=runtime,stdout=log,stderr=subprocess.STDOUT)
 print('public parser pid='+str(child.pid),flush=True)
 try:code=child.wait(timeout=300)
 except BaseException:
  child.kill();child.wait();raise
text=(out/'probe.log').read_text();print(text[-1800:],flush=True)
rows=[json.loads(line.split(' ',1)[1])for line in text.splitlines()if line.startswith('PARSE_METRIC ')]
result=[json.loads(line.split(' ',1)[1])for line in text.splitlines()if line.startswith('PARSE_RESULT ')]
report={'passed':code==0 and len(rows)==3 and len(result)==1,'scope':'actual265MBproducer parsed once, interleaved with small publicProgram, then same parsed image reused; no private execution, parties, crypto or application throughput claim','source_product_sha256':hashes,'large_bytecode_bytes':large.stat().st_size,'metrics':rows,'result':result,'elapsed_seconds':clock()-start,'pid':child.pid,'exit_code':code,'raw':str(out.relative_to(root)),'integrity_verified':all(sha(p)==hashes[str(p.relative_to(root))]for p in tracked)}
report['passed']=report['passed']and report['integrity_verified'];encoded=json.dumps(report,indent=2)+'\n';(out/'report.json').write_text(encoded);(work/'producer-parse-report.json').write_text(encoded)
if not report['passed']:raise SystemExit(1)
