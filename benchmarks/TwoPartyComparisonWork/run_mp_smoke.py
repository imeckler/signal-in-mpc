"""Same-graph Tinier and MASCOT/Tinier component checks, live preprocessing.

All revealed outputs in this entry are padded public-known fixture results.
This does not implement persistent private-output handoff or a Signal send.
"""
import hashlib
import json
import os
import pathlib
import re
import subprocess
import tempfile
import time

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
MP=BASE/'data61-MP-SPDZ-113c4e4'

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def compile_case(case,index):
    name=f'two_party_smoke_{index}'
    source=ROOT/'benchmarks/TwoPartyComparisonWork/boolean_graph.mpc'
    (MP/f'Programs/Source/{name}.mpc').write_bytes(source.read_bytes())
    env=dict(os.environ,TWO_PARTY_BRISTOL=str(pathlib.Path(case['directory'])/'circuit.txt'))
    with open(BASE/(name+'-compile.log'),'w') as f:
        subprocess.run(['python3','compile.py','-B','64',name],cwd=MP,env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=120)
    return name

def run_case(case,name,backend,port):
    work=pathlib.Path(tempfile.mkdtemp(prefix=backend+'-',dir=BASE))
    fixture=pathlib.Path(case['directory'])
    # Fresh key/OT directory per independent cold execution. Never roll back a
    # cached OT root or reuse consumed preprocessing between benchmark cases.
    (work/'Player-Data').mkdir()
    (work/'Programs').symlink_to(MP/'Programs',target_is_directory=True)
    for p,who in [(0,'bob'),(1,'alice')]:
        (work/f'Input-P{p}-0').write_text(' '.join(str(x) for x in (fixture/(who+'.bin')).read_bytes())+'\n')
    env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP))
    children=[];files=[];stats=[];start=time.monotonic()
    try:
        for party in (0,1):
            log=open(work/f'party-{party}.log','w');files.append(log)
            command=[str(MP/f'{backend}-party.x'),'-N','2','-p',str(party),'-pn',str(port),'-S','40','-b','10000','-v','-IF',str(work/'Input')]
            if backend=='mascot':command+=['-P',str(2**255-19)]
            command.append(name)
            children.append(subprocess.Popen(command,cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT))
        deadline=start+120
        for child in children:
            while True:
                pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                if pid:
                    child.returncode=os.waitstatus_to_exitcode(status)
                    stats.append({'exit_code':child.returncode,'cpu_seconds':usage.ru_utime+usage.ru_stime,
                                  'peak_rss_bytes':usage.ru_maxrss})
                    break
                if time.monotonic()>deadline:raise TimeoutError('bounded component deadline')
                time.sleep(.02)
    finally:
        for child in children:
            if child.returncode is None:
                if child.poll() is None:child.kill()
                child.wait()
        for f in files:f.close()
    logs=[(work/f'party-{p}.log').read_text() for p in (0,1)]
    expected=(fixture/'bob.output').read_bytes()
    chunks=[sum(x<<j for j,x in enumerate(expected[i:i+32])) for i in range(0,len(expected),32)]
    actual=[int(x)&0xffffffff for x in re.findall(r'FIXTURE_CHUNK (-?\d+)',logs[0])]
    for stat,log in zip(stats,logs):
        counts=re.findall(r'EXACT_SOCKET_BYTES sent=(\d+) received=(\d+)',log)
        if len(counts)!=1:raise RuntimeError('missing/duplicate exact socket counters')
        stat['socket_sent_bytes'],stat['socket_received_bytes']=map(int,counts[0])
        # Preserve original phase/resource text: printed MB is rounded; phase
        # CPU values overlap and must not be added. Exact overall CPU is wait4.
        stat['phase_report']=next((line for line in log.splitlines() if line.startswith('Spent ')),None)
        stat['leftover_report']=[line.strip() for line in log.splitlines() if ' left' in line]
    passed=all(s['exit_code']==0 for s in stats) and actual==chunks
    # Startup coordination opens an additional local socket. Exact socket counts
    # include both protocol and startup traffic; compare global send/receive.
    passed=passed and sum(s['socket_sent_bytes'] for s in stats)==sum(s['socket_received_bytes'] for s in stats)
    result={'passed':passed,'backend':backend,'name':case['name'],'and_gates':case['and_gates'],
            'controller_wall_seconds':time.monotonic()-start,'parties':stats,'directory':str(work),
            'bristol_sha256':case['bristol_sha256'],'logical_input_bits':case['logical_input_bits'],
            'worker_sha256':sha(MP/f'{backend}-party.x'),'runtime_sha256':sha(MP/'libSPDZ.so')}
    if not passed:raise RuntimeError(json.dumps(result))
    return result

if __name__=='__main__':
    cases=json.loads((ROOT/'benchmarks/TwoPartyComparisonWork/emp-smoke-report.json').read_text())['results'][:2]
    results=[]
    for index,case in enumerate(cases):
        name=compile_case(case,index)
        for backend in ('tinier','mascot'):
            results.append(run_case(case,name,backend,31340+20*index+(backend=='mascot')*10))
    report={'passed':all(r['passed'] for r in results),'scope':'same-graph loopback component smoke, not full Signal/TLS throughput',
            'security':{'parties':2,'corruptions':1,'statistical_parameter':40,'computational_target':128,
                        'ot':'checked SoftSpoken; no KOS/insecure fallback','mascot_prime':str(2**255-19),
                        'preprocessing_batch_size_option':10000,'fresh_key_ot_directory_per_case':True,
                        'full_parameter_composition_validated':False},
            'compiler_source_sha256':sha(ROOT/'benchmarks/TwoPartyComparisonWork/boolean_graph.mpc'),
            'instrumentation':json.loads((ROOT/'benchmarks/TwoPartyComparisonWork/mp-instrumentation.json').read_text()),
            'results':results}
    target=ROOT/'benchmarks/TwoPartyComparisonWork/mp-smoke-report.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':report['passed'],'cases':len(results),'report':str(target)}))
