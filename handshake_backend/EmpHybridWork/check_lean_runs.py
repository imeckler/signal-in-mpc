"""Run pinned Lean circuits on the validated Boolean engine with private inputs.

For every profile written by a lowering script (`.deps/emp-hybrid-word-v1/*.json`)
and every fixture lane in it: the input is split into fresh random XOR shares,
one per party; the circuit runs with all inputs and outputs private; one bit is
opened saying whether the output equals the independently computed expectation.
A further run per profile supplies a wrong expectation and must be rejected at
the equality bit. Functional evidence on local loopback at statistical 128;
`secure_hybrid_backend` stays false.
"""
import hashlib,json,os,pathlib,re,subprocess,sys,tempfile,time
# Explicit mode: no argument = malicious statistical-128 engine; "semi-honest" =
# the honest-but-curious build (separate binary, separate report files).
SH=sys.argv[1:]==['semi-honest']
if sys.argv[1:] not in ([],['semi-honest']):raise SystemExit('usage: check_lean_runs.py [semi-honest]')
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';MP=BASE/'data61-MP-SPDZ-113c4e4';HERE=pathlib.Path(__file__).resolve().parent;WORDS=ROOT/'.deps/emp-hybrid-word-v1'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bits=lambda data:bytes((byte>>b)&1 for byte in data for b in range(8))
def run(name,spec,lane,port,corrupt=False):
    # One runtime-sized binary serves every profile.
    binary=BASE/('dyn-run-sh-fixture-v3' if SH else 'dyn-run-fixture-v3');work=pathlib.Path(tempfile.mkdtemp(prefix='lean-run-',dir=BASE))
    msb=spec.get('bit_order')=='msb';bits=(lambda data:bytes((byte>>(7-b))&1 for byte in data for b in range(8))) if msb else (lambda data:bytes((byte>>b)&1 for byte in data for b in range(8)))
    secret=bits(bytes.fromhex(lane['input']));share_a=bytes(b&1 for b in os.urandom(len(secret)));share_b=bytes(x^y for x,y in zip(secret,share_a))
    expected=bytearray(bits(bytes.fromhex(lane['output'])))
    if corrupt:expected[0]^=1
    (work/'1.share').write_bytes(share_a);(work/'2.share').write_bytes(share_b);(work/'expected.bits').write_bytes(bytes(expected))
    files=[];children=[];stats=[];failure=None;start=time.monotonic()
    try:
        for party in (1,2):
            log=open(work/f'{party}.log','w');files.append(log);env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP))
            children.append(subprocess.Popen([str(binary),str(party),str(port),str(WORDS/spec['circuit']),spec['circuit_sha256'],str(work/f'{party}.share'),str(work/'expected.bits'),str(WORDS/spec['equal']),spec['equal_sha256'],str(work/f'{party}.json')],cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT))
        deadline=start+600
        for c in children:
            while True:
                pid,status,u=os.wait4(c.pid,os.WNOHANG)
                if pid:c.returncode=os.waitstatus_to_exitcode(status);stats.append(dict(exit_code=c.returncode,cpu_seconds=u.ru_utime+u.ru_stime,peak_rss_bytes=u.ru_maxrss));break
                if time.monotonic()>deadline:raise TimeoutError('deadline')
                time.sleep(.05)
    except Exception as e:failure=type(e).__name__
    finally:
        for c in children:
            if c.returncode is None:
                if c.poll() is None:c.kill()
                c.wait()
        for f in files:f.close()
        for p in (1,2):(work/f'{p}.share').unlink(missing_ok=True)
    logs=[(work/f'{p}.log').read_text(errors='replace') for p in (1,2)]
    for p,s in zip((1,2),stats):
        m=work/f'{p}.json'
        if m.exists():s['metrics']=json.loads(m.read_text())
    ok=failure is None and len(stats)==2
    if corrupt:ok=ok and all(s['exit_code']!=0 for s in stats) and all('fixture passed' not in l for l in logs) and any('stage=equality' in l for l in logs)
    else:ok=ok and all(s['exit_code']==0 for s in stats) and all('dyn run fixture passed private_output_bits=%d opened_bits=1'%spec['output_bits'] in l for l in logs)
    return dict(passed=ok,profile=name,lane=lane['label'],wrong_expectation=corrupt,seconds=time.monotonic()-start,directory=str(work),failure_category=failure,parties=stats,os_buffer_exhausted=any('No buffer space available' in l for l in logs))
def attempt(*args,**kwargs):
    retries=[]
    for _ in range(4):
        result=run(*args,**kwargs)
        if result['passed'] or not result['os_buffer_exhausted']:break
        retries.append(result['directory']);time.sleep(8)
    result['os_buffer_retries']=retries;return result
if __name__=='__main__':
    results=[];port=38000 if SH else 36000
    for profile in sorted(WORDS.glob('*.json')):
        spec=json.loads(profile.read_text())
        if 'circuit_sha256' not in spec:continue
        if sha(WORDS/spec['circuit'])!=spec['circuit_sha256'] or sha(WORDS/spec['equal'])!=spec['equal_sha256']:raise ValueError('circuit pin drift '+profile.stem)
        for lane in spec['fixtures']:
            results.append(attempt(profile.stem,spec,lane,port));port+=20;time.sleep(1)
        results.append(attempt(profile.stem,spec,spec['fixtures'][0],port,corrupt=True));port+=20;time.sleep(1)
    ok=bool(results) and all(r['passed'] for r in results)
    build=json.loads((BASE/'hybrid-v3-build.json').read_text())
    key='dyn-run-sh' if SH else 'dyn-run';tag='-sh' if SH else ''
    report=dict(passed=ok,secure_hybrid_backend=False,security_mode='semi-honest' if SH else 'malicious-128',results=results,binaries={key:build[key]['binary_sha256']},emp_source=build['emp_source'],scope=('Pinned Lean circuits executed with plain half-gates garbling (honest-but-curious only, no protection against deviation)' if SH else 'Pinned Lean circuits executed on validated-v3 (Boolean statistical 128)')+' with XOR-shared private inputs and private outputs; one equality bit opened against an independent expectation; a wrong expectation is rejected. Local loopback fixture secrets only.')
    (HERE/f'lean-runs{tag}-report.json').write_text(json.dumps(report,indent=2)+'\n')
    summary={r['profile']+':'+r['lane']+(':wrong-expectation' if r['wrong_expectation'] else ''):(r['passed'],round(r['seconds'],1)) for r in results}
    (HERE/f'lean-runs{tag}-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(dict(passed=ok,cases=summary)))
    if not ok:raise SystemExit(1)
