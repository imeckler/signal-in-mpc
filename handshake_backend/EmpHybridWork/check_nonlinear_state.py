"""Public-known fixture controller; parties receive only shares and private pads."""
import hashlib,json,os,pathlib,subprocess,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
BIN=BASE/'build-modern-worker/emp-nonlinear-state'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def bits(b):return bytes((x>>i)&1 for x in b for i in range(7,-1,-1))
def run(case,port,bad=False):
    fixture=pathlib.Path(case['directory']);work=pathlib.Path(tempfile.mkdtemp(prefix='nonlinear-state-',dir=BASE))
    pad=bits(os.urandom(16));(work/'fresh-pad').write_bytes(pad)
    key=bytes(range(32));plain=bytes(range(16))
    for _ in range(2):
        plain=subprocess.run(['/opt/homebrew/opt/openssl@3.5/bin/openssl','enc','-aes-256-ecb','-K',key.hex(),'-nopad'],input=plain,capture_output=True,check=True).stdout
    expected=bytes(a^b for a,b in zip(bits(plain),pad))
    children=[];logs=[];failure=None;start=time.monotonic()
    try:
        for party,who in ((1,'alice'),(2,'bob')):
            log=open(work/(who+'.log'),'wb');logs.append(log);env=dict(os.environ)
            if bad and party==2:env['EMP_TEST_CORRUPT_RETAINED_DELTA']='1'
            children.append(subprocess.Popen([str(BIN),str(party),str(port),str(fixture/'circuit.txt'),str(fixture/(who+'.bin')),str(work/'fresh-pad'),str(work/(who+'.output')),str(work/(who+'.json'))],env=env,stdout=log,stderr=subprocess.STDOUT))
        deadline=start+30
        for child in children:child.wait(timeout=max(1,deadline-time.monotonic()))
    except Exception as e:failure=type(e).__name__
    finally:
        for child in children:
            if child.poll() is None:child.kill()
            child.wait()
        for log in logs:log.close()
    codes=[c.returncode for c in children]
    metrics=[json.loads((work/(w+'.json')).read_text()) if (work/(w+'.json')).exists() else None for w in ('alice','bob')]
    if bad:
        passed=failure is None and len(codes)==2 and all(c!=0 for c in codes) and not (work/'bob.output').exists() and any('lambda c_gamma check failed' in (work/(w+'.log')).read_text() for w in ('alice','bob'))
    else:
        passed=failure is None and codes==[0,0] and (work/'bob.output').read_bytes()==expected and not (work/'alice.output').exists()
        if passed:passed=metrics[0]['sent_bytes']==metrics[1]['received_bytes'] and metrics[1]['sent_bytes']==metrics[0]['received_bytes']
    return dict(passed=passed,corrupt_retained_delta=bad,exit_codes=codes,failure_category=failure,directory=str(work),controller_seconds=time.monotonic()-start,parties=metrics,circuit_sha256=sha(fixture/'circuit.txt'))
if __name__=='__main__':
    case=json.loads((ROOT/'benchmarks/TwoPartyComparisonWork/emp-smoke-report.json').read_text())['results'][0]
    results=[run(case,31530),run(case,31540,True)]
    report=dict(passed=all(r['passed'] for r in results),scope='Two nonlinear imported AES calls in one authenticated EMP session. Private first result and key carried through checkpoints; only final padded result revealed to Bob. Not field conversion, Signal or erasure evidence.',security='Current unaudited EMP rewrite; declared S40; implementation/theorem composition unvalidated.',source_sha256=sha(pathlib.Path(__file__).with_name('nonlinear_state_fixture.cpp')),binary_sha256=sha(BIN),build=json.loads((BASE/'modern-build.json').read_text()),results=results)
    target=pathlib.Path(__file__).with_name('nonlinear-state-report.json');target.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=report['passed'],report=str(target))))
    if not report['passed']:raise SystemExit(1)
