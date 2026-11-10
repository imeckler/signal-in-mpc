"""Bounded semantic and real checked-triple controls; no curve conversion claim."""
import hashlib,json,os,pathlib,subprocess,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
BIN=BASE/'build-modern-worker/emp-padded-kernel'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(port,bad):
    work=pathlib.Path(tempfile.mkdtemp(prefix='padded-kernel-',dir=BASE));children=[];logs=[];failure=None
    try:
        for party in (1,2):
            f=open(work/f'{party}.log','wb');logs.append(f);env=dict(os.environ)
            if party==2 and bad:env['EMP_TEST_CORRUPT_PADDED_DELTA']='1'
            children.append(subprocess.Popen([str(BIN),str(party),str(port)],env=env,stdout=f,stderr=subprocess.STDOUT))
        deadline=time.monotonic()+30
        for c in children:c.wait(timeout=max(1,deadline-time.monotonic()))
    except Exception as e:failure=type(e).__name__
    finally:
        for c in children:
            if c.poll() is None:c.kill()
            c.wait()
        for f in logs:f.close()
    codes=[c.returncode for c in children];text=[(work/f'{p}.log').read_text() for p in (1,2)]
    passed=failure is None and (all(c!=0 for c in codes) and any('lambda c_gamma check failed' in t for t in text) and all('fixture passed' not in t for t in text) if bad else codes==[0,0] and all('real_ands=1 checked_ands=1024 dummy_outputs_opened=0' in t for t in text))
    return dict(passed=passed,corrupt_delta=bad,exit_codes=codes,failure_category=failure,directory=str(work))
if __name__=='__main__':
    test=BASE/'pad-program-test'
    subprocess.run(['c++','-std=c++20','-O2','-I'+str(BASE/'modern-install/include'),str(HERE/'pad_program_test.cpp'),'-o',str(test)],check=True)
    semantic=json.loads(subprocess.check_output([str(test)]));results=[run(31550,False),run(31560,True)]
    report=dict(passed=semantic['passed'] and all(r['passed'] for r in results),semantic=semantic,results=results,security='Unaudited current EMP, configured S40. Actual checked 1024-AND kernel, no parameter bypass. Backend/theorem composition remains unvalidated.',scope='Original-output equivalence tested at0/1/2/15/1023/1024/1025 ANDs with constants, inversions, duplicate/input outputs; real one-AND native kernel pads with1023 independent secret ANDs, keeps dummy outputs through checking, prunes without opening.',pins={p.name:sha(p) for p in [HERE/'pad_program.h',HERE/'padded_kernel_fixture.cpp',BIN]},build=json.loads((BASE/'modern-build.json').read_text()))
    target=HERE/'padding-report.json';target.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=report['passed'],report=str(target))))
    if not report['passed']:raise SystemExit(1)
