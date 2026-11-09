"""Functional current-EMP gate replay/private-output/checkpoint controls."""
import hashlib
import json
import os
import pathlib
import subprocess
import tempfile
import time

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
WORKER=BASE/'build-modern-worker/modern-worker'

def run(case,port,corrupt=False):
    fixture=pathlib.Path(case['directory']);work=pathlib.Path(tempfile.mkdtemp(prefix='modern-smoke-',dir=BASE))
    children=[];files=[];start=time.monotonic();failure=None
    try:
        for party,who in ((1,'alice'),(2,'bob')):
            stream=open(work/(who+'.log'),'w');files.append(stream)
            env=dict(os.environ)
            if corrupt and party==2:env['EMP_MODERN_TEST_CORRUPT_DELTA']='1'
            children.append(subprocess.Popen([str(WORKER),str(party),str(port),str(fixture/'circuit.txt'),
                str(fixture/(who+'.bin')),str(work/(who+'.output')),str(work/(who+'.json'))],
                env=env,stdout=stream,stderr=subprocess.STDOUT))
        deadline=start+30
        for child in children:child.wait(timeout=max(1,deadline-time.monotonic()))
    except Exception as exc:failure=type(exc).__name__
    finally:
        for child in children:
            if child.poll() is None:child.kill()
            child.wait()
        for stream in files:stream.close()
    codes=[c.returncode for c in children]
    metrics=[json.loads((work/(who+'.json')).read_text()) if (work/(who+'.json')).exists() else None for who in ('alice','bob')]
    if corrupt:
        logs=[(work/(who+'.log')).read_text() for who in ('alice','bob')]
        passed=(failure is None and all(c!=0 for c in codes) and not (work/'bob.output').exists()
                and any('lambda c_gamma check failed' in log or 'peer share-MAC hash mismatch' in log for log in logs))
    else:
        passed=(failure is None and codes==[0,0] and (work/'bob.output').read_bytes()==(fixture/'bob.output').read_bytes()
                and not (work/'alice.output').exists())
        if passed:passed=metrics[0]['sent_bytes']==metrics[1]['received_bytes'] and metrics[1]['sent_bytes']==metrics[0]['received_bytes']
    return {'passed':passed,'name':case['name'],'corrupt_delta_control':corrupt,'failure_category':failure,
            'exit_codes':codes,'controller_wall_seconds':time.monotonic()-start,'directory':str(work),
            'bristol_sha256':case['bristol_sha256'],'parties':metrics}

if __name__=='__main__':
    cases=json.loads((ROOT/'benchmarks/TwoPartyComparisonWork/emp-smoke-report.json').read_text())['results'][:2]
    results=[run(cases[0],31500),run(cases[1],31510),run(cases[0],31520,True)]
    report={'passed':all(r['passed'] for r in results),'unaudited_rewrite':True,
            'scope':'current EMP imported AES/SHA gates, authenticated checkpoint and Bob-only output; no curve/full Signal claim',
            'security':'declared S40; tiny nonzero chunks below1024 rejected; full implementation/theorem composition unvalidated',
            'build':json.loads((BASE/'modern-build.json').read_text()),'results':results}
    target=ROOT/'benchmarks/TwoPartyComparisonWork/modern-smoke-report.json';target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':report['passed'],'report':str(target)}))
    if not report['passed']:raise SystemExit(1)
