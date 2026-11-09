"""Execute prepared fused core once; compare only private padded fixture result."""
import hashlib
import json
import os
import pathlib
import subprocess
import time

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'

if __name__=='__main__':
    work=BASE/'signal-core-2'
    prepared=json.loads((work/'prepare-report.json').read_text())
    digest=hashlib.sha256((work/'circuit.txt').read_bytes()).hexdigest()
    if digest!=prepared['bristol_sha256']:raise ValueError('prepared circuit drift')
    children=[];streams=[];start=time.monotonic();failure=None
    env=dict(os.environ,DYLD_LIBRARY_PATH=str(BASE/'install/lib'))
    try:
        for party,who in ((1,'alice'),(2,'bob')):
            stream=open(work/(who+'.log'),'w');streams.append(stream)
            children.append(subprocess.Popen([str(BASE/'emp-worker'),str(party),'31420',str(work/'circuit.txt'),
                str(work/(who+'.bin')),str(work/(who+'.output')),str(work/(who+'.json'))],
                env=env,stdout=stream,stderr=subprocess.STDOUT))
        deadline=start+120
        for child in children:child.wait(timeout=max(1,deadline-time.monotonic()))
    except Exception as exc:
        failure=type(exc).__name__
    finally:
        for child in children:
            if child.poll() is None:child.kill()
            child.wait()
        for stream in streams:stream.close()
    codes=[c.returncode for c in children]
    passed=(failure is None and codes==[0,0] and (work/'bob.output').exists()
            and (work/'bob.output').read_bytes()==(work/'expected-padded.bin').read_bytes())
    metrics=[json.loads((work/(who+'.json')).read_text()) if (work/(who+'.json')).exists() else None for who in ('alice','bob')]
    if passed:
        passed=metrics[0]['sent_bytes']==metrics[1]['received_bytes'] and metrics[1]['sent_bytes']==metrics[0]['received_bytes']
    report={'passed':passed,'scope':'two fused zero-plaintext Signal core sends; no curve/sealed sender/TLS/response claim',
            'retained_state':'first returned selected chain/counter feeds second graph internally; no host share handoff',
            'security':'legacy EMP with40-bit comparison-mask/failclosed overlay; full composition unvalidated',
            'controller_wall_seconds':time.monotonic()-start,'exit_codes':codes,'failure_category':failure,
            'prepared':prepared,'parties':metrics,
            'worker_sha256':hashlib.sha256((BASE/'emp-worker').read_bytes()).hexdigest(),
            'controller_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
    target=ROOT/'benchmarks/TwoPartyComparisonWork/emp-signal-core-report.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':passed,'report':str(target),'wall_seconds':report['controller_wall_seconds']}))
    if not passed:raise SystemExit(1)
