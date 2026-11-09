"""Exercise stock authenticated-MAC corruption hook; never enable debug_mac.

Only party1 gets '-o mac_fail', perturbing its first opened check value in
MAC_Check.hpp. This tests detection before fixture output, not lifecycle erasure
or arbitrary network corruption. Existing canonical runtime remains untouched.
"""
import hashlib
import json
import os
import pathlib
import subprocess
import tempfile
import time

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
MP=BASE/'data61-MP-SPDZ-113c4e4'

def check(backend,port):
    case=json.loads((ROOT/'benchmarks/TwoPartyComparisonWork/emp-smoke-report.json').read_text())['results'][0]
    fixture=pathlib.Path(case['directory']);work=pathlib.Path(tempfile.mkdtemp(prefix='reject-'+backend+'-',dir=BASE))
    (work/'Player-Data').mkdir();(work/'Programs').symlink_to(MP/'Programs',target_is_directory=True)
    for p,who in ((0,'bob'),(1,'alice')):(work/f'Input-P{p}-0').write_text(' '.join(str(x) for x in (fixture/(who+'.bin')).read_bytes())+'\n')
    children=[];files=[];start=time.monotonic();failure=None
    try:
        for p in (0,1):
            log=open(work/f'party-{p}.log','w');files.append(log)
            command=[str(MP/f'{backend}-party.x'),'-N','2','-p',str(p),'-pn',str(port),'-S','40','-b','10000','-IF',str(work/'Input')]
            if backend=='mascot':command+=['-P',str(2**255-19)]
            if p==1:command+=['-o','mac_fail']
            command+=['two_party_smoke_0']
            children.append(subprocess.Popen(command,cwd=work,env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP)),stdout=log,stderr=subprocess.STDOUT))
        deadline=start+30
        for child in children:child.wait(timeout=max(1,deadline-time.monotonic()))
    except Exception as exc:failure=type(exc).__name__
    finally:
        for child in children:
            if child.poll() is None:child.kill()
            child.wait()
        for log in files:log.close()
    logs=[(work/f'party-{p}.log').read_text() for p in (0,1)]
    codes=[c.returncode for c in children]
    passed=(failure is None and len(codes)==2 and all(c!=0 for c in codes)
            and all('FIXTURE_CHUNK' not in log for log in logs)
            and all('because of MAC check failure' in log for log in logs))
    return {'passed':passed,'backend':backend,'exit_codes':codes,'wall_seconds':time.monotonic()-start,
            'failure_category':failure,'no_fixture_output':all('FIXTURE_CHUNK' not in log for log in logs),
            'directory':str(work)}

if __name__=='__main__':
    cases=[check('tinier',31470),check('mascot',31480)]
    report={'passed':all(c['passed'] for c in cases),'scope':'stock per-party opened-check-value corruption rejected; not tamper completeness or erasure',
            'debug_mac_enabled':False,'corrupt_party':1,
            'mac_checker_sha256':hashlib.sha256((MP/'Protocols/MAC_Check.hpp').read_bytes()).hexdigest(),
            'runtime_sha256':hashlib.sha256((MP/'libSPDZ.so').read_bytes()).hexdigest(),'cases':cases}
    target=ROOT/'benchmarks/TwoPartyComparisonWork/mp-rejection-report.json';target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':report['passed'],'report':str(target)}))
    if not report['passed']:raise SystemExit(1)
