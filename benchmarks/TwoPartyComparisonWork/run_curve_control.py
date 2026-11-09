"""Bounded actual MASCOT/Tinier curve/conversion control; no EMP claim."""
import hashlib
import json
import os
import pathlib
import random
import re
import shutil
import subprocess
import tempfile
import time
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
MP=BASE/'data61-MP-SPDZ-113c4e4'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def compile_control(expected):
    frozen=BASE/'curve-module-snapshot/handshake_backend'
    frozen.mkdir(parents=True,exist_ok=True)
    for name in ('__init__.py','field_dag.py','mixed.py'):
        path=frozen/name;current=(ROOT/'handshake_backend'/name).read_bytes()
        if path.exists() and path.read_bytes()!=current:raise ValueError('mixed adapter source snapshot drift')
        path.write_bytes(current)
    link=MP/'handshake_backend'
    if not link.exists():link.symlink_to(frozen,target_is_directory=True)
    elif link.resolve()!=frozen:raise ValueError('compiler module binding mismatch')
    field=BASE/'x25519-field.json'
    source=ROOT/'.deps/relay-service-artifacts/x25519-field.json'
    if field.exists() and field.read_bytes()!=source.read_bytes():raise ValueError('field artifact drift')
    field.write_bytes(source.read_bytes())
    shutil.copyfile(ROOT/'benchmarks/TwoPartyComparisonWork/curve_control.mpc',MP/'Programs/Source/two_party_curve.mpc')
    env=dict(os.environ,TWO_PARTY_FIELD_DAG=str(field),TWO_PARTY_CURVE_EXPECTED=expected.hex())
    with open(BASE/'mp-curve-compile.log','w') as log:
        subprocess.run(['python3','compile.py','-M','-X','-P',str(2**255-19),'two_party_curve'],cwd=MP,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=180,check=True)

def execute_control(scalar,point,port,reject=False):
    work=pathlib.Path(tempfile.mkdtemp(prefix='mascot-curve-',dir=BASE))
    (work/'Player-Data').mkdir();(work/'Programs').symlink_to(MP/'Programs',target_is_directory=True)
    bits=[(x>>i)&1 for x in scalar+point for i in range(7,-1,-1)]
    rng=random.Random(28419);left=[rng.getrandbits(1) for _ in bits]
    shares=[left,[a^b for a,b in zip(bits,left)]]
    for p in (0,1):(work/f'Input-P{p}-0').write_text(' '.join(map(str,shares[p]))+'\n')
    children=[];files=[];stats=[];start=time.monotonic()
    try:
        for p in (0,1):
            log=open(work/f'party-{p}.log','w');files.append(log)
            command=[str(MP/'mascot-party.x'),'-N','2','-p',str(p),'-pn',str(port),'-S','40','-b','10000','-P',str(2**255-19),'-IF',str(work/'Input'),'-v','two_party_curve']
            children.append(subprocess.Popen(command,cwd=work,env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP)),stdout=log,stderr=subprocess.STDOUT))
        deadline=start+180
        for child in children:
            while True:
                pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                if pid:
                    child.returncode=os.waitstatus_to_exitcode(status)
                    stats.append({'exit_code':child.returncode,'cpu_seconds':usage.ru_utime+usage.ru_stime,'peak_rss_bytes':usage.ru_maxrss})
                    break
                if time.monotonic()>deadline:raise TimeoutError('bounded curve control deadline')
                time.sleep(.02)
    finally:
        for child in children:
            if child.returncode is None:
                if child.poll() is None:child.kill()
                child.wait()
        for f in files:f.close()
    logs=[(work/f'party-{p}.log').read_text() for p in (0,1)]
    for stat,log in zip(stats,logs):
        counters=re.findall(r'EXACT_SOCKET_BYTES sent=(\d+) received=(\d+)',log)
        if len(counters)==1:stat['socket_sent_bytes'],stat['socket_received_bytes']=map(int,counters[0])
        stat['leftover_report']=[line.strip() for line in log.splitlines() if ' left' in line]
        stat['phase_report']=[line.strip() for line in log.splitlines() if line.startswith('Spent ')]
    if reject:
        passed=all(s['exit_code']!=0 for s in stats) and all('CURVE_MATCH' not in log for log in logs) and any('curve control low-order result' in log for log in logs)
    else:
        passed=all(s['exit_code']==0 for s in stats) and 'CURVE_MATCH 1' in logs[0]
        passed=passed and sum(s['socket_sent_bytes'] for s in stats)==sum(s['socket_received_bytes'] for s in stats)
    return {'passed':passed,'control':'low-order rejection' if reject else 'private X25519 equality',
            'controller_wall_seconds':time.monotonic()-start,'parties':stats,'directory':str(work)}

if __name__=='__main__':
    scalar=bytes(range(32))
    point=X25519PrivateKey.from_private_bytes(bytes(range(32,64))).public_key().public_bytes_raw()
    expected=X25519PrivateKey.from_private_bytes(scalar).exchange(X25519PublicKey.from_public_bytes(point))
    compile_control(expected)
    cases=[execute_control(scalar,point,31390),execute_control(scalar,bytes(32),31400,True)]
    report={'passed':all(c['passed'] for c in cases),'scope':'one private curve plus checked conversion control; no EMP curve or full send claim',
            'security':{'parties':2,'corruptions':1,'statistical_parameter':40,'computational_target':128,
                        'ot':'checked SoftSpoken','fresh_key_ot_directory_per_case':True},
            'field_sha256':sha(BASE/'x25519-field.json'),'compiler_source_sha256':sha(ROOT/'benchmarks/TwoPartyComparisonWork/curve_control.mpc'),
            'mixed_module_sha256':sha(BASE/'curve-module-snapshot/handshake_backend/mixed.py'),
            'field_executor_sha256':sha(BASE/'curve-module-snapshot/handshake_backend/field_dag.py'),
            'worker_sha256':sha(MP/'mascot-party.x'),'runtime_sha256':sha(MP/'libSPDZ.so'),
            'compiler_resource_report':(BASE/'mp-curve-compile.log').read_text(),'cases':cases}
    target=ROOT/'benchmarks/TwoPartyComparisonWork/curve-control-report.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':report['passed'],'report':str(target)}))
    if not report['passed']:raise SystemExit(1)
