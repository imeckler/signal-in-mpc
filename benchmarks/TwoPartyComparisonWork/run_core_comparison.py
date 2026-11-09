"""Equal two-send core and balanced verification wrapper across three entries."""
import hashlib
import json
import os
import pathlib
import re
import subprocess
import tempfile
import time
import argparse

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'
MP=BASE/'data61-MP-SPDZ-113c4e4'
PREP=BASE/'signal-core-2-check'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def run(backend,port,batch=10000,bucket=4):
    work=pathlib.Path(tempfile.mkdtemp(prefix='core-'+backend+'-',dir=BASE))
    children=[];streams=[];stats=[];failure=None;start=time.monotonic()
    try:
        if backend!='emp':
            (work/'Player-Data').mkdir();(work/'Programs').symlink_to(MP/'Programs',target_is_directory=True)
            for p,who in ((0,'bob'),(1,'alice')):
                (work/f'Input-P{p}-0').write_text(' '.join(str(x) for x in (PREP/(who+'.bin')).read_bytes())+'\n')
        for p in (0,1):
            stream=open(work/f'party-{p}.log','w');streams.append(stream)
            if backend=='emp':
                who='bob' if p==0 else 'alice';party=2 if p==0 else 1
                command=[str(BASE/'emp-worker'),str(party),str(port),str(PREP/'circuit.txt'),str(PREP/(who+'.bin')),str(work/'output.bin'),str(work/f'party-{p}.json')]
                # EMP's ALICE must listen before BOB connects; NetIO retries, so
                # starting BOB first is supported but measured waiting is included.
                env=dict(os.environ,DYLD_LIBRARY_PATH=str(BASE/'install/lib'))
            else:
                command=[str(MP/f'{backend}-party.x'),'-N','2','-p',str(p),'-pn',str(port),'-S','40','-b',str(batch),'-B',str(bucket),'-v','-IF',str(work/'Input')]
                if backend=='mascot':command+=['-P',str(2**255-19)]
                command+=['two_party_signal_core'];env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP))
            children.append(subprocess.Popen(command,cwd=work,env=env,stdout=stream,stderr=subprocess.STDOUT))
        deadline=start+120
        for child in children:
            while True:
                pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                if pid:
                    child.returncode=os.waitstatus_to_exitcode(status)
                    stats.append({'exit_code':child.returncode,'cpu_seconds':usage.ru_utime+usage.ru_stime,'peak_rss_bytes':usage.ru_maxrss});break
                if time.monotonic()>deadline:raise TimeoutError('bounded native core deadline')
                time.sleep(.02)
    except Exception as exc:failure=type(exc).__name__
    finally:
        for child in children:
            if child.returncode is None:
                if child.poll() is None:child.kill()
                child.wait()
        for stream in streams:stream.close()
    logs=[(work/f'party-{p}.log').read_text() for p in (0,1)]
    passed=failure is None and len(stats)==2 and all(s['exit_code']==0 for s in stats)
    if passed and backend=='emp':
        passed=(work/'output.bin').read_bytes()==b'\x01'
        for p,stat in enumerate(stats):stat['backend_metrics']=json.loads((work/f'party-{p}.json').read_text())
        passed=passed and stats[0]['backend_metrics']['sent_bytes']==stats[1]['backend_metrics']['received_bytes'] and stats[1]['backend_metrics']['sent_bytes']==stats[0]['backend_metrics']['received_bytes']
    elif passed:
        passed='SIGNAL_CORE_MATCH 1' in logs[0]
        for stat,log in zip(stats,logs):
            counters=re.findall(r'EXACT_SOCKET_BYTES sent=(\d+) received=(\d+)',log)
            if len(counters)!=1:passed=False;continue
            stat['socket_sent_bytes'],stat['socket_received_bytes']=map(int,counters[0])
            stat['phase_report']=[line.strip() for line in log.splitlines() if line.startswith('Spent ')]
            stat['leftover_report']=[line.strip() for line in log.splitlines() if ' left' in line]
        passed=passed and sum(s.get('socket_sent_bytes',0) for s in stats)==sum(s.get('socket_received_bytes',0) for s in stats)
    return {'passed':passed,'backend':backend,'preprocessing_batch_option':batch,'sacrifice_bucket':bucket,
            'controller_wall_seconds':time.monotonic()-start,'parties':stats,
            'failure_category':failure,'directory':str(work)}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--tinier-bulk',action='store_true');args=parser.parse_args()
    prepared=json.loads((PREP/'prepare-report.json').read_text())
    if sha(PREP/'circuit.txt')!=prepared['bristol_sha256']:raise ValueError('prepared graph drift')
    results=[]
    report={'scope':'matched two-send zero-plaintext Signal core and balanced equality only; not full Signal/TLS or sustained throughput',
            'prepared':prepared,'security':'declared S40/t1 two-party candidates; legacy EMP local mask/failclosed overlay, no S128 validation',
            'shared_state':'private returned chain/counter routed internally; only aggregate equality opens; no durable or inter-session handoff claim',
            'compile_scope':'MP packed execution preserves exact core and verification AND count; no application field work in these rows',
            'bytecode_sha256':sha(MP/'Programs/Bytecode/two_party_signal_core-0.bc'),
            'emp_worker_sha256':sha(BASE/'emp-worker'),'tinier_worker_sha256':sha(MP/'tinier-party.x'),
            'mascot_worker_sha256':sha(MP/'mascot-party.x'),'mp_runtime_sha256':sha(MP/'libSPDZ.so'),
            'source_sha256':sha(ROOT/'benchmarks/TwoPartyComparisonWork/signal_core_check.mpc'),
            'expected_fixture_sha256':sha(PREP/'expected-logical.json'),'results':results,'passed':False}
    target=ROOT/'benchmarks/TwoPartyComparisonWork'/('core-tinier-bulk-report.json' if args.tinier_bulk else 'core-comparison-report.json')
    try:
        backends=('tinier',) if args.tinier_bulk else ('emp','tinier','mascot')
        for i,backend in enumerate(backends):
            result=run(backend,31460 if args.tinier_bulk else 31430+i*10,
                       prepared['counts']['AND'] if args.tinier_bulk else 10000,3 if args.tinier_bulk else 4)
            results.append(result)
            if not result['passed']:break
        report['passed']=len(results)==len(backends) and all(r['passed'] for r in results)
    finally:target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':report['passed'],'report':str(target),'results':len(results)}))
    if not report['passed']:raise SystemExit(1)
