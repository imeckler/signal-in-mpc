#!/usr/bin/env python3
"""Test isolated partial VM scratch hooks; never enables application retirement."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import secrets
import shutil
import subprocess
import sys
import time
from pin_tls_worker import build
from prepare_tls_shape import Shape

ROOT=Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build',action='store_true')
    parser.add_argument('--timeout',type=int,default=600)
    parser.add_argument('--port',type=int,default=19500)
    args=parser.parse_args()
    runtime=ROOT/'.deps/tls-scratch-runtime/MP-SPDZ'
    work=ROOT/'handshake_backend/ScratchWork'
    output=ROOT/'benchmarks/results/raw/tls-vm-scratch'/secrets.token_hex(8)
    output.mkdir(parents=True)
    def run_logged(command,name,cwd=runtime):
        with (output/name).open('wb') as log:
            subprocess.run(command,cwd=cwd,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
    if args.build:
        run_logged(['make','-j2','libSPDZ.so'],'library-build.log')
        if sys.platform=='darwin':
            run_logged(['install_name_tool','-id','@rpath/libSPDZ.so','libSPDZ.so'],'library-install-name.log')
        run_logged(['make','-f',str(work/'Makefile'),'TLS_ROOT='+str(ROOT/'handshake_backend'),
                    '../tls-scratch-fixture','../tls-stacked-checks'],'fixture-build.log')
    run_logged([str(runtime.parent/'tls-stacked-checks')],'stacked.log',ROOT)
    assert '18720 fields' in (output/'stacked.log').read_text()
    provenance=json.loads((work/'patch-provenance.json').read_text())
    assert digest(work/'vm-scratch.patch')==provenance['patch_sha256']
    for name, hashes in provenance['files'].items():
        assert digest(runtime/name)==hashes['after'],name
    source_paths=[*sorted(work.glob('*.h')),*sorted(work.glob('*.cpp')),work/'Makefile',
                  work/'vm-scratch.patch',work/'patch-provenance.json',
                  *sorted((ROOT/'handshake_backend').glob('*.h')),
                  ROOT/'scripts/prepare_tls_scratch_runtime.py',Path(__file__).resolve()]
    snapshots={str(p.relative_to(ROOT)):digest(p) for p in source_paths}
    executables=[runtime/'libSPDZ.so',runtime.parent/'tls-scratch-fixture',runtime.parent/'tls-stacked-checks']
    products={str(p.relative_to(ROOT)):digest(p) for p in executables}
    baseline=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    shape_backend=ROOT/'.deps/sharing-refresh/tls-application-shapes-v2'
    cache=output/'working';cache.mkdir()
    functions=[]
    for source, selected in [(baseline,['tls_begin-s:[256]-sbv:[256x1]',
                                       'tls_agreement-s:[256]-s:1-sbv:[256x1]']),
                             (shape_backend,[Shape(['tls-route-application',n]).descriptor for n in (6,1029,16385)])]:
        functions.extend(selected)
        for line in build(source,selected).splitlines()[1:]:
            hash_value,name=line.split(' ',1)
            path=cache/name;path.parent.mkdir(parents=True,exist_ok=True)
            if path.exists():assert digest(path)==hash_value
            else:shutil.copyfile(source/name,path)
            assert digest(path)==hash_value
    manifest=output/'programs.manifest';manifest.write_text(build(cache,functions))
    # Disposable loopback peer certificates; not application credentials.
    run_logged(['bash',str(baseline/'Scripts/setup-ssl.sh'),'5'],'setup-ssl.log',cache)
    hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*5)
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'passed':False,
            'parties':5,'threshold':2,'statistical_security_parameter':128,
            'binary_field_degree':128,'native_mpc_executed':False,
            'full_vm_erasure_implemented':False,'application_execution_enabled':False,
            'scope':'constructed secret VM memory/register objects and temp.Sansp only; explicit host quiescence; no freed allocation, preprocessing or PRNG cleanup',
            'source_sha256':snapshots,'product_sha256':products,
            'program_manifest_sha256':digest(manifest),'logs':str(output.relative_to(ROOT)),
            'stacked_check':'64 packed widths;18720 fields; nested hidden frames, shrink, pop and reuse; ASan/UBSan on test translation unit',
            'cases':[]}
    try:
        for capacity in (6,1029,16385):
            processes=[];logs=[];started=time.monotonic()
            case={'capacity':capacity,'passed':False}
            try:
                for party in range(5):
                    log=(output/f'capacity-{capacity}-party-{party}.log').open('wb');logs.append(log)
                    processes.append(subprocess.Popen([str(runtime.parent/'tls-scratch-fixture'),str(party),
                        str(hosts),str(args.port),str(manifest),str(capacity)],cwd=cache,stdout=log,stderr=subprocess.STDOUT))
                for p in processes:p.wait(timeout=max(1,args.timeout-(time.monotonic()-started)))
                assert [p.returncode for p in processes]==[0]*5
                for log in logs:log.flush()
                for party in range(5):
                    text=(output/f'capacity-{capacity}-party-{party}.log').read_text()
                    assert f'scratch fixture passed: capacity={capacity}; three calls; two guards;' in text
                case.update(passed=True,router_calls=3,uninitialized_and_outstanding_job_rejected=True,
                            external_output_shares_preserved=True,automatic_worker_cleanup=True,
                            basepoint_agreement_after_cleanup=capacity==6)
            finally:
                for p in processes:
                    if p.poll() is None:p.kill()
                for p in processes:p.wait()
                for log in logs:log.close()
                case.update(exit_codes=[p.returncode for p in processes],elapsed_seconds=time.monotonic()-started)
                report['cases'].append(case)
            print('Scratch cleanup passed capacity',capacity,'in',case['elapsed_seconds'],'seconds',flush=True)
        assert snapshots=={str(p.relative_to(ROOT)):digest(p) for p in source_paths}
        assert products=={str(p.relative_to(ROOT)):digest(p) for p in executables}
        report.update(passed=True,native_mpc_executed=True)
    except Exception as error:
        report['error']=repr(error)
    finally:
        report['log_sha256']={str(p.relative_to(ROOT)):digest(p) for p in sorted(output.glob('*.log'))}
        text=json.dumps(report,indent=2)+'\n'
        (output/'report.json').write_text(text)
        (ROOT/'benchmarks/results/tls-vm-scratch-checks.json').write_text(text)
    if not report['passed']:raise SystemExit('scratch check failed: '+str(output))


if __name__=='__main__':main()
