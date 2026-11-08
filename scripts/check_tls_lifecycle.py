#!/usr/bin/env python3
"""Check isolated serialized-buffer cleanup plus five-party scratch/reuse regressions."""
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
    parser.set_defaults(lifetime=True)
    parser.add_argument('--timeout',type=int,default=600)
    parser.add_argument('--port',type=int,default=19500)
    args=parser.parse_args()
    runtime=ROOT/'.deps/tls-lifecycle-runtime/MP-SPDZ'
    buffers=ROOT/'handshake_backend/ByteBufferWork'
    epoch=ROOT/'handshake_backend/EpochWork'
    lifecycle=ROOT/'handshake_backend/LifecycleWork'
    work=ROOT/'handshake_backend/ScratchWork'
    lifetime=ROOT/'handshake_backend/LifetimeWork'
    label='tls-lifecycle'
    output=ROOT/'benchmarks/results/raw'/label/secrets.token_hex(8)
    output.mkdir(parents=True)
    def run_logged(command,name,cwd=runtime):
        with (output/name).open('wb') as log:
            subprocess.run(command,cwd=cwd,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=min(args.timeout,30) if name=='buffers.log' else args.timeout)
    if args.build:
        run_logged(['make','-j2','libSPDZ.so'],'library-build.log')
        if sys.platform=='darwin':
            run_logged(['install_name_tool','-id','@rpath/libSPDZ.so','libSPDZ.so'],'library-install-name.log')
        makefile=lifecycle/'Makefile'
        targets=['../tls-lifecycle-fixture','../tls-stacked-checks','../tls-lifecycle-buffer-checks','../tls-prng-lifetime-checks','../tls-owned-storage-checks']
        if args.lifetime:targets.append('../tls-lifetime-checks')
        run_logged(['make','-f',str(makefile),'TLS_ROOT='+str(ROOT/'handshake_backend'),*targets],'fixture-build.log')
    run_logged([str(runtime.parent/'tls-stacked-checks')],'stacked.log',ROOT)
    assert '18720 fields' in (output/'stacked.log').read_text()
    provenance=json.loads((work/'patch-provenance.json').read_text())
    assert digest(work/'vm-scratch.patch')==provenance['patch_sha256']
    for name, hashes in provenance['files'].items():
        if name not in ('Processor/Machine.h','Processor/Machine.hpp'):
            assert digest(runtime/name)==hashes['after'],name
    if args.lifetime:
        lifetime_provenance=json.loads((lifetime/'patch-provenance.json').read_text())
        assert digest(lifetime/'fixed-field-lifetime.patch')==lifetime_provenance['patch_sha256']
        for name,hashes in lifetime_provenance['files'].items():
            assert digest(runtime/name)==hashes['after'],name
            assert digest(ROOT/'.deps/sharing-refresh/MP-SPDZ'/name)==hashes['before'],name
        run_logged([str(runtime.parent/'tls-lifetime-checks')],'lifetime-candidate.log',ROOT)
        run_logged([str(ROOT/'.deps/sharing-refresh/tls-lifetime-checks'),'baseline'],'lifetime-baseline.log',ROOT)
        assert 'candidate payload cleanup passed:' in (output/'lifetime-candidate.log').read_text()
        assert '; 0 nonzero;' in (output/'lifetime-candidate.log').read_text()
        assert 'baseline retained payloads:' in (output/'lifetime-baseline.log').read_text()
    buffer_provenance=json.loads((buffers/'patch-provenance.json').read_text())
    assert digest(buffers/'serialized-buffer.patch')==buffer_provenance['patch_sha256']
    for name,hashes in buffer_provenance['files'].items():
        assert digest(ROOT/'.deps/sharing-refresh/MP-SPDZ'/name)==hashes['before'],name
    epoch_provenance=json.loads((epoch/'patch-provenance.json').read_text())
    assert digest(epoch/'runtime-epoch.patch')==epoch_provenance['patch_sha256']
    for name,hashes in epoch_provenance['files'].items():
        if name not in ('Processor/Machine.h','Processor/Machine.hpp'):
            assert digest(runtime/name)==hashes['after'],name
    lifecycle_provenance=json.loads((lifecycle/'patch-provenance.json').read_text())
    assert digest(lifecycle/'owned-storage.patch')==lifecycle_provenance['patch_sha256']
    for name,hashes in lifecycle_provenance['files'].items():
        assert digest(runtime/name)==hashes['after'],name
    run_logged([str(runtime.parent/'tls-lifecycle-buffer-checks')],'buffers.log',ROOT)
    run_logged([str(runtime.parent/'tls-owned-storage-checks')],'storage.log',ROOT)
    run_logged([str(runtime.parent/'tls-prng-lifetime-checks')],'prng.log',ROOT)
    assert 'serialized buffer cleanup passed:' in (output/'buffers.log').read_text()
    source_paths=[*sorted(work.glob('*.h')),*sorted(work.glob('*.cpp')),work/'Makefile',
                  work/'vm-scratch.patch',work/'patch-provenance.json',
                  *sorted((ROOT/'handshake_backend').glob('*.h')),
                  ROOT/'scripts/prepare_tls_scratch_runtime.py',Path(__file__).resolve()]
    if args.lifetime:
        source_paths += [*sorted(lifetime.glob('*.cpp')),lifetime/'Makefile',
                         lifetime/'fixed-field-lifetime.patch',lifetime/'patch-provenance.json',
                         ROOT/'scripts/prepare_tls_lifetime_runtime.py']
    source_paths += [*sorted(buffers.glob('*')), *sorted(epoch.glob('*')), *sorted(lifecycle.glob('*')), ROOT/'scripts/prepare_tls_lifecycle_runtime.py', ROOT/'signal_backend/SendShape.h']
    snapshots={str(p.relative_to(ROOT)):digest(p) for p in source_paths}
    executables=[runtime/'libSPDZ.so',runtime.parent/'tls-lifecycle-fixture',runtime.parent/'tls-stacked-checks']
    if args.lifetime:
        executables += [runtime.parent/'tls-lifetime-checks',ROOT/'.deps/sharing-refresh/tls-lifetime-checks',
                        ROOT/'.deps/sharing-refresh/MP-SPDZ/libSPDZ.so']
    executables += [runtime.parent/'tls-lifecycle-buffer-checks',runtime.parent/'tls-prng-lifetime-checks',runtime.parent/'tls-owned-storage-checks']
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
            'fixed_field_destruction_cleanup_tested':args.lifetime,
            'runtime_epoch_renewal_tested':True,
            'owned_stack_and_gmp_tested':True,
            'storage_checks':(output/'storage.log').read_text().strip(),
            'prng_checks':(output/'prng.log').read_text().strip(),
            'serialized_buffer_checks':(output/'buffers.log').read_text().strip(),
            'serialized_buffer_sanitizers':['address','undefined'],
            'serialized_buffer_test_boundary':'test translation unit and exact candidate Tools/octetStream.cpp sanitized; remaining candidate library optimized; global new[]/delete[] public allocation observer',
            'scope':'serialized octetStream/FlexBuffer discarded allocations and fixed field/VM scratch regression; no full live protocol, bigint or PRNG cleanup',
            'source_sha256':snapshots,'product_sha256':products,
            'program_manifest_sha256':digest(manifest),'logs':str(output.relative_to(ROOT)),
            'stacked_check':'64 packed widths;18720 fields; nested hidden frames, shrink, pop and reuse; ASan/UBSan on test translation unit',
            'cases':[]}
    if args.lifetime:
        report['field_lifetime_local_checks']={
            'candidate':(output/'lifetime-candidate.log').read_text().strip(),
            'baseline':(output/'lifetime-baseline.log').read_text().strip(),
            'sanitizers':['address','undefined'],
            'scope':'fixed field payloads observed in allocator deallocate before free; five native types, vector growth/shrink/clear/replacement and constructor failure; normal library build with sanitized test translation unit',
            'raw_byte_bigint_live_protocol_and_prng_cleanup':False}
    try:
        for capacity in (6,1029,16385):
            processes=[];logs=[];started=time.monotonic()
            case={'capacity':capacity,'passed':False}
            try:
                for party in range(5):
                    log=(output/f'capacity-{capacity}-party-{party}.log').open('wb');logs.append(log)
                    processes.append(subprocess.Popen([str(runtime.parent/'tls-lifecycle-fixture'),str(party),
                        str(hosts),str(args.port),str(manifest),str(capacity)],cwd=cache,stdout=log,stderr=subprocess.STDOUT))
                for p in processes:p.wait(timeout=max(1,args.timeout-(time.monotonic()-started)))
                assert [p.returncode for p in processes]==[0]*5
                for log in logs:log.flush()
                for party in range(5):
                    text=(output/f'capacity-{capacity}-party-{party}.log').read_text()
                    assert f'lifecycle fixture passed: capacity={capacity}; three calls; two guards;' in text
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
        (ROOT/'benchmarks/results'/f'{label}-checks.json').write_text(text)
    if not report['passed']:raise SystemExit('scratch check failed: '+str(output))


if __name__=='__main__':main()
