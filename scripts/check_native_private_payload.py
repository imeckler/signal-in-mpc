#!/usr/bin/env python3
"""Disposable five-party private-length TLS/status-gate fixture, not a service test."""
import hashlib
import json
import os
from pathlib import Path
import secrets
import shutil
import subprocess
import time
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from prepare_tls_shape import install, Shape

ROOT=Path(__file__).resolve().parents[1]
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    output=ROOT/'benchmarks/results/raw/native-private-payload'/secrets.token_hex(8)
    output.mkdir(parents=True)
    cache=output/'working';cache.mkdir()
    baseline=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    runtime=ROOT/'.deps/tls-session-runtime/MP-SPDZ'
    report={'passed':False,'native_mpc_executed':False,'scope':'public disposable native private-length seal and authenticated status gate; no live service',
            'application_gate_changed':False,'cases':[],'cleanup_errors':[],'logs':str(output.relative_to(ROOT))}
    started=time.monotonic();processes=[];logs=[]
    def logged(cmd,name,cwd=ROOT):
        with (output/name).open('w') as log:subprocess.run(cmd,cwd=cwd,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=900)
    try:
        for folder in ('Compiler',):shutil.copytree(baseline/folder,cache/folder)
        shutil.copy2(baseline/'compile.py',cache/'compile.py')
        for folder in ('Source','Bytecode','Schedules','Functions'):(cache/'Programs'/folder).mkdir(parents=True)
        install(cache,ROOT/'.deps/sharing-refresh/tls-application-shapes-v2/Worker-Public/tls-shape-emitter',ROOT/'.lake/build/bin/private_tls_emitter')
        logged([os.sys.executable,str(cache/'Worker-Public/tls-shape-compiler'),'tls-seal-private-record','16'],'compile.log',cache)
        manifests=list((cache/'Worker-Public').glob('*.manifest'))
        if not manifests:manifests=list(cache.rglob('*.manifest'))
        assert len(manifests)==1,manifests
        manifest=manifests[0]
        logged(['bash',str(baseline/'Scripts/setup-ssl.sh'),'5'],'ssl.log',cache)
        hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*5)
        key=bytes(range(16));iv=bytes(range(12));data=bytes(range(16))
        for run,invalid in enumerate(((255,17),(0,0))):
            cases=[]
            for seq,(valid,length) in enumerate([(255,0),(255,1),(255,15),(255,16),invalid]):
                sequence=seq.to_bytes(8,'big');raw=key+iv+sequence+bytes([valid])+length.to_bytes(2,'big')+data
                expected='reject'
                if seq<4:
                    inner=data[:length]+b'\x17'+bytes(16-length)
                    header=b'\x17\x03\x03'+(33).to_bytes(2,'big')
                    nonce=bytes(a^b for a,b in zip(iv,bytes(4)+sequence))
                    expected=(header+AESGCM(key).encrypt(nonce,inner,header)).hex()
                cases.append(raw.hex()+' '+expected)
            fixture=output/f'cases-{run}.txt';fixture.write_text('\n'.join(cases)+'\n')
            processes=[];logs=[]
            for party in range(5):
                log=(output/f'run-{run}-party-{party}.log').open('w');logs.append(log)
                processes.append(subprocess.Popen([str(runtime.parent/'tls-private-payload-fixture'),str(party),str(hosts),str(19720+run*10),str(manifest),str(fixture)],cwd=cache,stdout=log,stderr=subprocess.STDOUT))
            codes=[p.wait(timeout=max(1,900-(time.monotonic()-started))) for p in processes]
            for log in logs:log.close()
            logs=[]
            report['cases'].append({'rejection':'bounds' if run==0 else 'producer_status','exit_codes':codes,'valid_lengths':[0,1,15,16], 'rejected_wire_release_calls':0 if codes==[0]*5 else None})
            if codes!=[0]*5:raise RuntimeError('native private payload case failed; inspect public logs')
        report.update(passed=True,native_mpc_executed=True)
    except Exception as error:report['error']=str(error)
    finally:
        for p in processes:
            try:
                if p.poll() is None:p.terminate()
                try:p.wait(timeout=5)
                except subprocess.TimeoutExpired:p.kill();p.wait(timeout=5)
            except Exception as error:report['cleanup_errors'].append(str(error))
        for log in logs:log.close()
        names=['scripts/check_native_private_payload.py','handshake_backend/PayloadWork/native_fixture.cpp','handshake_backend/PayloadWork/StatusGate.h','handshake_backend/PayloadWork/PrivatePayload.h','handshake_backend/NativeSession.h','TlsMpc/TlsPrivateSeal.lean','handshake_backend/PayloadWork/EmitPrivateTls.lean','scripts/prepare_tls_shape.py','handshake_backend/SessionWork/Makefile','.deps/tls-session-runtime/tls-private-payload-fixture','.deps/tls-session-runtime/tls-worker','.deps/tls-session-runtime/MP-SPDZ/libSPDZ.so','.lake/build/bin/private_tls_emitter']
        report['sha256']={n:digest(ROOT/n) for n in names if (ROOT/n).is_file()}
        report['log_sha256']={str(p.relative_to(ROOT)):digest(p) for p in output.glob('*.log')}
        report['elapsed_seconds']=time.monotonic()-started
        if report['cleanup_errors']:report['passed']=False
        text=json.dumps(report,indent=2)+'\n'
        (output/'report.json').write_text(text);(ROOT/'benchmarks/results/tls-native-private-payload.json').write_text(text);print(text)
    if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
