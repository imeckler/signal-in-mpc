#!/usr/bin/env python3
"""Five-party synthetic owned-share store fixture; does not activate TLS/session gates."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from signal_backend.shape import SendShape
from scripts.pin_tls_worker import build
from scripts.check_lean_signal_spqr_send import cases

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--port',type=int,default=19720)
    ap.add_argument('--timeout',type=int,default=900);args=ap.parse_args()
    assert 1024<args.port<65530 and 1<=args.timeout<=3600
    shape=SendShape(['signal-spqr-send','0','1','1','1','1','0','none','none'])
    stage=ROOT/'.deps/signal-established-native'/shape.stem
    manifest=stage/'signal-send.manifest'
    assert manifest.read_text()==build(stage,[shape.descriptor])
    runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    subprocess.run(['make','-C',str(runtime),'-f',str(ROOT/'signal_backend/Makefile'),
        'SIGNAL_ROOT='+str(ROOT/'signal_backend'),'SIGNAL_OUTPUT='+str(ROOT/'.deps/signal-native-store-fixture'),
        str(ROOT/'.deps/signal-native-store-fixture')],check=True)
    data=stage/'Player-Data';data.mkdir(exist_ok=True)
    # Disposable local fixture transport certificates only; no live identities.
    for pattern in ('*.pem','*.key','*.0'):
        for p in (runtime/'Player-Data').glob(pattern):shutil.copy2(p,data/p.name)
    logdir=stage/'fixture-logs';logdir.mkdir(exist_ok=True)
    hosts=logdir/'hosts';hosts.write_text('127.0.0.1\n'*5)
    _,raw,expected,labels,_=next(cases())
    indices=[labels.index('consecutive-coupled-state-'+str(i)) for i in range(2)]
    fixture=logdir/'public-fixtures.txt';fixture.write_text(''.join(raw[i].hex()+' '+expected[i].hex()+'\n' for i in indices))
    processes=[];streams=[];started=time.monotonic();exit_codes=[]
    try:
        for party in range(5):
            stream=(logdir/f'party-{party}.log').open('w');streams.append(stream)
            processes.append(subprocess.Popen([str(ROOT/'.deps/signal-native-store-fixture'),str(party),
                str(hosts),str(args.port),str(manifest),str(fixture)],cwd=stage,stdout=stream,stderr=subprocess.STDOUT))
        deadline=time.monotonic()+args.timeout
        while any(p.poll() is None for p in processes):
            if time.monotonic()>deadline:raise TimeoutError('native Signal store fixture timed out')
            if any(p.poll() not in (None,0) for p in processes):raise RuntimeError('native fixture party failed')
            time.sleep(.1)
        exit_codes=[p.returncode for p in processes]
        assert exit_codes==[0]*5
        for stream in streams:stream.flush()
        assert all('native Signal store fixture passed' in (logdir/f'party-{p}.log').read_text() for p in range(5))
    finally:
        for p in processes:
            if p.poll() is None:p.kill()
        for p in processes:p.wait()
        for stream in streams:stream.close()
    report={'passed':True,'parties':5,'threshold':2,'native_mpc_executed':True,
        'consecutive_sends':2,'elapsed_seconds':time.monotonic()-started,'party_exit_codes':exit_codes,
        'public_fixture_only':True,'opened_outputs':'public fixture Signal wire only; no chain state opened',
        'native_fixture_sha256':sha(ROOT/'.deps/signal-native-store-fixture'),
        'manifest_sha256':sha(manifest),'fixture_sha256':sha(fixture),
        'logs':str(logdir.relative_to(ROOT)),
        'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__),
           ROOT/'signal_backend/native_store_fixture.cpp',ROOT/'signal_backend/EstablishedSendStore.h',
           ROOT/'signal_backend/SendShape.h',ROOT/'signal_backend/PrivateGrpcRequest.h',ROOT/'handshake_backend/NativeWorker.h',
           ROOT/'programs/signal_export.mpc',ROOT/'signal_backend/prepare.py']},
        'owned_bits_request_framing_executed':True,'tls_payload_handoff_tested':False,'full_libsignal_session_refinement':False,
        'application_readiness_gate_opened':False,'production_ready':False,'wan_throughput_measured':False}
    (ROOT/'signal_backend/native-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Five-party shared-state Signal fixture passed; two consecutive sends; no TLS activation')
if __name__=='__main__':main()
