#!/usr/bin/env python3
"""Actual five-party TLS application lifecycle with unopened synthetic producer frames.

The fixture-only producer uses disposable known state. Its generic gRPC framing
is deliberately NOT claimed to be the real Signal service protocol.
"""
import argparse
from datetime import datetime,timezone
import hashlib,json,os,secrets,signal,socket,subprocess,threading,time,shutil
from pathlib import Path
from check_full_handshake import certificates,OPENSSL
from pin_tls_worker import build
from prepare_tls_shape import install,Shape
ROOT=Path(__file__).resolve().parents[1]

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def provision(backend):
    baseline=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    functions=[p.name for p in (baseline/'Programs/Functions').iterdir()
               if p.is_file() and p.name.startswith(('tls_binary_','tls_begin-','tls_agreement-'))]
    def copy_manifest(source,text):
        for line in text.splitlines()[1:]:
            value,name=line.split(' ',1);source_file=source/name
            assert digest(source_file)==value,name
            target=backend/name;target.parent.mkdir(parents=True,exist_ok=True)
            if target.exists(): assert digest(target)==value,('immutable closure collision',name)
            else: shutil.copyfile(source_file,target)
    copy_manifest(baseline,build(baseline,functions))
    signal_root=ROOT/'.deps/signal-established-native/signal-spqr-send-0-1-1-1-1-0-none-none'
    signal_manifest=signal_root/'signal-send.manifest'
    text=signal_manifest.read_text();copy_manifest(signal_root,text)
    functions.extend(Path(line.split(' ',1)[1]).name for line in text.splitlines()[1:]
                     if line.split(' ',1)[1].startswith('Programs/Functions/'))
    # Install the application-capable helper, not the historical handshake-only
    # helper in the canonical runtime. Keep its archived accepted TLS emitter.
    compiler_config=json.loads((baseline/'Worker-Public/tls-shape-toolchain.json').read_text())
    for name in compiler_config['files']:
        target=backend/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(baseline/name,target)
    emitter=ROOT/'.deps/sharing-refresh/tls-application-shapes-v2/Worker-Public/tls-shape-emitter'
    (backend/'Programs/Source').mkdir(parents=True,exist_ok=True)
    install(backend,emitter)
    for arguments in [('tls-seal-record',23,228,0),('tls-seal-record',22,5,0),
                      ('tls-open-record',48),('tls-route-application',27),
                      ('tls-open-record',255),('tls-route-application',234),
                      ('tls-open-record',27),('tls-route-application',6),('tls-post-handshake',6)]:
        shape=Shape(arguments)
        subprocess.run([str(backend/'Worker-Public/tls-shape-compiler'),*shape.arguments],cwd=backend,check=True)
        functions.append(shape.descriptor)
    # The fixed traffic-update kernel was never provisioned in the old boot
    # cache. Compile/pin its real Lean export before starting any private work.
    update='tls_binary_tls_update_traffic-sbv:[256x1]-sbv:[256x1]'
    if not (backend/'Programs/Functions'/update).exists():
        with (backend/'Worker-Public/tls-update-traffic.json').open('wb') as artifact:
            subprocess.run([str(emitter),'tls-update-traffic'],stdout=artifact,check=True)
        image=json.loads((backend/'Worker-Public/tls-update-traffic.json').read_text())
        assert image['input_bits']==256 and len(image['outputs'])==256 and image['name']=='tls-update-traffic'
        source='program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text()
        (backend/'Programs/Source/tls_lifecycle_export.mpc').write_text(source)
        config=json.loads((backend/'Worker-Public/tls-shape-toolchain.json').read_text())
        subprocess.run([config['python']['path'],'-B','compile.py','-M','-X','-P',str(2**255-19),
                        'tls_lifecycle_export','binary-packed','Worker-Public/tls-update-traffic.json'],
                       cwd=backend,check=True,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'))
    functions.append(update)
    return build(backend,functions,['Worker-Public/tls-shape-compiler','Worker-Public/tls-shape-toolchain.json'])

def bridge(listener,server,result):
    def command(text):
        server.stdin.write(text+'\n');server.stdin.flush()
        line=server.stdout.readline().strip()
        status,value=line.split(' ',1)
        if status not in ('ready','waiting'):raise ValueError('OpenSSL fixture response')
        return status,bytes.fromhex(value) if value!='-' else b''
    try:
        with listener: connection,_=listener.accept()
        with connection:
            connection.settimeout(1800)
            def exact(n):
                out=bytearray()
                while len(out)<n:
                    data=connection.recv(n-len(out))
                    if not data:raise EOFError('client transport closed')
                    out.extend(data)
                return bytes(out)
            ready=False
            while True:
                try: header=exact(5)
                except EOFError:
                    if result.get('replay_sent'):break
                    raise
                n=int.from_bytes(header[3:5],'big')
                if n>16640:raise ValueError('oversize record')
                status,wire=command((header+exact(n)).hex())
                if not ready:
                    if status=='ready':ready=True;result['client_finished_accepted']=True
                    if wire:connection.sendall(wire)
                    continue
                if wire:
                    # This server emits echo application data only after SSL_read
                    # authenticated an incoming application payload. KU/close
                    # inputs alone produce no echo here.
                    result['private_application_records']+=1
                    connection.sendall(wire)
                    if result['private_application_records']==1:
                        _,update=command('update-request')
                        if not update:raise ValueError('server update absent')
                        result['server_requested_update']=True;connection.sendall(update)
                    if result['private_application_records']==3:
                        _,replay=command('replay')
                        if replay!=wire:raise ValueError('replay fixture mismatch')
                        result['replay_sent']=True;connection.sendall(replay)
            result['closed_after_replay']=True
    except Exception as error: result['error']=str(error)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--build',action='store_true')
    ap.add_argument('--timeout',type=int,default=1800);ap.add_argument('--port',type=int,default=19800)
    args=ap.parse_args();backend=ROOT/'.deps/tls-session-runtime/MP-SPDZ'
    output=ROOT/'benchmarks/results/raw/native-application-lifecycle'/secrets.token_hex(8);output.mkdir(parents=True)
    def logged(command,name,cwd=ROOT):
        with (output/name).open('wb') as log:
            subprocess.run(command,cwd=cwd,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
    if args.build:
        logged(['make','-j2','libSPDZ.so'],'library-build.log',backend)
        logged(['install_name_tool','-id','@rpath/libSPDZ.so','libSPDZ.so'],'install-name.log',backend)
        logged(['make','-f',str(ROOT/'handshake_backend/SessionWork/Makefile'),
                'TLS_ROOT='+str(ROOT/'handshake_backend'),'../tls-private-application-worker','../tls-session-host-checks'],'worker-build.log',backend)
    logged([str(backend.parent/'tls-session-host-checks')],'host-checks.log')
    logged(['lake','env','lean',str(ROOT/'handshake_backend/SessionWork/NativeApplicationFixture.lean')],'controller-check.log')
    manifest=output/'programs.manifest';manifest.write_text(provision(backend))
    baseline=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    logged(['bash',str(baseline/'Scripts/setup-ssl.sh'),'5'],'peer-certificates.log',backend)
    for name in ('public_auth','fixture_server'):
        logged(['c++','-std=c++20','-O2','-I'+str(OPENSSL/'include'),str(ROOT/f'handshake_backend/{name}.cpp'),
                '-L'+str(OPENSSL/'lib'),'-lssl','-lcrypto','-o',str(output/name)],name+'-build.log')
    profiles,trust=certificates(output);cert,key=profiles['ed25519']
    hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*5)
    session=secrets.token_hex(32)
    listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen(1);listener.settimeout(args.timeout)
    port=listener.getsockname()[1]
    server_log=(output/'server.log').open('w')
    server=subprocess.Popen([str(output/'fixture_server'),str(cert),str(key),'512','no','h2'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=server_log,text=True)
    server_result={'client_finished_accepted':False,'private_application_records':0,'server_requested_update':False,'replay_sent':False}
    thread=threading.Thread(target=bridge,args=(listener,server,server_result),daemon=True);thread.start()
    names=[Path(__file__),*sorted((ROOT/'handshake_backend').glob('*.h')),
           *sorted((ROOT/'handshake_backend/SessionWork').glob('*.h')),
           ROOT/'handshake_backend/SessionWork/worker_main.cpp',ROOT/'handshake_backend/SessionWork/NativeApplicationFixture.lean',
           ROOT/'handshake_backend/SessionWork/Makefile',*[ROOT/'signal_backend'/name for name in ['SendShape.h','EstablishedSendStore.h','PrivateGrpcRequest.h','PublicSyntheticProducer.h']],
           backend/'libSPDZ.so',backend.parent/'tls-private-application-worker',manifest,ROOT/'handshake_backend/fixture_server.cpp']
    names += [ROOT/name for name in ['TlsMpc/TlsWorkerProcess.lean','TlsMpc/TlsWorkerPipe.lean',
              'TlsMpc/TlsWorker.lean','TlsMpc/TlsClient.lean','TlsMpc/TlsApplication.lean',
              'TlsMpc/TlsApplicationPolicy.lean','TlsMpc/TlsWire.lean',
              '.lake/build/lib/lean/TlsMpc/TlsWorkerPipe.olean']]
    hashes={str(p.relative_to(ROOT)):digest(p) for p in names}
    canonical=digest(baseline/'libSPDZ.so')
    processes=[];logs=[];cleanup_errors=[];started=time.monotonic()
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'passed':False,'parties':5,'threshold':2,
            'native_mpc_executed':False,'candidate_application_gate_activated':False,
            'production_signal_service_protocol_tested':False,'synthetic_frame_bytes':228,
            'full_vm_erasure_implemented':False,'full_system_complete':False,
            'scope':'owned-storage lifecycle plus synthetic shared Signal/HTTP2-gRPC producer through real TLS; OpenSSL/compiler/OS assumptions remain',
            'source_and_product_sha256':hashes,'logs':str(output.relative_to(ROOT))}
    try:
        for party in range(5):
            log=(output/f'party-{party}.log').open('w');logs.append(log)
            command=['lake','env','lean','--run',str(ROOT/'handshake_backend/SessionWork/NativeApplicationFixture.lean'),
                     str(backend.parent/'tls-private-application-worker'),str(backend),str(party),str(hosts),str(args.port),str(manifest),session,
                     '127.0.0.1',str(port),'server.example',str(output/'public_auth'),str(trust),'228']
            processes.append(subprocess.Popen(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True))
        cases=[]
        for party,p in enumerate(processes):
            stdout,_=p.communicate(timeout=max(1,args.timeout-(time.monotonic()-started)))
            (output/f'party-{party}.json').write_text(stdout)
            assert p.returncode==0,('controller failed',party,p.returncode)
            case=json.loads(stdout);assert case['passed'],case;cases.append(case)
        thread.join(timeout=15)
        assert not thread.is_alive() and 'error' not in server_result,server_result
        assert server_result['client_finished_accepted'] and server_result['private_application_records']==3
        assert server_result['server_requested_update'] and server_result['replay_sent'] and server_result['closed_after_replay']
        assert all(digest(p)==hashes[str(p.relative_to(ROOT))] for p in names),'source/product changed during run'
        assert digest(baseline/'libSPDZ.so')==canonical,'canonical library changed'
        report.update(passed=True,native_mpc_executed=True,candidate_application_gate_activated=True,controllers=cases)
    except Exception as error:report['error']=repr(error)
    finally:
        for p in processes:
            try:os.killpg(p.pid,signal.SIGKILL)
            except ProcessLookupError:pass
            except PermissionError:
                try:p.terminate()
                except ProcessLookupError:pass
                except Exception as error:cleanup_errors.append(('terminate',p.pid,repr(error)))
            except Exception as error:cleanup_errors.append(('killpg',p.pid,repr(error)))
        for p in processes:
            try:p.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:p.kill();p.wait(timeout=5)
                except Exception as error:cleanup_errors.append(('reap',p.pid,repr(error)))
        listener.close()
        try:
            server.terminate()
            try:server.wait(timeout=5)
            except subprocess.TimeoutExpired:server.kill();server.wait(timeout=5)
        except Exception as error:cleanup_errors.append(('server-reap',server.pid,repr(error)))
        server_log.close()
        for log in logs:log.close()
        report['cleanup_errors']=cleanup_errors
        report.update(server=server_result,controller_exit_codes=[p.returncode for p in processes],elapsed_seconds=time.monotonic()-started)
        report['log_sha256']={str(p.relative_to(ROOT)):digest(p) for p in output.glob('*.log')}
        text=json.dumps(report,indent=2)+'\n';(output/'report.json').write_text(text)
        (ROOT/'benchmarks/results/tls-native-application-lifecycle.json').write_text(text)
        print(json.dumps({k:report[k] for k in ['passed','elapsed_seconds','controller_exit_codes','server']},indent=2),flush=True)
    if not report['passed']:raise SystemExit('native application lifecycle failed: '+str(output))
if __name__=='__main__':main()
