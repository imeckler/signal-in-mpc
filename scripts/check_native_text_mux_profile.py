#!/usr/bin/env python3
"""Normal lifecycle/provider profile, tested with a separately linked disposable adapter."""
import argparse
from datetime import datetime,timezone
import hashlib,json,os,secrets,signal,socket,subprocess,threading,time,shutil,re,resource
from pathlib import Path
from check_full_handshake import certificates,OPENSSL
from pin_tls_worker import build
from prepare_tls_shape import install,Shape
ROOT=Path(__file__).resolve().parents[1]

def digest(p):
    result=hashlib.sha256()
    with p.open('rb') as source:
        for chunk in iter(lambda:source.read(1024*1024),b''):result.update(chunk)
    return result.hexdigest()

def provision(backend,service_manifest=None):
    from check_native_provider_profile import provision as base_provision
    text=base_provision(backend)
    functions=[Path(line.split(' ',1)[1]).name for line in text.splitlines()[1:] if line.split(' ',1)[1].startswith('Programs/Functions/')]
    public_files=[line.split(' ',1)[1] for line in text.splitlines()[1:] if line.split(' ',1)[1].startswith('Worker-Public/')]
    extras=[ROOT/'.deps/tls-websocket-upgrade-native'/name for name in ['mux-byte.manifest','mux-admit.manifest','request-id-seed.manifest','request-id-next.manifest']]
    historical=ROOT/'.deps/private-variable-conversation-native/260-80-0-0/service.manifest'
    selected=service_manifest or historical
    extras += [ROOT/'.deps/private-text-notification-native/text.manifest',selected]
    old_products={name:value for value,name in (line.split(' ',1)for line in historical.read_text().splitlines()[1:])}
    for manifest in extras:
        for line in manifest.read_text().splitlines()[1:]:
            value,name=line.split(' ',1);source=manifest.parent/name;assert digest(source)==value
            target=backend/name;target.parent.mkdir(parents=True,exist_ok=True)
            if target.exists() and digest(target)!=value:
                # Replace only the exact historical service descriptor in a
                # cloned public cache; unknown/mutable products fail closed.
                assert manifest==selected and service_manifest is not None and name.startswith('Programs/Functions/') and old_products.get(name)==digest(target),('public closure collision',name)
                shutil.copy2(source,target)
            elif not target.exists():shutil.copy2(source,target)
            if name.startswith('Programs/Functions/'):functions.append(Path(name).name)
            if name.startswith('Worker-Public/'):public_files.append(name)
    for capacity in [1290]:
        shape=Shape(('tls-seal-private-record',capacity))
        subprocess.run([str(backend/'Worker-Public/tls-shape-compiler'),*shape.arguments],cwd=backend,check=True)
        functions.append(shape.descriptor)
    return build(backend,sorted(set(functions)),sorted(set(public_files)))

def bridge(listener,server,result):
    try:
        with listener: connection,_=listener.accept()
        with connection:
            connection.settimeout(3600)
            def exact(n):
                out=bytearray()
                while len(out)<n:
                    data=connection.recv(n-len(out))
                    if not data:raise EOFError()
                    out.extend(data)
                return bytes(out)
            while True:
                try:header=exact(5)
                except EOFError:break
                size=int.from_bytes(header[3:5],'big');assert size<=16640
                result['external_tls_received_bytes']=result.get('external_tls_received_bytes',0)+5+size
                server.stdin.write((header+exact(size)).hex()+'\n');server.stdin.flush()
                line=server.stdout.readline().strip()
                if not line:raise RuntimeError('local endpoint terminated')
                status,wire=line.split(' ',1)
                assert status in ('ready','waiting')
                if status=='ready':result['client_finished_accepted']=True
                if wire!='-':
                    response=bytes.fromhex(wire);result['external_tls_sent_bytes']=result.get('external_tls_sent_bytes',0)+len(response);connection.sendall(response)
            server.stdin.write('quit\n');server.stdin.flush();server.stdin.close()
            assert server.wait(timeout=30)==0
            result['clean_endpoint_completion']=True
    except Exception as error:result['error']=repr(error)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--timeout',type=int,default=3600);ap.add_argument('--port',type=int,default=20300);ap.add_argument('--public-cache',type=Path)
    ap.add_argument('--service-manifest',type=Path);ap.add_argument('--runtime-root',type=Path);ap.add_argument('--result-name',default='tls-native-text-mux-profile');ap.add_argument('--execution',choices=['sequential','batch'],default='sequential');ap.add_argument('--rounds',type=int,choices=[2,4],default=2)
    args=ap.parse_args();runtime=(args.runtime_root or ROOT/'.deps/tls-session-runtime/MP-SPDZ').resolve()
    if not re.fullmatch(r'[a-z0-9-]+',args.result_name):raise ValueError('invalid result name')
    if args.service_manifest:args.service_manifest=args.service_manifest.resolve()
    if args.execution=='batch' and not args.service_manifest:raise ValueError('batch execution requires explicit pinned closure')
    if args.rounds==4 and (args.result_name=='tls-native-text-mux-profile' or runtime!=(ROOT/'.deps/tls-backend-diagnostic-runtime-v4/MP-SPDZ').resolve()):raise ValueError('extended throughput profile requires unique result name and diagnosticv4 runtime')
    worker_name='tls-text-throughput-fixture-worker'if args.rounds==4 else'tls-text-mux-fixture-worker'
    makefile=ROOT/'handshake_backend/BatchThroughputWork/Makefile'if args.rounds==4 else ROOT/'handshake_backend/WebSocketWork/Makefile'
    if not hasattr(time,'CLOCK_MONOTONIC_RAW'):raise RuntimeError('suspend-aware CLOCK_MONOTONIC_RAW required')
    clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
    output=ROOT/'benchmarks/results/raw'/args.result_name/secrets.token_hex(8);output.mkdir(parents=True)
    print('integration output '+str(output),flush=True)
    phases=[]
    def logged(command,name,cwd=ROOT):
        started=clock()
        with (output/name).open('wb') as log:
            child=subprocess.Popen(command,cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
            print('public phase '+name+' pid='+str(child.pid),flush=True)
            try:code=child.wait(timeout=args.timeout)
            except BaseException:
                child.kill();child.wait();raise
        phases.append({'phase':name,'pid':child.pid,'exit_code':code,'elapsed_seconds':clock()-started,'children_rusage_maxrss':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss})
        if code:raise subprocess.CalledProcessError(code,command)
    logged(['make','-f',str(makefile),'TLS_ROOT='+str(ROOT/'handshake_backend'),'../'+worker_name],'worker-build.log',runtime)
    logged(['lake','env','lean',str(ROOT/'handshake_backend/WebSocketWork/MuxProviderController.lean')],'controller-check.log')
    backend=output/'working';backend.mkdir()
    if args.public_cache:
        # Copy only explicitly public compiler/program material. PlayerData and
        # runtime state/peer secrets from the old execution are never reused.
        from check_native_websocket_service import clone_public_cache
        clone_public_cache(args.public_cache,backend)
    manifest=output/'programs.manifest';manifest.write_text(provision(backend,args.service_manifest))
    # Diagnostic overlays retain libSPDZ.so's relative install ID. Select the
    # exact measured library explicitly in the child's working directory.
    library=backend/'libSPDZ.so'
    if not library.exists():library.symlink_to(runtime/'libSPDZ.so')
    assert library.resolve()==(runtime/'libSPDZ.so').resolve()
    for name in ['websocket-initial-state.bin','tls-websocket-frame-v2-4096-initial.bin','websocket-control-initial.bin','tls-chat-response-4096-initial.bin','chat-mux-initial.bin']:
        assert ' Worker-Public/'+name+'\n' in manifest.read_text(),('missing parser state pin',name)
    baseline=ROOT/'.deps/sharing-refresh/MP-SPDZ';canonical=digest(baseline/'libSPDZ.so')
    logged(['bash',str(baseline/'Scripts/setup-ssl.sh'),'5'],'peer-certificates.log',backend)
    logged(['c++','-std=c++20','-O2','-I'+str(OPENSSL/'include'),str(ROOT/'handshake_backend/public_auth.cpp'),'-L'+str(OPENSSL/'lib'),'-lssl','-lcrypto','-o',str(output/'public_auth')],'auth-build.log')
    profiles,trust=certificates(output);cert,key=profiles['ed25519'];hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*5)
    names=[Path(__file__),*sorted((ROOT/'handshake_backend').glob('*.h')),
      *sorted((ROOT/'handshake_backend/SessionWork').glob('*.h')),
      *sorted((ROOT/'handshake_backend/WebSocketWork').glob('*.h')),
      *sorted((ROOT/'handshake_backend/WebSocketWork').glob('*.lean')),
      *sorted((ROOT/'signal_backend/VariableServiceWork').glob('*.h')),
      *sorted((ROOT/'signal_backend/TextNotificationWork').glob('*.h')),ROOT/'signal_backend/TextNotificationWork/fixture_server.py',ROOT/'signal_backend/TextNotificationWork/server-fixtures.json',
      ROOT/'handshake_backend/WebSocketWork/mux_worker_main.cpp',ROOT/'handshake_backend/WebSocketWork/TextMuxFixtureFactory.cpp',ROOT/'handshake_backend/WebSocketWork/NoMuxProvider.cpp',ROOT/'handshake_backend/WebSocketWork/Makefile',
      runtime/'libSPDZ.so',runtime.parent/worker_name,manifest]
    names += [ROOT/n for n in ['TlsMpc/TlsWorker.lean','TlsMpc/TlsWorkerPipe.lean','TlsMpc/TlsApplication.lean','TlsMpc/TlsClient.lean',
      'TlsMpc/TlsChatResponseMux.lean','TlsMpc/TlsPrivateRequestId.lean','TlsMpc/TlsProviderGate.lean','TlsMpc/TlsChatResponse.lean','TlsMpc/TlsWebSocketFrame.lean','TlsMpc/TlsWebSocketControl.lean','TlsMpc/TlsWebSocketIdle.lean']]
    names += [ROOT/'scripts/check_native_websocket_service.py',ROOT/'signal_backend/VariableServiceWork/PrivateProvider.h',ROOT/'handshake_backend/WebSocketWork/prepare_provider_gate.py']
    if args.rounds==4:names += [ROOT/'handshake_backend/BatchThroughputWork/TextExtendedMuxFixtureFactory.cpp',ROOT/'handshake_backend/BatchThroughputWork/NativeBatchService.h',ROOT/'handshake_backend/BatchThroughputWork/Makefile',ROOT/'.deps/signal-established-send-oracle-target/debug/signal-text-recipient-extended-oracle']
    hashes={str(p.relative_to(ROOT)):digest(p) for p in names}
    for source in names:
        if source.suffix in ('.h','.cpp','.lean','.py') or source.name=='Makefile':
            target=output/'source-snapshot'/source.relative_to(ROOT);target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
    shutil.copy2(runtime.parent/worker_name,output/'worker-snapshot')
    listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen(1);listener.settimeout(args.timeout);port=listener.getsockname()[1]
    server_log=(output/'server.log').open('w');server=subprocess.Popen([os.sys.executable,str(ROOT/'signal_backend/TextNotificationWork/fixture_server.py'),str(cert),str(key),'127','no','http/1.1','--report',str(output/'endpoint.json'),'--rounds',str(args.rounds)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=server_log,text=True)
    server_result={};thread=threading.Thread(target=bridge,args=(listener,server,server_result),daemon=True);thread.start()
    processes=[];logs=[];cleanup=[];started=clock();session=secrets.token_hex(32)
    report={'passed':False,'producer_execution':args.execution,'rounds_per_conversation':args.rounds,'messages':2*args.rounds,'timing_clock':'CLOCK_MONOTONIC_RAW (suspend-aware on macOS)','public_setup_phases':phases,'runtime_root':str(runtime.relative_to(ROOT)),'service_manifest':str(args.service_manifest.relative_to(ROOT)) if args.service_manifest else None,'native_mpc_executed':False,'logs':str(output.relative_to(ROOT)),'source_and_product_sha256':hashes,
      'scope':'normal lifecycle worker/controller with embedding-only opaque provider/input registry; separately linked disposable adapter and local endpoint test; four opaque pending slots, one pending per conversation; two distinct conversations/nonempty text fixture messages',
      'authenticated_bootstrap_supplied':False,'fixture_material_in_normal_core':False,'no_default_provider':True,
      'canonical_runtime_sha256':canonical,'canonical_application_gate_opened':False,'sharing_refresh_resumed':False,'full_system_complete':False}
    try:
        for party in range(5):
            log=(output/f'party-{party}.log').open('w');logs.append(log)
            command=['lake','env','lean','--run',str(ROOT/'handshake_backend/WebSocketWork/MuxProviderController.lean'),str(runtime.parent/worker_name),str(backend),str(party),str(hosts),str(args.port),str(manifest),session,'127.0.0.1',str(port),'server.example',str(output/'public_auth'),str(trust),'0',args.execution]
            processes.append(subprocess.Popen(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True))
            report['native_mpc_executed']=True
            print('public controller party='+str(party)+' pid='+str(processes[-1].pid),flush=True)
        cases=[]
        for party,p in enumerate(processes):
            stdout,_=p.communicate(timeout=max(1,args.timeout-(clock()-started)));(output/f'party-{party}.json').write_text(stdout)
            assert p.returncode==0,('controller failed',party,p.returncode)
            case=json.loads(stdout);assert case['passed'];cases.append(case)
        thread.join(timeout=35);assert not thread.is_alive() and 'error' not in server_result,server_result
        endpoint=json.loads((output/'endpoint.json').read_text());assert endpoint['actual_session_texts_recovered']==2*args.rounds and endpoint['independent_conversations']==2 and endpoint['responses_reordered'] and endpoint['interleaved_pongs_validated']==1+2*args.rounds,endpoint
        assert all(digest(p)==hashes[str(p.relative_to(ROOT))] for p in names),'source/product changed'
        assert digest(baseline/'libSPDZ.so')==canonical,'canonical runtime changed'
        report.update(passed=True,native_mpc_executed=True,controllers=cases,endpoint=endpoint)
    except Exception as error:report['error']=repr(error)
    finally:
        for p in processes:
            if p.poll() is None:
                try:os.killpg(p.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                except PermissionError:
                    try:p.terminate()
                    except ProcessLookupError:pass
                    except Exception as error:cleanup.append(('terminate',p.pid,repr(error)))
                except Exception as error:cleanup.append(('killpg',p.pid,repr(error)))
        for p in processes:
            try:p.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:p.kill();p.wait(timeout=5)
                except Exception as error:cleanup.append(('reap',p.pid,repr(error)))
        listener.close()
        if server.poll() is None:
            try:server.terminate();server.wait(timeout=5)
            except subprocess.TimeoutExpired:server.kill();server.wait(timeout=5)
            except Exception as error:cleanup.append(('server',repr(error)))
        for log in logs:log.close()
        report['source_integrity_verified']=all(digest(p)==hashes[str(p.relative_to(ROOT))] for p in names)
        report['canonical_runtime_unchanged']=digest(baseline/'libSPDZ.so')==canonical
        server_log.close();report.update(cleanup_errors=cleanup,server=server_result,controller_exit_codes=[p.returncode for p in processes],elapsed_seconds=clock()-started)
        if cleanup:report['passed']=False
        report['children_rusage_maxrss']=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        report['controller_pids']=[p.pid for p in processes]
        report['log_sha256']={str(p.relative_to(ROOT)):digest(p) for p in output.glob('*.log')}
        text=json.dumps(report,indent=2)+'\n';(output/'report.json').write_text(text);(ROOT/'benchmarks/results'/(args.result_name+'.json')).write_text(text)
        print(json.dumps({k:report[k] for k in ['passed','elapsed_seconds','controller_exit_codes','server']},indent=2),flush=True)
    if not report['passed']:raise SystemExit('native WebSocket service failed: '+str(output))
if __name__=='__main__':main()
