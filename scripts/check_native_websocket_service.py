#!/usr/bin/env python3
"""Five-party local TLS/H1/WebSocket variable Signal service integration fixture."""
import argparse
from datetime import datetime,timezone
import hashlib,json,os,secrets,signal,socket,subprocess,threading,time,shutil,re
from pathlib import Path
from check_full_handshake import certificates,OPENSSL
from pin_tls_worker import build
from prepare_tls_shape import install,Shape
ROOT=Path(__file__).resolve().parents[1]

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def provision(backend):
    baseline=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    public_files=set()
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
    closures=[(ROOT/'.deps/private-variable-conversation-native/260-0-0-0','service.manifest'),
      (ROOT/'.deps/private-sealed-relay-native/260-72-1-5-13-1','upgrade.manifest')]
    ws=ROOT/'.deps/tls-websocket-upgrade-native'
    closures += [(ws,name) for name in ['upgrade.manifest','frame-v2-4096.manifest','frame-idle-v2-4096.manifest',
      'control-collect.manifest','control-encode.manifest','chat-4096.manifest']]
    for capacity in range(1,129):
        manifest=ws/f'activity-{capacity}.manifest'
        if not manifest.exists():
            subprocess.run([os.sys.executable,str(ROOT/'handshake_backend/WebSocketWork/prepare_activity.py'),str(capacity)],check=True)
        closures.append((ws,manifest.name))
    for source,name in closures:
        text=(source/name).read_text();copy_manifest(source,text)
        public_files.update(line.split(" ",1)[1] for line in text.splitlines()[1:] if line.split(" ",1)[1].startswith("Worker-Public/"))
        functions.extend(Path(line.split(' ',1)[1]).name for line in text.splitlines()[1:]
          if line.split(' ',1)[1].startswith('Programs/Functions/'))
    # Install the application-capable helper, not the historical handshake-only
    # helper in the canonical runtime. Keep its archived accepted TLS emitter.
    compiler_config=json.loads((baseline/'Worker-Public/tls-shape-toolchain.json').read_text())
    for name in compiler_config['files']:
        target=backend/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(baseline/name,target)
    emitter=ROOT/'.deps/sharing-refresh/tls-application-shapes-v2/Worker-Public/tls-shape-emitter'
    (backend/'Programs/Source').mkdir(parents=True,exist_ok=True)
    install(backend,emitter,ROOT/".lake/build/bin/private_tls_emitter")
    for arguments in [('tls-seal-record',23,345,0),('tls-seal-record',22,5,0),
                      ('tls-seal-private-record',1186),('tls-seal-private-record',131)]:
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
    return build(backend,functions,sorted(public_files|{'Worker-Public/tls-shape-compiler','Worker-Public/tls-shape-toolchain.json'}))

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
                server.stdin.write((header+exact(size)).hex()+'\n');server.stdin.flush()
                line=server.stdout.readline().strip()
                if not line:raise RuntimeError('local endpoint terminated')
                status,wire=line.split(' ',1)
                assert status in ('ready','waiting')
                if status=='ready':result['client_finished_accepted']=True
                if wire!='-':connection.sendall(bytes.fromhex(wire))
            server.stdin.write('quit\n');server.stdin.flush();server.stdin.close()
            assert server.wait(timeout=30)==0
            result['clean_endpoint_completion']=True
    except Exception as error:result['error']=repr(error)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--timeout',type=int,default=3600);ap.add_argument('--port',type=int,default=20300);ap.add_argument('--public-cache',type=Path)
    args=ap.parse_args();runtime=ROOT/'.deps/tls-session-runtime/MP-SPDZ'
    output=ROOT/'benchmarks/results/raw/native-websocket-service'/secrets.token_hex(8);output.mkdir(parents=True)
    print('integration output '+str(output),flush=True)
    def logged(command,name,cwd=ROOT):
        with (output/name).open('wb') as log:subprocess.run(command,cwd=cwd,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=args.timeout)
    logged(['make','-f',str(ROOT/'handshake_backend/WebSocketWork/Makefile'),'TLS_ROOT='+str(ROOT/'handshake_backend'),'../tls-websocket-worker'],'worker-build.log',runtime)
    logged(['lake','env','lean',str(ROOT/'handshake_backend/WebSocketWork/NativeServiceFixture.lean')],'controller-check.log')
    backend=output/'working';backend.mkdir()
    if args.public_cache:
        # Copy only explicitly public compiler/program material. PlayerData and
        # runtime state/peer secrets from the old execution are never reused.
        for name in ('Compiler','backend_adapter','handshake_backend','Worker-Public','Programs'):
            shutil.copytree(args.public_cache/name,backend/name)
        shutil.copy2(args.public_cache/'compile.py',backend/'compile.py')
    manifest=output/'programs.manifest';manifest.write_text(provision(backend))
    for name in ['websocket-initial-state.bin','tls-websocket-frame-v2-4096-initial.bin','websocket-control-initial.bin','tls-chat-response-4096-initial.bin']:
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
      ROOT/'signal_backend/VariableServiceWork/fixture_server.py',ROOT/'signal_backend/VariableServiceWork/server-fixture.json',
      ROOT/'handshake_backend/WebSocketWork/worker_main.cpp',ROOT/'handshake_backend/WebSocketWork/Makefile',
      runtime/'libSPDZ.so',runtime.parent/'tls-websocket-worker',manifest]
    names += [ROOT/n for n in ['TlsMpc/TlsWorker.lean','TlsMpc/TlsWorkerPipe.lean','TlsMpc/TlsApplication.lean','TlsMpc/TlsClient.lean',
      'TlsMpc/TlsChatResponse.lean','TlsMpc/TlsWebSocketFrame.lean','TlsMpc/TlsWebSocketControl.lean','TlsMpc/TlsWebSocketIdle.lean']]
    hashes={str(p.relative_to(ROOT)):digest(p) for p in names}
    for source in names:
        if source.suffix in ('.h','.cpp','.lean','.py') or source.name=='Makefile':
            target=output/'source-snapshot'/source.relative_to(ROOT);target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
    shutil.copy2(runtime.parent/'tls-websocket-worker',output/'worker-snapshot')
    listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen(1);listener.settimeout(args.timeout);port=listener.getsockname()[1]
    server_log=(output/'server.log').open('w');server=subprocess.Popen([os.sys.executable,str(ROOT/'signal_backend/VariableServiceWork/fixture_server.py'),str(cert),str(key),'127','no','http/1.1','--report',str(output/'endpoint.json')],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=server_log,text=True)
    server_result={};thread=threading.Thread(target=bridge,args=(listener,server,server_result),daemon=True);thread.start()
    processes=[];logs=[];cleanup=[];started=time.monotonic();session=secrets.token_hex(32)
    report={'passed':False,'native_mpc_executed':False,'logs':str(output.relative_to(ROOT)),'source_and_product_sha256':hashes,
      'scope':'disposable local protocol-faithful H1/WS service with private variable Signal producer; single pending response profile',
      'canonical_runtime_sha256':canonical,'canonical_application_gate_opened':False,'sharing_refresh_resumed':False,'full_system_complete':False}
    try:
        for party in range(5):
            log=(output/f'party-{party}.log').open('w');logs.append(log)
            command=['lake','env','lean','--run',str(ROOT/'handshake_backend/WebSocketWork/NativeServiceFixture.lean'),str(runtime.parent/'tls-websocket-worker'),str(backend),str(party),str(hosts),str(args.port),str(manifest),session,'127.0.0.1',str(port),'server.example',str(output/'public_auth'),str(trust),'0']
            processes.append(subprocess.Popen(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True))
            report['native_mpc_executed']=True
        cases=[]
        for party,p in enumerate(processes):
            stdout,_=p.communicate(timeout=max(1,args.timeout-(time.monotonic()-started)));(output/f'party-{party}.json').write_text(stdout)
            assert p.returncode==0,('controller failed',party,p.returncode)
            case=json.loads(stdout);assert case['passed'];cases.append(case)
        thread.join(timeout=35);assert not thread.is_alive() and 'error' not in server_result,server_result
        endpoint=json.loads((output/'endpoint.json').read_text());assert endpoint['requests_validated']==2 and endpoint['interleaved_pongs_validated']==3,endpoint
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
        server_log.close();report.update(cleanup_errors=cleanup,server=server_result,controller_exit_codes=[p.returncode for p in processes],elapsed_seconds=time.monotonic()-started)
        if cleanup:report['passed']=False
        report['log_sha256']={str(p.relative_to(ROOT)):digest(p) for p in output.glob('*.log')}
        text=json.dumps(report,indent=2)+'\n';(output/'report.json').write_text(text);(ROOT/'benchmarks/results/tls-native-websocket-service.json').write_text(text)
        print(json.dumps({k:report[k] for k in ['passed','elapsed_seconds','controller_exit_codes','server']},indent=2),flush=True)
    if not report['passed']:raise SystemExit('native WebSocket service failed: '+str(output))
if __name__=='__main__':main()
