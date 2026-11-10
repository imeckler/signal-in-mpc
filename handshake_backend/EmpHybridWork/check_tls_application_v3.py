#!/usr/bin/env python3
"""TLS application lifecycle on the two-party worker against a real OpenSSL server.

Two unchanged Lean application controllers (NativeApplicationFixture), each with
its own worker. After the in-engine handshake: three private application
payloads are sealed and sent (neither party knows them: XOR of both parties'
randomness, produced by the worker's TEST-ONLY producer), OpenSSL echoes each
one, and the workers check inside the engines that every echo equals the private
payload that was sent. Also exercised: client KeyUpdate, server-requested
KeyUpdate and the automatic response, key rotation in both directions, rejection
of a replayed authenticated record, terminal abort.

Usage: check_tls_application_v3.py [malicious|semi-honest] [PAYLOAD_BYTES]
"""
import hashlib,json,os,pathlib,re,secrets,socket,subprocess,sys,threading,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;BASE=ROOT/'.deps/two-party-comparison'
sys.path.insert(0,str(ROOT/'scripts'))
from check_full_handshake import certificates,OPENSSL
def bridge(listener,server,result):
    def command(text):
        server.stdin.write(text+'\n');server.stdin.flush()
        status,value=server.stdout.readline().strip().split(' ',1)
        if status not in ('ready','waiting'):raise ValueError('OpenSSL fixture response')
        return status,bytes.fromhex(value) if value!='-' else b''
    try:
        with listener:connection,_=listener.accept()
        with connection:
            connection.settimeout(3600)
            def exact(n):
                out=bytearray()
                while len(out)<n:
                    data=connection.recv(n-len(out))
                    if not data:raise EOFError('client transport closed')
                    out.extend(data)
                return bytes(out)
            ready=False
            while True:
                try:header=exact(5)
                except EOFError:
                    if result.get('replay_sent'):break
                    raise
                status,wire=command((header+exact(int.from_bytes(header[3:5],'big'))).hex())
                if not ready:
                    if status=='ready':ready=True;result['client_finished_accepted']=True
                    if wire:connection.sendall(wire)
                    continue
                if wire:
                    # The server writes only after SSL_read authenticated an application payload.
                    result['private_application_records']+=1;connection.sendall(wire)
                    if result['private_application_records']==1:
                        _,update=command('update-request')
                        if not update:raise ValueError('server update absent')
                        result['server_requested_update']=True;connection.sendall(update)
                    if result['private_application_records']==3:
                        _,replay=command('replay')
                        if replay!=wire:raise ValueError('replay fixture mismatch')
                        result['replay_sent']=True;connection.sendall(replay)
            result['closed_after_replay']=True
    except Exception as error:result['error']=str(error)
def main():
    mode=sys.argv[1] if len(sys.argv)>1 else 'malicious';size=int(sys.argv[2]) if len(sys.argv)>2 else 64
    if mode not in ('malicious','semi-honest') or not 1<=size<=4096:raise SystemExit('malicious|semi-honest [1..4096]')
    sh=mode=='semi-honest';port=21900 if sh else 21800;timeout=3600
    output=BASE/'tls-application-v3-run'/secrets.token_hex(8);output.mkdir(parents=True)
    subprocess.run(['lake','build','session_application_fixture','hybrid_kdf_emitter'],cwd=ROOT,check=True,capture_output=True)
    for name in ('public_auth','fixture_server'):
        subprocess.run(['c++','-std=c++20','-O2','-I'+str(OPENSSL/'include'),str(ROOT/f'handshake_backend/{name}.cpp'),'-L'+str(OPENSSL/'lib'),'-lssl','-lcrypto','-o',str(output/name)],check=True)
    MP=BASE/'data61-MP-SPDZ-113c4e4';work=output/'work';work.mkdir()
    with open(output/'ssl-setup.log','w') as log:subprocess.run(['bash',str(MP/'Scripts/setup-ssl.sh'),'2'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
    env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP),TLS_WORKER_TEST_PRODUCER=str(size))
    profiles,trust=certificates(output);cert,key=profiles['ed25519']
    hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*2);session=secrets.token_hex(32)
    listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen(1);listener.settimeout(timeout);server_port=listener.getsockname()[1]
    server_log=open(output/'server.log','w')
    server=subprocess.Popen([str(output/'fixture_server'),str(cert),str(key),'512','no','h2'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=server_log,text=True)
    server_result={'client_finished_accepted':False,'private_application_records':0}
    thread=threading.Thread(target=bridge,args=(listener,server,server_result),daemon=True);thread.start()
    worker=BASE/('tls-worker-sh-fixture-v3' if sh else 'tls-worker-fixture-v3');controller=ROOT/'.lake/build/bin/session_application_fixture'
    sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
    report=dict(passed=False,parties=2,security_mode=mode,payload_bytes=size,logs=str(output),test_only_private_producer=True,
        sha256={str(p.relative_to(ROOT)):sha(p) for p in (worker,controller,HERE/'tls_worker_v3.cpp',HERE/'tls_kernels.h',ROOT/'TlsMpc/HybridKdf.lean',ROOT/'TlsMpc/TlsApplication.lean',ROOT/'TlsMpc/TlsPostHandshake.lean')})
    processes,logs=[],[];started=time.monotonic()
    try:
        for party in range(2):
            log=open(output/f'party-{party}.log','w');logs.append(log)
            command=[str(controller),str(worker),str(work),str(party),str(hosts),str(port),str(HERE/'circuit_cache.py'),session,'127.0.0.1',str(server_port),'server.example',str(output/'public_auth'),str(trust),str(size)]
            processes.append(subprocess.Popen(command,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=log,text=True))
        cases=[]
        for party,p in enumerate(processes):
            stdout,_=p.communicate(timeout=max(1,timeout-(time.monotonic()-started)));(output/f'party-{party}.json').write_text(stdout)
            if p.returncode:raise RuntimeError(f'controller {party} failed; see its log')
            cases.append(json.loads(stdout))
        thread.join(timeout=10)
        texts=[(output/f'party-{party}.log').read_text() for party in range(2)]
        echoes=[t.count('test echo matches private payload') for t in texts]
        report.update(controllers=cases,echoes_matched_inside_engines=echoes)
        if not all(c['passed'] for c in cases):raise RuntimeError('controller lifecycle failed')
        if echoes!=[3,3]:raise RuntimeError('echo equality was not established three times by both workers')
        if thread.is_alive() or 'error' in server_result or server_result['private_application_records']!=3 or not server_result.get('server_requested_update') or not server_result.get('replay_sent'):raise RuntimeError('server side of the lifecycle incomplete')
        report['passed']=True
    except Exception as error:report['error']=str(error)
    finally:
        for p in processes:
            if p.poll() is None:p.terminate()
        for p in processes:p.wait()
        listener.close()
        if server.poll() is None:server.kill()
        server.wait()
        for log in logs:log.close()
        server_log.close()
        totals=[]
        for party in range(2):
            text=(output/f'party-{party}.log').read_text();rows=[]
            for m in re.finditer(r'operation (\d+) ok seconds=([\d.e+-]+) and_gates=(\d+) emp_sent_bytes=(\d+) field_sent_bytes=(\d+) field_products=(\d+)',text):
                rows.append(dict(operation=int(m[1]),seconds=float(m[2]),and_gates=int(m[3]),emp_sent_bytes=int(m[4]),field_sent_bytes=int(m[5]),field_products=int(m[6])))
            totals.append(rows[-1] if rows else None);report.setdefault('operations',[]).append(rows)
            report.setdefault('rejections',[]).extend(re.findall(r'operation \d+ rejected[^\n]*',text))
        report.update(server=server_result,elapsed_seconds=time.monotonic()-started,worker_totals=totals,controller_exit_codes=[p.returncode for p in processes])
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');(HERE/('tls-application-sh-report.json' if sh else 'tls-application-v3-report.json')).write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:report.get(k) for k in ('passed','security_mode','payload_bytes','elapsed_seconds','echoes_matched_inside_engines','controllers','worker_totals','rejections','server','error')}),flush=True)
    if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
