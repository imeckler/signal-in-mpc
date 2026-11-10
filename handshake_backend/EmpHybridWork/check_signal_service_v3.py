#!/usr/bin/env python3
"""Signal service path on the two-party worker against the local fixture server.

Two unchanged Lean controllers (WebSocketWork/ProviderController), each with its
own worker. Inside the engines: TLS 1.3 handshake, authenticated WebSocket
upgrade with private credentials, four established sealed-sender text sends
(two conversations, two rounds, SPQR), private parsing of the 101 response,
frames, pings and the correlated 200 responses, masked pongs, KeyUpdate.

The server (signal_backend/TextNotificationWork/fixture_server.py) is ordinary
local TLS; it validates the upgrade credentials and each relay request, opens
the sealed-sender envelope with the pinned libsignal, and a retained libsignal
recipient session DECRYPTS every message and checks body and timestamp. Public
disposable fixtures only; no live service or account.

Usage: check_signal_service_v3.py [malicious|semi-honest]
"""
import hashlib,json,os,pathlib,re,secrets,socket,subprocess,sys,threading,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;BASE=ROOT/'.deps/two-party-comparison'
sys.path.insert(0,str(ROOT/'scripts'))
from check_full_handshake import certificates,OPENSSL
def bridge(listener,server,result):
    def command(text):
        server.stdin.write(text+'\n');server.stdin.flush()
        line=server.stdout.readline().strip()
        if not line:raise ValueError('fixture server stopped')
        status,value=line.split(' ',1)
        if status not in ('ready','waiting'):raise ValueError('fixture server response')
        return bytes.fromhex(value) if value!='-' else b''
    try:
        with listener:connection,_=listener.accept()
        with connection:
            connection.settimeout(7200)
            def exact(n):
                out=bytearray()
                while len(out)<n:
                    data=connection.recv(n-len(out))
                    if not data:raise EOFError
                    out.extend(data)
                return bytes(out)
            while True:
                try:header=exact(5)
                except EOFError:break
                wire=command((header+exact(int.from_bytes(header[3:5],'big'))).hex());result['client_records']+=1
                if wire:connection.sendall(wire)
    except Exception as error:result['error']=type(error).__name__+': '+str(error)
def main():
    mode=sys.argv[1] if len(sys.argv)>1 else 'malicious'
    if mode not in ('malicious','semi-honest'):raise SystemExit('malicious|semi-honest')
    sh=mode=='semi-honest';port=22100 if sh else 22000;timeout=7200
    output=BASE/'signal-service-v3-run'/secrets.token_hex(8);output.mkdir(parents=True)
    subprocess.run(['lake','build','provider_controller_fixture','hybrid_kdf_emitter'],cwd=ROOT,check=True,capture_output=True)
    subprocess.run(['c++','-std=c++20','-O2','-I'+str(OPENSSL/'include'),str(ROOT/'handshake_backend/public_auth.cpp'),'-L'+str(OPENSSL/'lib'),'-lssl','-lcrypto','-o',str(output/'public_auth')],check=True)
    MP=BASE/'data61-MP-SPDZ-113c4e4';work=output/'work';work.mkdir()
    with open(output/'ssl-setup.log','w') as log:subprocess.run(['bash',str(MP/'Scripts/setup-ssl.sh'),'2'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
    env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP),TLS_WORKER_SERVICE_FIXTURE='text')
    profiles,trust=certificates(output);cert,key=profiles['ed25519']
    hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*2);session=secrets.token_hex(32)
    listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen(1);listener.settimeout(timeout);server_port=listener.getsockname()[1]
    server_log=open(output/'server.log','w');server_report=output/'server-report.json'
    server=subprocess.Popen([sys.executable,str(ROOT/'signal_backend/TextNotificationWork/fixture_server.py'),str(cert),str(key),'127','no','http/1.1','--batch','1','--rounds','2','--report',str(server_report)],
        stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=server_log,text=True)
    bridged={'client_records':0}
    thread=threading.Thread(target=bridge,args=(listener,server,bridged),daemon=True);thread.start()
    worker=BASE/('tls-worker-sh-fixture-v3' if sh else 'tls-worker-fixture-v3');controller=ROOT/'.lake/build/bin/provider_controller_fixture'
    sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
    report=dict(passed=False,parties=2,security_mode=mode,logs=str(output),fixture_state_admission='public disposable test fixture, not authenticated provisioning',
        sha256={str(p.relative_to(ROOT)):sha(p) for p in (worker,controller,HERE/'tls_worker_v3.cpp',HERE/'tls_kernels.h',HERE/'service_kernels.h',HERE/'kernel.h',ROOT/'TlsMpc/HybridKernels.lean',ROOT/'TlsMpc/HybridService.lean')})
    processes,logs=[],[];started=time.monotonic()
    try:
        for party in range(2):
            log=open(output/f'party-{party}.log','w');logs.append(log)
            command=[str(controller),str(worker),str(work),str(party),str(hosts),str(port),str(HERE/'circuit_cache.py'),session,'127.0.0.1',str(server_port),'server.example',str(output/'public_auth'),str(trust),'0']
            processes.append(subprocess.Popen(command,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=log,text=True))
        cases=[]
        for party,p in enumerate(processes):
            stdout,_=p.communicate(timeout=max(1,timeout-(time.monotonic()-started)));(output/f'party-{party}.json').write_text(stdout)
            if stdout.strip():cases.append(json.loads(stdout.strip().splitlines()[0]))
        report['controllers']=cases
        if any(p.returncode for p in processes) or len(cases)!=2 or not all(c['passed'] for c in cases):raise RuntimeError('controller failed; see its log')
        thread.join(timeout=20)
        # The server asserts completion (four decrypted texts, all pongs) before writing its report.
        server.stdin.write('quit\n');server.stdin.flush();server.wait(timeout=60)
        if server.returncode!=0 or not server_report.exists():raise RuntimeError('fixture server did not confirm completion')
        report['server']=json.loads(server_report.read_text())
        if report['server'].get('actual_session_texts_recovered')!=4 or 'error' in bridged:raise RuntimeError('recipient did not recover four texts')
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
            report.setdefault('rejections',[]).extend(re.findall(r'operation \d+ rejected[^\n]*',text)+re.findall(r'tls-worker-v3 aborted[^\n]*',text))
        report.update(bridge=bridged,server_diagnostic=(output/'server.log').read_text()[-300:],elapsed_seconds=time.monotonic()-started,worker_totals=totals,controller_exit_codes=[p.returncode for p in processes])
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');(HERE/('signal-service-sh-report.json' if sh else 'signal-service-v3-report.json')).write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:report.get(k) for k in ('passed','security_mode','elapsed_seconds','controllers','server','worker_totals','rejections','bridge','server_diagnostic','error')}),flush=True)
    if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
