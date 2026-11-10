#!/usr/bin/env python3
"""Two Lean TLS controllers, each with a v3 two-party worker, against a real
OpenSSL TLS 1.3 server.

The X25519 key exchange, the key schedule, handshake record opening, Finished
verification and the sealed client Finished all run inside the two engines
(validated-v3 Boolean, native field) at statistical security 128. The harness
holds no client secret; it bridges public ciphertext to an OpenSSL memory-BIO
server and passes when OpenSSL accepts the client Finished and both controllers
report an authenticated session. Disposable local certificates only.
"""
import hashlib,json,os,pathlib,re,secrets,signal,socket,subprocess,sys,threading,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;BASE=ROOT/'.deps/two-party-comparison'
sys.path.insert(0,str(ROOT/'scripts'))
from check_full_handshake import certificates,OPENSSL
def serve(listener,server,result):
    try:
        with listener:connection,_=listener.accept()
        with connection:
            connection.settimeout(3600)
            def exact(size):
                out=bytearray()
                while len(out)<size:
                    chunk=connection.recv(size-len(out))
                    if not chunk:raise EOFError('client closed before server accepted Finished')
                    out.extend(chunk)
                return bytes(out)
            while True:
                header=exact(5);record=header+exact(int.from_bytes(header[3:5],'big'))
                server.stdin.write(record.hex()+'\n');server.stdin.flush()
                status,text=server.stdout.readline().strip().split(' ',1)
                if status not in ('ready','waiting'):raise ValueError('invalid OpenSSL fixture response')
                wire=bytes.fromhex(text) if text!='-' else b'';offset=0
                while offset<len(wire):
                    length=5+int.from_bytes(wire[offset+3:offset+5],'big');result['outgoing_records'].append({'type':wire[offset],'wire_bytes':length});offset+=length
                if status=='ready':result['client_finished_accepted']=True;break
                connection.sendall(wire)
    except Exception as error:result['error']=str(error)
def main():
    # Mode is explicit: "malicious" (default) or "semi-honest" (separate binary and report).
    mode=sys.argv[1] if len(sys.argv)>1 else 'malicious'
    if mode not in ('malicious','semi-honest'):raise SystemExit('malicious|semi-honest')
    # Case "untrusted": the controllers are given a different CA; they must reject
    # the server and no client Finished may be produced.
    case=sys.argv[2] if len(sys.argv)>2 else 'ok'
    if case not in ('ok','untrusted'):raise SystemExit('ok|untrusted')
    sh=mode=='semi-honest';port=(21700 if sh else 21500)+(40 if case=='untrusted' else 0);timeout=3600
    output=BASE/'tls-worker-v3-run'/secrets.token_hex(8);output.mkdir(parents=True)
    subprocess.run(['lake','build','session_handshake_fixture','hybrid_kdf_emitter'],cwd=ROOT,check=True,capture_output=True)
    MP=BASE/'data61-MP-SPDZ-113c4e4';work=output/'work';work.mkdir()
    with open(output/'ssl-setup.log','w') as log:subprocess.run(['bash',str(MP/'Scripts/setup-ssl.sh'),'2'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
    # Key agreement route: "split" (default) or "ladder" (shared-scalar Montgomery ladder).
    route=sys.argv[3] if len(sys.argv)>3 else 'split'
    if route not in ('split','ladder'):raise SystemExit('split|ladder')
    env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP),TLS_WORKER_KEY_AGREEMENT=route)
    for name in ('public_auth','fixture_server'):
        subprocess.run(['c++','-std=c++20','-O2','-I'+str(OPENSSL/'include'),str(ROOT/f'handshake_backend/{name}.cpp'),'-L'+str(OPENSSL/'lib'),'-lssl','-lcrypto','-o',str(output/name)],check=True)
    profiles,trust=certificates(output);cert,key=profiles['ed25519']
    if case=='untrusted':(output/'other').mkdir();_,trust=certificates(output/'other')
    hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*2);session=secrets.token_hex(32)
    listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen(1);listener.settimeout(timeout);server_port=listener.getsockname()[1]
    server_log=open(output/'server.log','w')
    server=subprocess.Popen([str(output/'fixture_server'),str(cert),str(key),'512','no','h2'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=server_log,text=True)
    server_result={'client_finished_accepted':False,'outgoing_records':[]}
    bridge=threading.Thread(target=serve,args=(listener,server,server_result),daemon=True);bridge.start()
    worker=BASE/('tls-worker-sh-fixture-v3' if sh else 'tls-worker-fixture-v3');controller=ROOT/'.lake/build/bin/session_handshake_fixture'
    sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
    report=dict(passed=False,parties=2,security_mode=mode,
        engine='half-gates garbling + semi-honest field shares (no protection against deviation)' if sh else 'validated-v3 + native field (MASCOT)',
        statistical_security=None if sh else 128,logs=str(output),
        sha256={str(p.relative_to(ROOT)):sha(p) for p in (worker,controller,HERE/'tls_worker_v3.cpp',HERE/'tls_kernels.h',HERE/'dyn_word_mask.h',HERE/'circuit_cache.py',ROOT/'TlsMpc/HybridKdf.lean',ROOT/'TlsMpc/TlsClient.lean')})
    processes,logs=[],[];started=time.monotonic()
    try:
        for party in range(2):
            log=open(output/f'party-{party}.log','w');logs.append(log)
            command=[str(controller),str(worker),str(work),str(party),str(hosts),str(port),str(HERE/'circuit_cache.py'),session,'127.0.0.1',str(server_port),'server.example',str(output/'public_auth'),str(trust)]
            processes.append(subprocess.Popen(command,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=log,text=True))
        cases=[];codes=[]
        for party,p in enumerate(processes):
            stdout,_=p.communicate(timeout=max(1,timeout-(time.monotonic()-started)));(output/f'party-{party}.json').write_text(stdout);codes.append(p.returncode)
            if stdout.strip():cases.append(json.loads(stdout.strip().splitlines()[0]))
        report.update(case=case,key_agreement=route,controllers=cases)
        if case=='untrusted':
            texts=[(output/f'party-{party}.log').read_text() for party in range(2)]
            if not all(codes) or len(cases)!=2 or any(c['certificate_verified'] or c['application_session_accepted'] or c['client_finished_sent'] for c in cases):raise RuntimeError('untrusted server was not rejected by both controllers')
            if any(re.search(r'operation (4|5|6) ok',t) for t in texts) or server_result['client_finished_accepted']:raise RuntimeError('work continued past failed authentication')
            report['passed']=True
        else:
            if any(codes):raise RuntimeError('a controller failed; see its log')
            if len(cases)!=2 or not all(c['passed'] for c in cases):raise RuntimeError('controller did not reach the authenticated boundary')
            bridge.join(timeout=10)
            if bridge.is_alive() or not server_result['client_finished_accepted'] or 'error' in server_result:raise RuntimeError('OpenSSL server did not accept client Finished')
            report['passed']=True
    except Exception as error:report['error']=str(error)
    finally:
        for p in processes:
            if p.poll() is None:p.terminate()   # the controller stops its own worker
        for p in processes:p.wait()
        listener.close()
        if server.poll() is None:server.kill()
        server.wait()
        for log in logs:log.close()
        server_log.close()
        totals=[]
        for party in range(2):
            # Cumulative public counters after each operation (operation 0 = setup and mask batch).
            text=(output/f'party-{party}.log').read_text();rows=[]
            for m in re.finditer(r'operation (\d+) ok seconds=([\d.e+-]+) and_gates=(\d+) emp_sent_bytes=(\d+) field_sent_bytes=(\d+) field_products=(\d+)',text):
                rows.append(dict(operation=int(m[1]),seconds=float(m[2]),and_gates=int(m[3]),emp_sent_bytes=int(m[4]),field_sent_bytes=int(m[5]),field_products=int(m[6])))
            totals.append(rows[-1] if rows else None);report.setdefault('operations',[]).append(rows)
            report.setdefault('rejections',[]).extend(re.findall(r'operation \d+ rejected[^\n]*',text))
        report.update(server=server_result,elapsed_seconds=time.monotonic()-started,worker_totals=totals,controller_exit_codes=[p.returncode for p in processes])
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');(HERE/(('tls-worker-sh' if sh else 'tls-worker-v3')+('-untrusted' if case=='untrusted' else '')+('-ladder' if route=='ladder' else '')+'-report.json')).write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:report.get(k) for k in ('passed','security_mode','case','elapsed_seconds','worker_totals','rejections','error')}),flush=True)
    if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
