#!/usr/bin/env python3
"""Actual authorized restore + fresh TLS/WS runner. Never manufactures a cap.
Requires crypto-owned certified account state and linked real resolver already
provisioned in --working; this runner owns public endpoint/transport only.
"""
import argparse,hashlib,json,os,pathlib,secrets,signal,socket,subprocess,sys,threading,time
from datetime import datetime,timedelta,timezone
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'scripts'));from check_full_handshake import OPENSSL
from cryptography import x509
from cryptography.hazmat.primitives import hashes,serialization
from cryptography.hazmat.primitives.asymmetric import rsa,ed25519
from cryptography.x509.oid import NameOID,ExtendedKeyUsageOID
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def certs(directory):
 now=datetime.now(timezone.utc);ca_key=rsa.generate_private_key(public_exponent=65537,key_size=2048);ca_name=x509.Name([x509.NameAttribute(NameOID.COMMON_NAME,'Disposable restored TLS fixture CA')])
 ca=(x509.CertificateBuilder().subject_name(ca_name).issuer_name(ca_name).public_key(ca_key.public_key()).serial_number(x509.random_serial_number()).not_valid_before(now-timedelta(days=1)).not_valid_after(now+timedelta(days=2)).add_extension(x509.BasicConstraints(ca=True,path_length=0),True).sign(ca_key,hashes.SHA256()))
 key=ed25519.Ed25519PrivateKey.generate();leaf=(x509.CertificateBuilder().subject_name(x509.Name([x509.NameAttribute(NameOID.COMMON_NAME,'chat.signal.org')])).issuer_name(ca_name).public_key(key.public_key()).serial_number(x509.random_serial_number()).not_valid_before(now-timedelta(hours=1)).not_valid_after(now+timedelta(days=1)).add_extension(x509.BasicConstraints(ca=False,path_length=None),True).add_extension(x509.SubjectAlternativeName([x509.DNSName('chat.signal.org')]),False).add_extension(x509.ExtendedKeyUsage([ExtendedKeyUsageOID.SERVER_AUTH]),False).sign(ca_key,hashes.SHA256()))
 cert=directory/'server.pem';private=directory/'server.key';trust=directory/'ca.pem';cert.write_bytes(leaf.public_bytes(serialization.Encoding.PEM));trust.write_bytes(ca.public_bytes(serialization.Encoding.PEM));private.write_bytes(key.private_bytes(serialization.Encoding.PEM,serialization.PrivateFormat.PKCS8,serialization.NoEncryption()));private.chmod(0o600);return cert,private,trust
def bridge(listener,server,result,timeout,stop):
 try:
  with listener:
   listener.settimeout(1)
   while True:
    try:connection,_=listener.accept();break
    except socket.timeout:
     if stop.is_set():raise EOFError
  with connection:
   connection.settimeout(1)
   def exact(n):
    data=b''
    while len(data)<n:
     try:part=connection.recv(n-len(data))
     except socket.timeout:
      if stop.is_set():raise EOFError
      continue
     if not part:raise EOFError
     data+=part
    return data
   while True:
    try:header=exact(5)
    except EOFError:break
    size=int.from_bytes(header[3:5],'big');assert size<=16640;payload=exact(size)
    result['external_received_bytes']=result.get('external_received_bytes',0)+5+size
    server.stdin.write((header+payload).hex()+'\n');server.stdin.flush();line=server.stdout.readline().strip();assert line
    ready,wire=line.split(' ',1);assert ready in['ready','waiting']
    if wire!='-':
     response=bytes.fromhex(wire);result['external_sent_bytes']=result.get('external_sent_bytes',0)+len(response);connection.sendall(response)
   server.stdin.write('quit\n');server.stdin.flush();server.stdin.close();assert server.wait(timeout=30)==0;result['completed']=True
 except Exception:result['error']='endpoint-transport-failure'
def main():
 p=argparse.ArgumentParser();p.add_argument('--working',type=pathlib.Path,required=True);p.add_argument('--worker',type=pathlib.Path,required=True);p.add_argument('--runtime',type=pathlib.Path,required=True);p.add_argument('--fixture',type=pathlib.Path,required=True);p.add_argument('--expected-manifest-sha256',required=True);p.add_argument('--factory-source',type=pathlib.Path,required=True);p.add_argument('--archive-root',type=pathlib.Path,required=True);p.add_argument('--port',type=int,default=30900);p.add_argument('--timeout',type=int,default=1800);args=p.parse_args()
 for name in ['working','worker','runtime','fixture','factory_source','archive_root']:setattr(args,name,getattr(args,name).resolve())
 manifest=args.working/'programs.manifest';assert sha(manifest)==args.expected_manifest_sha256;assert(args.working/'Player-Data').is_dir();assert args.worker.is_file()and args.factory_source.is_file()and args.archive_root.is_dir()
 runtime=args.runtime/'libSPDZ.so';assert runtime.is_file()
 # Public immutable closures only; no account archives/journal/key contents read.
 pins={str(manifest):sha(manifest),str(runtime):sha(runtime),str(args.worker):sha(args.worker),str(args.fixture):sha(args.fixture),str(args.factory_source):sha(args.factory_source)}
 for line in manifest.read_text().splitlines()[1:]:
  digest,name=line.split(' ',1);file=args.working/name;assert sha(file)==digest;pins[str(file)]=digest
 sources=[pathlib.Path(__file__),HERE/'RestoredProviderController.lean',HERE/'fixture_server.py',ROOT/'handshake_backend/WebSocketWork/mux_worker_main.cpp',*sorted((ROOT/'handshake_backend').glob('*.h')),*sorted((ROOT/'handshake_backend/RestoreAdmissionWork').glob('*.h')),*sorted((ROOT/'handshake_backend/WebSocketWork').glob('*.h')),*sorted((ROOT/'signal_backend/RecoveryWork').glob('*.h'))]
 for file in sources:pins[str(file)]=sha(file)
 output=ROOT/'benchmarks/results/raw/tls-authorized-account-restore'/secrets.token_hex(8);output.mkdir(parents=True);cert,key,trust=certs(output);auth=output/'public_auth'
 with(output/'auth-build.log').open('w')as log:subprocess.run(['c++','-std=c++20','-O2','-I'+str(OPENSSL/'include'),str(ROOT/'handshake_backend/public_auth.cpp'),'-L'+str(OPENSSL/'lib'),'-lssl','-lcrypto','-o',str(auth)],stdout=log,stderr=subprocess.STDOUT,check=True)
 hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*5);session=secrets.token_hex(32)
 listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen(1);listener.settimeout(args.timeout);endpoint_port=listener.getsockname()[1]
 serverlog=(output/'server.log').open('w');server=subprocess.Popen([sys.executable,str(HERE/'fixture_server.py'),str(cert),str(key),'127','no','http/1.1','--fixture',str(args.fixture),'--report',str(output/'endpoint.json')],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=serverlog,text=True)
 endpoint={};stop=threading.Event();thread=threading.Thread(target=bridge,args=(listener,server,endpoint,args.timeout,stop),daemon=True);thread.start();processes=[];logs=[];cleanup=[];error=None;results=[];started=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
 report={'passed':False,'native_mpc_executed':False,'production_gate_enabled':False,'full_system_complete':False,'scope':'Actual linked authorized account engine + freshTLS/HTTP101 + retained-outbox remask/replay + nextproducer + actualrecipient; no capability manufactured by runner. Positive claims require all controller/endpoint/integrity/cleanup checks below.','manifest_sha256':args.expected_manifest_sha256,'source_product_sha256':pins,'logs':str(output.relative_to(ROOT))}
 try:
  for party in range(5):
   log=(output/f'party-{party}.log').open('w');logs.append(log)
   command=['lake','env','lean','--run',str(HERE/'RestoredProviderController.lean'),str(args.worker),str(args.working),str(party),str(hosts),str(args.port),str(manifest),session,'127.0.0.1',str(endpoint_port),'chat.signal.org',str(auth),str(trust),'0','sequential']
   processes.append(subprocess.Popen(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True,env=dict(os.environ,DYLD_LIBRARY_PATH=str(args.runtime),TLS_ACCOUNT_ARCHIVE_ROOT=str(args.archive_root))));print('restored controller party='+str(party)+' pid='+str(processes[-1].pid),flush=True)
  deadline=time.monotonic()+args.timeout
  for party,child in enumerate(processes):
   out,_=child.communicate(timeout=max(.1,deadline-time.monotonic()));(output/f'party-{party}.json-output').write_text(out);assert child.returncode==0
   item=json.loads(out.splitlines()[-1]);assert item['passed']and item['certificate_verified']and item['authenticated_server_responses']and item['outbox_resume']and item['recipient_delivery_claimed']is False;results.append(item)
  thread.join(timeout=35);assert not thread.is_alive()and endpoint.get('completed')and'error'not in endpoint
  peer=json.loads((output/'endpoint.json').read_text());assert peer['actual_recipient_replay_rejections']>=1 and peer['fresh_texts_decrypted']>=1 and peer['service_acceptance_for_duplicate']and peer['unique_recipient_delivery_for_resumed']is False
  markers=['authorized_capability_and_barriers=1','fresh_session_created=1','one_shot_provider_consumed=1']
  evidence=all(all((output/f'party-{i}.log').read_text().count('RESTORE_EVIDENCE '+marker)==1 for marker in markers)for i in range(5));assert evidence
  report.update(passed=True,native_mpc_executed=True,controllers=results,peer=peer,authorized_restore_fresh_session_markers=evidence)
 except subprocess.TimeoutExpired:error='controller-timeout'
 except Exception:error='integration-failure'
 finally:
  stop.set()
  for child in processes:
   if child.poll()is None:
    try:os.killpg(child.pid,signal.SIGTERM);child.wait(timeout=5)
    except ProcessLookupError:child.wait(timeout=5)
    except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=5);cleanup.append('forced-controller-group-kill')
    except Exception:cleanup.append('controller-cleanup-failure')
  if server.poll()is None:
   server.terminate()
   try:server.wait(timeout=5)
   except subprocess.TimeoutExpired:server.kill();server.wait();cleanup.append('forced-server-kill')
  listener.close();thread.join(timeout=5)
  if thread.is_alive():cleanup.append('endpoint-thread-not-joined')
  for log in logs:log.close()
  serverlog.close();integrity=all(sha(pathlib.Path(file))==digest for file,digest in pins.items())
  report.update(controller_error=error,cleanup=cleanup,controller_exit_codes=[c.returncode for c in processes],endpoint_transport=endpoint,source_integrity=integrity,seconds=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)-started)
  report['passed']=report['passed']and not error and not cleanup and integrity
  (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');(HERE/'integrated-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k]for k in ['passed','controller_error','controller_exit_codes','seconds','cleanup']}),flush=True)
 assert report['passed']
if __name__=='__main__':main()
