#!/usr/bin/env python3
"""NEW account cut/restart: actual engine, two recipients and twelve texts.
Never resets/relabels an old account, reconstructs shares or manufactures a cap.
"""
import argparse,hashlib,importlib.util,json,os,pathlib,secrets,shlex,shutil,signal,socket,subprocess,sys,threading,time
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
spec=importlib.util.spec_from_file_location('sharded_tls_harness',ROOT/'handshake_backend/OutboxResumeWork/check_integrated.py');common=importlib.util.module_from_spec(spec);spec.loader.exec_module(common)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dependencies(binary,runtime):
 kind='fresh'if binary.name.endswith('fresh-worker')else'restored';out=[]
 for suffix in ['main','factory']:
  first=(binary.parent/f'.{kind}-{suffix}.d').read_text().replace('\\\n','').splitlines()[0]
  for item in shlex.split(first.split(':',1)[1]):
   p=pathlib.Path(item);p=p if p.is_absolute()else runtime/p
   if p.is_file()and p.is_relative_to(ROOT):out.append(p.resolve())
 return out

def phase(name,working,runtime,archive,output,port,timeout,pins,expected=None):
 folder=output/name;folder.mkdir();worker=working/('tls-sharded-fresh-worker'if name=='cut'else'tls-sharded-restored-worker');fixture=HERE/('peer-cut.json'if name=='cut'else'peer-restored.json');manifest=working/'programs.manifest';cert,key,trust=common.certs(folder);auth=folder/'public_auth'
 with(folder/'auth-build.log').open('w')as log:subprocess.run(['c++','-std=c++20','-O2','-I'+str(common.OPENSSL/'include'),str(ROOT/'handshake_backend/public_auth.cpp'),'-L'+str(common.OPENSSL/'lib'),'-lssl','-lcrypto','-o',str(auth)],stdout=log,stderr=subprocess.STDOUT,check=True)
 hosts=folder/'hosts';hosts.write_text('127.0.0.1\n'*5);session=secrets.token_hex(32);listener=socket.socket();listener.bind(('127.0.0.1',0));listener.listen(1);endpoint_port=listener.getsockname()[1]
 serverlog=(folder/'server.log').open('w');command=[sys.executable,str(HERE/'fixture_server.py'),str(cert),str(key),'127','no','http/1.1','--phase',name,'--fixture',str(fixture),'--report',str(folder/'endpoint.json')]
 if expected:command+=['--expected-resume',expected]
 server=subprocess.Popen(command,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=serverlog,text=True);endpoint={};stop=threading.Event();thread=threading.Thread(target=common.bridge,args=(listener,server,endpoint,timeout,stop),daemon=True);thread.start();processes=[];logs=[];cleanup=[];error=None;results=[];started=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
 report=dict(passed=False,phase=name,logs=str(folder.relative_to(ROOT)))
 try:
  for party in range(5):
   log=(folder/f'party-{party}.log').open('w');logs.append(log);cmd=['lake','env','lean','--run',str(HERE/'Controller.lean'),str(worker),str(working),str(party),str(hosts),str(port),str(manifest),session,'127.0.0.1',str(endpoint_port),'chat.signal.org',str(auth),str(trust),'0',name]
   child=subprocess.Popen(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=log,text=True,start_new_session=True,env=dict(os.environ,DYLD_LIBRARY_PATH=str(runtime),TLS_SHARDED_ACCOUNT_ROOT=str(archive)));processes.append(child);print(name+' controller party='+str(party)+' pid='+str(child.pid),flush=True)
  deadline=time.monotonic()+timeout
  while any(child.poll()is None for child in processes):
   if any(child.poll()not in [None,0]for child in processes):raise RuntimeError('controller_failure')
   if endpoint.get('error'):raise RuntimeError('endpoint_failure')
   if time.monotonic()>deadline:raise TimeoutError('controller_deadline')
   time.sleep(.25)
  for party,child in enumerate(processes):
   out,_=child.communicate();(folder/f'party-{party}.json-output').write_text(out);item=json.loads(out.splitlines()[-1]);assert child.returncode==0 and item['passed']and item['certificate_verified']and item['recipient_delivery_claimed']is False
   assert item['outcome_checkpoint']if name=='cut'else item['outbox_resume']and item['send_update'];results.append(item)
  thread.join(timeout=35);assert not thread.is_alive()and endpoint.get('completed')and'error'not in endpoint;peer=json.loads((folder/'endpoint.json').read_text());assert peer['passed']
  if name=='cut':
   assert peer['fresh_texts_decrypted']==2 and peer['withheld_responses']==1
   assert all((folder/f'party-{p}.log').read_text().count('SHARDED_OUTCOME sequence=2 cursor_advanced=0 producer_evaluated=0 conversation_commit_changes=0')==1 for p in range(5))
  else:
   assert peer['fresh_texts_decrypted']==10 and peer['replays_rejected_state_preserved']==1 and peer['resume_application_hash_matches']
   for party in range(5):
    log=(folder/f'party-{party}.log').read_text()
    for marker in ['authorized_capability_and_barriers=1','fresh_session_created=1','one_shot_provider_consumed=1']:assert log.count('RESTORE_EVIDENCE '+marker)==1
    assert log.count('SHARDED_ROUTE slot=0 route=pending')==1 and log.count('SHARDED_ROUTE slot=1 route=idle')==1
    assert 'SHARDED_CHECKPOINT phase=commit sequence=10'in log
  report.update(passed=True,controllers=results,peer=peer)
 except Exception as e:error=type(e).__name__
 finally:
  stop.set()
  for child in processes:
   if child.poll()is None:
    try:os.killpg(child.pid,signal.SIGTERM);child.wait(timeout=5)
    except ProcessLookupError:child.wait(timeout=5)
    except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=5);cleanup.append('forced_controller_group_kill')
    except Exception:cleanup.append('controller_cleanup_failure')
  if server.poll()is None:
   server.terminate()
   try:server.wait(timeout=5)
   except subprocess.TimeoutExpired:server.kill();server.wait();cleanup.append('forced_server_kill')
  listener.close();thread.join(timeout=5)
  if thread.is_alive():cleanup.append('endpoint_thread_not_joined')
  for log in logs:log.close()
  serverlog.close();integrity=all(sha(pathlib.Path(p))==v for p,v in pins.items());report.update(error=error,cleanup=cleanup,exit_codes=[c.returncode for c in processes],seconds=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)-started,endpoint=endpoint,integrity=integrity);report['passed']=report['passed']and error is None and not cleanup and integrity;(folder/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k]for k in ['passed','phase','error','exit_codes','seconds','cleanup']},indent=2),flush=True)
 return report

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--timeout',type=int,default=3600);parser.add_argument('--port',type=int,default=31300);args=parser.parse_args();working=ROOT/'.deps/tls-sharded-account-native/v1-candidate-1';runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';manifest=working/'programs.manifest';assert sha(manifest)=='511b04805187ae7f6756b8866e406bb956b182f80a617907999eda8f01c24a49'
 # One fixture identity has one active archive. Never start a second genesis or
 # roll journals back after an uncertain failed attempt; recovery is explicit.
 marker=working/'active-account.json';assert not marker.exists(),'account already initialized: preserve journal/current head and diagnose, do not reset/relabel'
 output=ROOT/'benchmarks/results/raw/tls-sharded-account'/secrets.token_hex(8);output.mkdir(parents=True);archive=output/'account';archive.mkdir();marker.write_text(json.dumps(dict(archive=str(archive),manifest_sha256=sha(manifest),fixture_material_sha256=sha(HERE/'FreshFixture.h')),indent=2)+'\n')
 data=working/'Player-Data';data.mkdir(exist_ok=True);source=ROOT/'.deps/tls-authorized-account-native/v1-candidate-2/Player-Data';copied={}
 for pattern in ['*.pem','*.key','*.0']:
  for p in source.glob(pattern):shutil.copyfile(p,data/p.name);copied[p.name]=sha(data/p.name);assert copied[p.name]==sha(p)
 assert len(copied)==15
 files={manifest,runtime/'libSPDZ.so',HERE/'peer-cut.json',HERE/'peer-restored.json',HERE/'FreshFixture.h',HERE/'Controller.lean',pathlib.Path(__file__),HERE/'fixture_server.py',ROOT/'signal_backend/Oracle/src/bin/signal-sharded-peer-fixture-oracle.rs'}
 for name in ['tls-sharded-fresh-worker','tls-sharded-restored-worker']:
  binary=working/name;files.add(binary);files.update(dependencies(binary,runtime))
 for name in ['signal-sharded-peer-fixture-oracle','signal-restored-recipient-oracle','signal-established-send-oracle','signal-chat-response-oracle']:files.add(ROOT/'.deps/signal-established-send-oracle-target/debug'/name)
 for line in manifest.read_text().splitlines()[1:]:digest,name=line.split(' ',1);assert sha(working/name)==digest;files.add(working/name)
 files.update(HERE.glob('*.h'));files.update(HERE.glob('*Factory.cpp'));pins={str(p.resolve()):sha(p)for p in files};(output/'launch-receipt.json').write_text(json.dumps(dict(source_product_sha256=pins,credential_sha256=copied),indent=2)+'\n')
 # Freeze actual compile dependencies before either native phase.
 snapshot=output/'source-snapshot'
 for p in files:
  if p.is_relative_to(ROOT)and '.deps'not in p.relative_to(ROOT).parts:
   dest=snapshot/p.relative_to(ROOT);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 phases=[];first=phase('cut',working,runtime,archive,output,args.port,args.timeout,pins);phases.append(first)
 if first['passed']:phases.append(phase('restored',working,runtime,archive,output,args.port+10,args.timeout,pins,first['peer']['application_sha256']['0']))
 result=dict(passed=len(phases)==2 and all(p['passed']for p in phases),native_MPC=True,production_gate_enabled=False,full_system_complete=False,NEW_fixture_identity_only=True,historical_head3_untouched=True,manifest_sha256=sha(manifest),archive_root=str(archive),logs=str(output.relative_to(ROOT)),source_product_sha256=pins,phases=phases,private_IDs_or_keys_reconstructed=False,recipient_unique_delivery_claim=False,scope='Two conversations: actual current-head/fullfield working-set readmit and both barriers; freshTLS; pending0 replay plus acknowledged-idle1; ten new texts and out-of-order response pairs. No fresh account bootstrap/refresh/throughput claim.')
 (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');(HERE/'integrated-report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['passed','archive_root','logs']},indent=2),flush=True)
 if not result['passed']:raise SystemExit(1)
if __name__=='__main__':main()
