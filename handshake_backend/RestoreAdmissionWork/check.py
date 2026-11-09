#!/usr/bin/env python3
import hashlib,json,pathlib,subprocess,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
sources=[HERE/'PrivateRequestCursor.h',HERE/'CoordinatedConversation.h',HERE/'cursor_checks.cpp',HERE/'coordinator_checks.cpp',ROOT/'handshake_backend/NativeSession.h',ROOT/'handshake_backend/WebSocketWork/NativeConversation.h',ROOT/'handshake_backend/WebSocketWork/MuxProviderCoordinator.h']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='tls-restore-admission-') as tmp:
 tmp=pathlib.Path(tmp)
 for name in ['cursor','coordinator']:
  exe=tmp/name
  subprocess.run(['clang++','-std=c++17','-fsanitize=address,undefined','-fno-omit-frame-pointer','-g',str(HERE/(name+'_checks.cpp')),'-o',str(exe)],check=True)
  args=[str(exe)]
  if name=='coordinator':args.append(str(tmp/'fences'))
  subprocess.run(args,check=True)
 runtime=ROOT/'.deps/tls-public-program-cache-runtime-v2/MP-SPDZ'
 target=tmp/'tls-provider-api-probe'
 log=tmp/'api-build.log'
 with log.open('w') as output:
  subprocess.run(['make','-f',str(ROOT/'handshake_backend/WebSocketWork/Makefile'),'TLS_ROOT='+str(ROOT/'handshake_backend'),'TLS_BUILD='+str(tmp),str(target)],cwd=runtime,stdout=output,stderr=subprocess.STDOUT,check=True)
 report={'passed':True,'asan_ubsan':True,'actual_ownedbits_api_compiled_linked':True,'native_mpc_executed':False,
 'actual_code_under_test':['PrivateRequestCursor','CoordinatedConversation','VariableSendStore','produce_batch_with_checkpoint','PrivateMuxRegistry'],
 'mock_boundaries':['kernel evaluation','whole-account certificate/disk cursor','account canonical binding','network/TLS'],
 'checks':['staged batch cursor commit once','reentrant close/reserve poisons','dimensions/phase rejection','two independent conversations','reserve/bind/commit before retain','reordered correlated completion slots','stale response rejection','failure after durable reserve before cursor install','whole failed range burned on simulated restart','old outbox IDs retained without reuse'],
 'full_account_authorization_validated':False,'fresh_tls_restore_interop_validated':False,
 'sources':{str(p.relative_to(ROOT)):sha(p) for p in sources},'api_binary_sha256':sha(target)}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k] for k in ['passed','asan_ubsan','actual_ownedbits_api_compiled_linked','native_mpc_executed']}))
