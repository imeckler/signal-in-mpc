#!/usr/bin/env python3
"""Five-party isolated private streaming response/correlation test; no TLS/service activation."""
from pathlib import Path
import hashlib,json,secrets,shutil,subprocess,time
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    output=ROOT/'benchmarks/results/raw/native-chat-response'/secrets.token_hex(8);output.mkdir(parents=True)
    working=output/'working';working.mkdir()
    stage=ROOT/'.deps/tls-websocket-upgrade-native';runtime=ROOT/'.deps/tls-session-runtime'
    report={'passed':False,'native_mpc_executed':False,'application_gate_changed':False,
      'scope':'public disposable five-party streaming uint64/uint32/merge/UTF8/body validation and shared request-ID correlation; only three decision bytes opened; no actual TLS/service connection',
      'cleanup_errors':[],'logs':str(output.relative_to(ROOT))}
    started=time.monotonic();processes=[];logs=[]
    from check_chat_response import scalar,blob,response,inner
    cases=[(response(inner(2**64-1)+blob(3,'snowman \u2603'.encode())+blob(4,b'{}')+blob(5,'x:\u2003value\r\n\u2003'.encode())),2**64-1,'success'),
      (scalar(1,2)+blob(3,scalar(1,127))+blob(3,scalar(2,200)+blob(4,b'old')+blob(4,b'{}')),127,'success'),
      (response(inner(128,2**32+200)+blob(3,b'OK')),128,'success'),
      (response(inner(128,401)),128,'non2xx'),(response(inner(128)),129,'reject')]
    fixture=output/'cases.txt';fixture.write_text(''.join(raw.hex()+' '+id.to_bytes(8,'big').hex()+' '+outcome+'\n' for raw,id,outcome in cases))
    names=['TlsMpc/TlsChatResponse.lean','TlsMpc/TlsWebSocketFrame.lean',
      'TlsMpc/Signal/Word64.lean','TlsMpc/Signal/VarintDecode/Spqr.lean',
      'handshake_backend/WebSocketWork/NativeChatResponse.h','handshake_backend/WebSocketWork/chat_native_fixture.cpp',
      'handshake_backend/WebSocketWork/EmitChatResponse.lean','handshake_backend/WebSocketWork/prepare_chat_response.py',
      'scripts/check_native_chat_response.py','handshake_backend/NativeWorker.h',
      'handshake_backend/WebSocketWork/Makefile','handshake_backend/SessionLifecycle.h','handshake_backend/SessionWork/NativeLifecycle.h',
      '.deps/tls-session-runtime/tls-chat-response-fixture','.deps/tls-session-runtime/MP-SPDZ/libSPDZ.so',
      '.lake/build/bin/chat_response_emitter','.deps/tls-websocket-upgrade-native/chat-4096.manifest']
    before={name:sha(ROOT/name) for name in names}
    try:
        manifest=output/'upgrade.manifest'
        selected={}
        for source in (stage/'chat-4096.manifest',):
            for line in source.read_text().splitlines()[1:]:
                digest,name=line.split(' ',1)
                assert name not in selected or selected[name]==digest
                selected[name]=digest
        manifest.write_text('tls-mpc-pinned-files-v1\n'+''.join(selected[name]+' '+name+'\n' for name in sorted(selected)))
        for line in manifest.read_text().splitlines()[1:]:
            digest,name=line.split(' ',1);path=working/name;path.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(stage/name,path);assert sha(path)==digest
        with (output/'ssl.log').open('w') as log:
            subprocess.run(['bash',str(ROOT/'.deps/sharing-refresh/MP-SPDZ/Scripts/setup-ssl.sh'),'5'],cwd=working,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=30)
        hosts=output/'hosts';hosts.write_text('127.0.0.1\n'*5)
        for party in range(5):
            log=(output/f'party-{party}.log').open('w');logs.append(log)
            processes.append(subprocess.Popen([str(runtime/'tls-chat-response-fixture'),str(party),str(hosts),'20120',str(manifest),str(fixture)],cwd=working,stdout=log,stderr=subprocess.STDOUT))
        codes=[p.wait(timeout=max(1,900-(time.monotonic()-started))) for p in processes]
        report['exit_codes']=codes
        if codes!=[0]*5:raise RuntimeError('native chat fixture failed; inspect public logs')
        assert before=={name:sha(ROOT/name) for name in names},'native component source/product changed during run'
        report.update(passed=True,native_mpc_executed=True)
    except Exception as error:report['error']=str(error)
    finally:
        for p in processes:
            try:
                if p.poll() is None:p.terminate()
                try:p.wait(timeout=5)
                except subprocess.TimeoutExpired:p.kill();p.wait(timeout=5)
            except Exception as error:report['cleanup_errors'].append(str(error))
        for log in logs:log.close()
        report['sha256']=before
        report['sources_unchanged_at_end']=before=={name:sha(ROOT/name) for name in names}
        report['log_sha256']={str(p.relative_to(ROOT)):sha(p) for p in output.glob('*.log')}
        report['elapsed_seconds']=time.monotonic()-started
        if report['cleanup_errors']:report['passed']=False
        text=json.dumps(report,indent=2)+'\n';(output/'report.json').write_text(text)
        (ROOT/'benchmarks/results/tls-native-chat-response.json').write_text(text);print(text)
    if not report['passed']:raise SystemExit(1)
if __name__=='__main__':main()
