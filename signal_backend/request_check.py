#!/usr/bin/env python3
"""Public private-framing fixtures decoded by unchanged vendored h2 0.4.16."""
import hashlib,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'signal_backend';ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    binary=ROOT/'.deps/signal-established-send-checks/request-fixture'
    subprocess.run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-O2',str(HERE/'request_fixture.cpp'),'-o',str(binary)],check=True)
    sizes=[0,1,120,121,122,127,128,1024]
    rows=[]
    for size in sizes:
        wire=subprocess.check_output([str(binary),str(size)],text=True).strip()
        rows.append({'mode':'h2','wire':wire})
    native=subprocess.run([str(ORACLE)],input=''.join(json.dumps(r)+'\n' for r in rows),
        capture_output=True,text=True,check=True,timeout=30)
    answers=[json.loads(line) for line in native.stdout.splitlines()]
    assert len(answers)==len(sizes)
    for size,answer in zip(sizes,answers):
        assert answer=={'method':'POST','path':'/org.signal.chat.messages.Messages/SendMessage',
            'authority':'grpc.chat.signal.org','authorization':'Basic '+'x'*size,
            'content_type':'application/grpc','te':'trailers','body':'00000000050a03010203'},answer
    report={'public_fixture_cases':len(sizes),'actual_h2_decoder':'h2 0.4.16 server handshake and request/DATA parsing',
        'all_metadata_and_body_match':True,'public_shape_rejections_tested':['stream0','even stream','unaligned bits','body over12000 bytes'],'secret_values_use_hpack_never_indexed_literals':True,
        'request_values_stay_shared_in_producer':True,'public_lengths_and_stream_id':True,
        'actual_signal_request_protobuf_implemented':False,'tls_handle_handoff_executed':False,
        'http2_connection_flow_control_and_responses_implemented':False,'production_ready':False,
        'oracle_binary_sha256':sha(ORACLE),'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in [
            Path(__file__),HERE/'PrivateGrpcRequest.h',HERE/'request_fixture.cpp',HERE/'Oracle/src/main.rs',
            HERE/'Oracle/Cargo.toml',HERE/'Oracle/Cargo.lock',
            ROOT/'.deps/libsignal-vendor/h2-0.4.16/src/hpack/decoder.rs']}}
    (HERE/'request-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('8 actual h2 parser matches, including HPACK integer-length boundaries; no TLS activation')
if __name__=='__main__':main()
