#!/usr/bin/env python3
"""Targeted producer/store tests; public fixtures, never production secret input."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from signal_backend.shape import SendShape
from scripts.check_lean_signal_spqr_send import cases,spqr_derive,varint
from scripts.check_lean_signal_chain_send import derive
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load

HERE=ROOT/'signal_backend'
BUILD=ROOT/'.deps/signal-established-send-checks'
ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run(args,**kwargs):return subprocess.run(list(map(str,args)),check=True,**kwargs)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile-backend',action='store_true')
    args=parser.parse_args()
    BUILD.mkdir(exist_ok=True)
    run(['lake','build','TlsMpc.Signal.SpqrSend'],cwd=ROOT)
    run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-O2',HERE/'store_checks.cpp','-o',BUILD/'store-checks'])
    environment=dict(os.environ,CARGO_TARGET_DIR=str(ROOT/'.deps/signal-established-send-oracle-target'))
    run(['cargo','+nightly-2025-09-24','build','--offline','--locked','--ignore-rust-version'],cwd=HERE/'Oracle',env=environment)
    results=[];native_rows=[];native_expected=[]
    for arguments,inputs,expected,labels,_ in cases():
        shape=SendShape(arguments)
        path=BUILD/(shape.stem+'.json')
        with path.open('w') as stream:
            run(['lake','env','lean','--run','SignalReference/SpqrSendExport.lean',*arguments],cwd=ROOT,stdout=stream)
        image=load(path)
        assert image['input_bits']==shape.input_bytes*8 and len(image['outputs'])==shape.output_bytes*8
        observed=evaluate_lanes(image,inputs)
        assert observed==expected,arguments
        lines=[]
        for raw,out,label in zip(inputs,observed,labels):
            reuse=label.startswith('consecutive-coupled-state-') and not label.endswith('-0')
            lines.append(f'{int(reuse)} {raw.hex()} {out.hex()}')
            if out[0]!=255:continue
            chunk=shape.chunk_bytes
            next_pq,pq_key=spqr_derive(raw[73:105],int.from_bytes(raw[105:109],'big'))
            _,cipher_key,mac_key,iv=derive(raw[41:73],pq_key)
            epoch=int.from_bytes(raw[109:117],'big');pc=int.from_bytes(raw[105:109],'big')
            pq=b'\1'+varint(epoch)+varint(pc+1)+raw[117:118]
            if chunk:pq+=varint(int.from_bytes(raw[118:120],'big'))+raw[120:152]
            native_rows.append({'version':raw[0],'counter':int.from_bytes(raw[1:5],'big'),
                'previous':int.from_bytes(raw[5:9],'big'),'ratchet':raw[9:41].hex(),
                'sender':raw[118+chunk:150+chunk].hex(),'receiver':raw[150+chunk:182+chunk].hex(),
                'plain':raw[182+chunk:182+chunk+shape.size].hex(),
                'addresses':raw[182+chunk+shape.size:].hex(),'pq':pq.hex(),
                'cipher_key':cipher_key.hex(),'mac_key':mac_key.hex(),'iv':iv.hex()})
            native_expected.append(out[73:].hex())
        # Rejected sends must preserve state for the following accepted send.
        rejected=next(i for i,l in enumerate(labels) if l=='payload-kind-255')
        lines += [f'0 {inputs[rejected].hex()} {observed[rejected].hex()}',
                  f'1 {inputs[0].hex()} {observed[0].hex()}']
        command=[BUILD/'store-checks',*arguments[1:7],str(int(shape.chunk)),str(int(shape.addresses))]
        result=run(command,input='\n'.join(lines)+'\n',capture_output=True,text=True)
        print(result.stdout.strip(),flush=True)
        row={'arguments':arguments,'circuit_cases':len(inputs),'store_transitions':len(lines),
             'artifact_sha256':sha(path),'input_bytes':shape.input_bytes,'output_bytes':shape.output_bytes,
             'descriptor':shape.descriptor,'cpp_store_checks':result.stdout.strip()}
        if args.compile_backend:
            from signal_backend.prepare import compile_profile
            row['native_function_manifest']=str(compile_profile(path,shape).relative_to(ROOT))
        results.append(row)
    native=run([ORACLE],input=''.join(json.dumps(row)+'\n' for row in native_rows),capture_output=True,text=True)
    answers=[json.loads(line) for line in native.stdout.splitlines()]
    assert len(answers)==len(native_expected)
    assert [row['wire'] for row in answers]==native_expected
    files=[HERE/'SendShape.h',HERE/'EstablishedSendStore.h',HERE/'store_checks.cpp',HERE/'shape.py',HERE/'PrivateGrpcRequest.h',
           Path(__file__),ROOT/'programs/signal_export.mpc',HERE/'Oracle/Cargo.toml',HERE/'Oracle/Cargo.lock',
           HERE/'Oracle/src/main.rs',ROOT/'TlsMpc/Signal/SpqrSend.lean',ROOT/'TlsMpc/Signal/Export.lean',
           ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/protocol.rs',
           ROOT/'.deps/libsignal-v0.106.1/rust/crypto/src/aes_cbc.rs']
    report={'cases':results,'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},
        'native_oracle_sha256':sha(ORACLE),'actual_libsignal_constructor_and_aes_cases':len(answers),
        'actual_libsignal_parser_successes':sum(row['parse']=='ok' for row in answers),
        'actual_libsignal_parser_errors':sorted(set(row['parse'] for row in answers if row['parse']!='ok')),
        'native_mpc_executed':False,'native_backend_compiled':args.compile_backend,
        'status_and_all_state_stay_shared':True,'host_transaction_atomic_before_wire_return':True,
        'additional_store_checks':['Malformed runtime output poisons store','Payload dimension mismatch never invokes runtime','Opaque handoff returns handle; retention failure poisons store'],
        'durable_store':False,'full_libsignal_session_or_spqr_transition_refinement':False,
        'production_ready':False,'throughput_measured':False,
        'boundaries':['Already selected active epoch and chunk payload; no DH/KEM state machine.',
          'KDF test keys derived by independent Python HMAC; native oracle covers actual AES wrapper and SignalMessage constructor, not private ChainKey methods.',
          'Circuit and C++ tests use public fixtures; native private runtime evaluation and TLS/H2 composition remain separate.',
          'No filesystem durability or crash recovery; single worker serializes store access.',
          'Secret rejection preserves selected chain state and yields zero wire; status is never opened by this store.']}
    (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'{sum(r["circuit_cases"] for r in results)} circuit cases; '
          f'{sum(r["store_transitions"] for r in results)} host store transitions; '
          f'{len(answers)} actual libsignal constructor/AES matches',flush=True)
if __name__=='__main__':main()
