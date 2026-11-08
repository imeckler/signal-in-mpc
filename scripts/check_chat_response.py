#!/usr/bin/env python3
"""Disposable streaming response fixtures against actual prost+inspected validation."""
from pathlib import Path
import hashlib,json,random,subprocess,time
import sys,re
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
def vi(n):
    out=bytearray()
    while n>=128:out.append((n&127)|128);n>>=7
    out.append(n);return bytes(out)
def scalar(tag,n):return vi(tag*8)+vi(n)
def blob(tag,b):return vi(tag*8+2)+vi(len(b))+b
def response(inner,typ=2):return scalar(1,typ)+blob(3,inner)
def inner(id=0,status=200):return scalar(1,id)+scalar(2,status)
def main():
    started=time.monotonic();out=ROOT/'benchmarks/results/raw/chat-response';out.mkdir(parents=True,exist_ok=True)
    cases=[]
    def add(wire,id=0,narrow=False):cases.append((wire,id,narrow))
    for id in [0,1,127,128,2**32-1,2**32,2**63-1,2**63,2**64-1]:
        for status in [200,204,299]:add(response(inner(id,status)+blob(4,b'{}')),id)
    for status in [0,99,100,199,200,299,300,401,500,999,1000,65535,70000,2**32+200]:add(response(inner(7,status)),7)
    for typ in [0,1,2,3,2**32+2,2**63+2]:add(response(inner(),typ))
    add(b'');add(scalar(1,2));add(blob(3,inner()));add(response(scalar(2,200)));add(response(scalar(1,0)))
    add(scalar(1,2)+blob(2,b'')+blob(3,inner()))
    add(response(scalar(1,1)+scalar(1,2)+scalar(2,200)),2)
    add(response(scalar(1,1)+scalar(1,0)+scalar(2,200)),0)
    add(response(scalar(1,1)+scalar(2,200)),0)
    add(response(inner()+scalar(2,401)));add(response(inner(0,0)+scalar(2,200)))
    add(scalar(1,2)+blob(3,scalar(1,9))+blob(3,scalar(2,200)),9)
    add(scalar(1,2)+blob(3,inner(9))+blob(3,b''),9)
    add(response(scalar(2,200)+scalar(1,0)))
    for body in [None,b'',b'{}',bytes(range(32))]:add(response(inner()+(b'' if body is None else blob(4,body))))
    add(response(inner()+blob(4,b'old')+blob(4,b'')))
    add(response(inner()+blob(4,b'')+blob(4,b'new')))
    for message in [b'',b'OK','snowman \u2603\U0001f600'.encode(),b'\x00\t\r\n']:
        add(response(inner()+blob(3,message)))
    add(response(inner()+blob(3,b'first')+blob(3,b'second')))
    for header in [b'X-Test: value',b'x: \t',b'x:\r\nvalue\r\n',b'x: a\tb',b'bad name: value',b'x: a\nb',b'',b'x:\x00']:
        add(response(inner()+blob(5,header)))
    add(response(inner()+blob(5,b'x:1')+blob(5,b'x:2')))
    add(response(inner()+blob(5,'x: \u2003value\u2003'.encode())))
    for whitespace in ['\u0085','\u00a0','\u1680',*map(chr,range(0x2000,0x200b)),'\u2028','\u2029','\u202f','\u205f','\u3000']:
        add(response(inner()+blob(5,('x:'+whitespace+'\r\nvalue\r\n'+whitespace).encode())))
        add(response(inner()+blob(5,('x:value\r\n'+whitespace).encode())))
    add(response(inner()+blob(5,'x:value\r\n\u200b'.encode())))
    for tag,unknown in [(6,scalar(6,2**64-1)),(7,vi(7*8+1)+bytes(8)),(8,blob(8,b'\xff\xff')), (9,vi(9*8+5)+bytes(4))]:
        add(response(inner()+unknown));add(scalar(1,2)+unknown+blob(3,inner()))
    group=vi(6*8+3)+scalar(1,999)+vi(6*8+4)
    add(response(inner()+group));add(scalar(1,2)+group+blob(3,inner()))
    for depth in [1,98,99,100,101]:
        group=vi(6*8+3)*depth+vi(6*8+4)*depth
        add(response(inner()+group));add(scalar(1,2)+group+blob(3,inner()))
    bad=[response(vi(8)+b'\x80'*9+b'\x02'+scalar(2,200)),response(vi(8)+b'\x80'*10+b'\x00'+scalar(2,200)),
      response(vi(8)+b'\x80'),response(inner()+vi(4*8+2)+vi(2**64-1)),response(inner()+b'\x00'),
      response(inner()+vi(2**32)),response(blob(1,b'')+scalar(2,200)),blob(1,b'')+blob(3,inner()),
      response(inner()+blob(3,b'\xc0\x80')),response(inner()+blob(3,b'\xff')+blob(3,b'valid')),
      response(inner()+blob(5,b'x:\xff')),response(inner()+vi(6*8+4)),response(inner()+vi(6*8+3)+vi(7*8+4))]
    for wire in bad:add(wire)
    add(response(vi(8)+b'\x80'*9+b'\x00'+scalar(2,200)))
    base=response(inner()+blob(4,b'body')+blob(5,b'x: value'))
    for n in range(len(base)):add(base[:n])
    rng=random.Random(67241)
    for _ in range(40):
        mutated=bytearray(base);i=rng.randrange(len(mutated));mutated[i]^=1<<rng.randrange(8);add(bytes(mutated))
    oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-chat-response-oracle'
    actual=subprocess.run([str(oracle)],input=''.join(json.dumps({'wire':w.hex(),'expected_id':id})+'\n' for w,id,_ in cases),text=True,capture_output=True,check=True)
    answers=[json.loads(line) for line in actual.stdout.splitlines()];assert len(answers)==len(cases)
    records=[]
    for (wire,id,narrow),answer in zip(cases,answers):
        accepted=answer.get('accepted',False) and answer.get('correlated',False) and not narrow
        flag=lambda v:'255' if v else '0'
        body=answer.get('body','') if accepted else ''
        message=answer.get('message','') if accepted else ''
        # Oracle returns public fixture body as hex, not live application bytes.
        body=answer.get('body_hex',answer.get('bodyhex',body))
        message=answer.get('message_hex',answer.get('messagehex',message))
        if isinstance(message,str) and accepted and answer.get('message_present') and not ('message_hex' in answer or 'messagehex' in answer):
            message=message.encode().hex()
        records.append(' '.join([wire.hex() or '-',str(id),flag(accepted),flag(accepted and answer.get('is_success',False)),
          flag(accepted and answer.get('body_present',False)),(body or '-') if accepted else '-',
          flag(accepted and answer.get('message_present',False)),(message or '-') if accepted else '-',str(answer.get('header_count',0) if accepted else 0)]))
    fixture=out/'cases.txt';fixture.write_text('\n'.join(records)+'\n')
    (out/'pinned-oracle.json').write_text(json.dumps(answers,indent=2)+'\n')
    subprocess.run(['lake','build','chat_response_checks','chat_response_emitter'],cwd=ROOT,check=True)
    audit=out/'Audit.lean';endpoints=['step_map','process_map','readState_map','runByte_map','compiled_runByte_correct']
    audit.write_text('import TlsMpc.TlsChatResponse\n'+''.join('#print axioms TlsMpc.TlsChatResponse.'+n+'\n' for n in endpoints))
    proof=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,text=True,capture_output=True,check=True)
    (out/'proof.log').write_text(proof.stdout+proof.stderr)
    for line in proof.stdout.splitlines():
        if 'depends on axioms:' in line:assert set(re.search(r'\[(.*)\]',line).group(1).replace(' ','').split(','))<=set(['propext','Classical.choice','Quot.sound']),line
    vectors=out/'step-vectors.txt'
    with (out/'checks.log').open('w') as log:
        subprocess.run([str(ROOT/'.lake/build/bin/chat_response_checks'),str(fixture),str(vectors)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=900)
    artifact=out/'tls-chat-response-4096.json'
    with artifact.open('w') as stream:subprocess.run([str(ROOT/'.lake/build/bin/chat_response_emitter'),'4096'],stdout=stream,check=True,timeout=900)
    inputs=[];expected=[]
    for line in vectors.read_text().splitlines():
        inp,value=line.split();inputs.append(bytes.fromhex(inp));expected.append(bytes.fromhex(value))
    assert inputs and evaluate_lanes(load(artifact),inputs)==expected,'compiled chat byte machine mismatch'
    print((out/'checks.log').read_text())
    names=['TlsMpc/TlsChatResponse.lean','handshake_backend/WebSocketWork/ChatResponseFixture.lean',
      'handshake_backend/WebSocketWork/EmitChatResponse.lean','scripts/check_chat_response.py',
      '.lake/build/bin/chat_response_checks','.lake/build/bin/chat_response_emitter']
    report={'passed':True,'cases':len(cases),'native_mpc_executed':False,'elapsed_seconds':time.monotonic()-started,
      'scope':'streaming algorithm versus actual generatedprost plus explicitly copied private target validation, mapped compiler and numeric byte-machine checks; no whole-target refinement or native claim',
      'interface_mask_cases':4,'compiled_step_vectors':len(inputs),'proof_endpoints':endpoints,
      'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),
      'integration_profile':'UTF8 strings and Unicode trim; one pending response; capacity4096',
      'sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names}}
    (ROOT/'benchmarks/results/tls-chat-response-checks.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
