"""Fuse one/two established Signal core sends with internal state continuity.

No curve, sealed sender, TLS or response parser. Zero-plaintext historical
fixture only. Streaming gate emission avoids retaining millions of gate tuples.
"""
import argparse
import hashlib
import json
import pathlib
import secrets
import shutil
import time
import resource
from convert import lower

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'

def b(bytes_):return [bool((x>>i)&1) for x in bytes_ for i in range(7,-1,-1)]
def selected(state,output):
    def part(seq,start,end):return seq[start*8:end*8]
    return (part(state,0,1)+part(output,33,37)+part(state,5,41)+part(output,1,33)
            +part(output,37,69)+part(output,69,73)+part(state,109,181))

def prepare(steps):
    if steps not in (1,2):raise ValueError('bounded profile supports one/two sends')
    started=time.monotonic()
    source=ROOT/'.deps/signal-established-send-checks/signal-spqr-send-0-1-1-1-1-0-none-none.json'
    fixture=ROOT/'.deps/signal-established-native/signal-spqr-send-0-1-1-1-1-0-none-none/fixture-logs/public-fixtures.txt'
    rows=[tuple(bytes.fromhex(x) for x in line.split()) for line in fixture.read_text().splitlines()]
    if len(rows)!=2 or any(len(a)!=182 or len(c)!=145 for a,c in rows):raise ValueError('fixture shape drift')
    image=json.loads(source.read_bytes())
    if image['input_bits']!=1456 or len(image['outputs'])!=1160:raise ValueError('graph profile drift')
    work=BASE/f'signal-core-{steps}';work.mkdir(exist_ok=True)
    logical=rows[0][0]+b''.join(bytes([rows[i][0][117]]) for i in range(1,steps))
    n=len(logical)*8;m=(steps*(1+72)+181)*8
    next_wire=2*n+m;counts={'AND':0,'XOR':0,'INV':0}
    body=work/'gates-body.txt'
    with body.open('w') as f:
        def gate(op,a,c=0):
            nonlocal next_wire
            out=next_wire;next_wire+=1;counts[op]+=1
            f.write(f'1 1 {a} {out} INV\n' if op=='INV' else f'2 1 {a} {c} {out} {op}\n')
            return out
        inputs=[gate('XOR',i,n+i) for i in range(n)]
        state=inputs[:117*8]+inputs[118*8:182*8]
        outputs=[];expected=[]
        expected_state=b(rows[0][0][:117]+rows[0][0][118:])
        for i in range(steps):
            payload=inputs[117*8:118*8] if i==0 else inputs[(182+i-1)*8:(182+i)*8]
            actual=lower(image,state[:117*8]+payload+state[117*8:],gate)
            outputs+=actual[:8]+actual[73*8:]
            state=selected(state,actual)
            wanted=b(rows[i][1]);expected+=wanted[:8]+wanted[73*8:]
            expected_state=selected(expected_state,wanted)
        outputs+=state;expected+=expected_state
        if len(outputs)!=m:raise ValueError('fused output dimensions')
        for i,wire in enumerate(outputs):gate('XOR',wire,2*n+i)
    circuit=work/'circuit.txt'
    with circuit.open('wb') as out,body.open('rb') as data:
        out.write(f'{sum(counts.values())} {next_wire}\n{n} {n+m} {m}\n\n'.encode())
        shutil.copyfileobj(data,out)
    # Strong fresh output pads, delivered only to Alice; Bob receives padded
    # results. The fixture driver knows dummy inputs/expected outputs only.
    bob=[bool(secrets.randbits(1)) for _ in range(n)]
    alice=[x^y for x,y in zip(b(logical),bob)]
    pads=[bool(secrets.randbits(1)) for _ in range(m)]
    (work/'bob.bin').write_bytes(bytes(bob));(work/'alice.bin').write_bytes(bytes(alice+pads))
    (work/'expected-padded.bin').write_bytes(bytes(x^y for x,y in zip(expected,pads)))
    receipt={'scope':'fused zero-plaintext established Signal core only; no full producer/TLS claim',
             'steps':steps,'input_bits':n,'output_bits':m,'counts':counts,'wires':next_wire,
             'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
             'fixture_sha256':hashlib.sha256(fixture.read_bytes()).hexdigest(),
             'bristol_sha256':hashlib.sha256(circuit.read_bytes()).hexdigest(),
             'bristol_bytes':circuit.stat().st_size,
             'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
             'preparation_seconds':time.monotonic()-started,'directory':str(work)}
    (work/'prepare-report.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--steps',type=int,default=2);prepare(p.parse_args().steps)
