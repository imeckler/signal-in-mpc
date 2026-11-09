"""Matched one-bit verification wrapper; final sender state never opens.

The fused state evolution remains identical. Replace private padded final
outputs with a balanced equality predicate against public-known fixture data,
so the binary-only MP entry can disclose the same permitted predicate as EMP.
This is a benchmark verification entry, not a persistent application API.
"""
import hashlib
import json
import pathlib
import shutil

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'

if __name__=='__main__':
    source=BASE/'signal-core-2';target=BASE/'signal-core-2-check';target.mkdir(exist_ok=True)
    receipt=json.loads((source/'prepare-report.json').read_text())
    if hashlib.sha256((source/'circuit.txt').read_bytes()).hexdigest()!=receipt['bristol_sha256']:raise ValueError('fused circuit drift')
    n,m=receipt['input_bits'],receipt['output_bits']
    pads=(source/'alice.bin').read_bytes()[-m:]
    expected=[x^y for x,y in zip((source/'expected-padded.bin').read_bytes(),pads)]
    body=target/'body.txt';counts={'AND':0,'XOR':0,'INV':0};matches=[]
    with (source/'circuit.txt').open() as original,body.open('w') as out:
        ng,nw=map(int,original.readline().split());n1,n2,n3=map(int,original.readline().split());original.readline()
        if n3!=m:raise ValueError('output dimension drift')
        def remap(wire):
            if 2*n<=wire<2*n+m:raise ValueError('removed pad referenced inside core')
            return wire-m if wire>=2*n+m else wire
        for _ in range(ng-m):
            row=original.readline().split();counts[row[-1]]+=1
            row[2:-1]=[str(remap(int(x))) for x in row[2:-1]]
            out.write(' '.join(row)+'\n')
        for i in range(m):
            row=original.readline().split()
            if row[-1]!='XOR' or int(row[3])!=2*n+i:raise ValueError('output pad routing drift')
            matches.append(remap(int(row[2])))
        if original.read().strip():raise ValueError('trailing circuit gates')
        next_wire=nw-2*m
        def gate(op,a,b=0):
            global next_wire
            result=next_wire;next_wire+=1;counts[op]+=1
            out.write(f'1 1 {a} {result} INV\n' if op=='INV' else f'2 1 {a} {b} {result} {op}\n')
            return result
        matches=[wire if bit else gate('INV',wire) for wire,bit in zip(matches,expected)]
        while len(matches)>1:
            matches=[gate('AND',matches[i],matches[i+1]) if i+1<len(matches) else matches[i]
                     for i in range(0,len(matches),2)]
        if matches!=[next_wire-1]:raise ValueError('last output routing')
    with (target/'circuit.txt').open('wb') as out,body.open('rb') as data:
        out.write(f'{sum(counts.values())} {next_wire}\n{n} {n} 1\n\n'.encode());shutil.copyfileobj(data,out)
    for who in ('alice','bob'):(target/(who+'.bin')).write_bytes((source/(who+'.bin')).read_bytes()[:n])
    (target/'expected-output.bin').write_bytes(b'\x01')
    (target/'expected-logical.json').write_text(json.dumps(expected)+'\n')
    result={'scope':'same fused Signal core; balanced public-known fixture equality only; no sender state disclosure',
            'input_bits':n,'alice_input_bits':n,'output_bits':1,'counts':counts,'wires':next_wire,
            'core_and_gates':receipt['counts']['AND'],'verification_and_gates':m-1,
            'bristol_sha256':hashlib.sha256((target/'circuit.txt').read_bytes()).hexdigest(),
            'source_fused_sha256':receipt['bristol_sha256'],'directory':str(target)}
    (target/'prepare-report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
