#!/usr/bin/env python3
"""Actual Lean numeric exports against independent TLS padding/type fixtures."""
from pathlib import Path
import json
import random
import subprocess
import sys
import hashlib
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from backend_adapter.aig import execute, statistics
from backend_adapter.aig_packed import plan


def reference(data):
    last = next((i for i in range(len(data)-1,-1,-1) if data[i]), None)
    if last is None or not (data[last] == 23 or (data[last] in (21,22) and last>0)):
        return bytes(len(data)+4)
    return bytes([255,data[last],last//256,last%256])+data[:last]+bytes(len(data)-last)


def main():
    rng=random.Random(821739)
    profiles=[]
    for size in (1,2,16,128,1024):
        run=subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),'tls-parse-inner',str(size)],
                           check=True,capture_output=True,text=True,timeout=120)
        image=json.loads(run.stdout)
        _,groups=plan(image)
        samples=[bytes(size),bytes([255])*size]
        offsets=sorted({0,size//2,size-1})
        for offset in offsets:
            for kind in (1,21,22,23,24,255):
                samples.append(bytes(rng.randrange(256) for _ in range(offset))+bytes([kind])+bytes(size-offset-1))
        samples += [bytes(rng.randrange(256) for _ in range(size)) for _ in range(8)]
        for data in samples:
            bits=[(byte>>bit)&1 for byte in data for bit in range(7,-1,-1)]
            output=execute(image,bits,0,1)
            raw=bytes(sum(output[j+i]<<(7-i) for i in range(8)) for j in range(0,len(output),8))
            assert raw==reference(data),(size,data.hex(),raw.hex())
        profiles.append({'plaintext_bytes':size,'fixtures':len(samples),
                         'and_depth':max(key[0] for key,_ in groups),**statistics(image),
                         'artifact_sha256':hashlib.sha256(run.stdout.encode()).hexdigest()})
    before=json.loads((ROOT/'benchmarks/results/tls-inner-depth-audit.json').read_text())['profiles']
    for old in before:
        new=next(p for p in profiles if p['plaintext_bytes']==old['plaintext_bytes'])
        if old['plaintext_bytes']>=128:
            assert new['and_depth']<old['and_depth']
    report={'profiles':profiles,'previous_sequential_profiles':before,'native_mpc_executed':False,
            'spec_and_compiler_theorem':'TlsMpc.TlsInnerParallel.compiled_decode_correct',
            'source_sha256':hashlib.sha256((ROOT/'TlsMpc/TlsInnerParallel.lean').read_bytes()).hexdigest()}
    (ROOT/'benchmarks/results/tls-parallel-inner-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(profiles))


if __name__=='__main__':main()
