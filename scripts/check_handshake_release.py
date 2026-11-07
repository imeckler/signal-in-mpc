#!/usr/bin/env python3
"""Check the exported handshake declassification gate against AESGCM."""
import sys, json, subprocess, tempfile, hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load, execute
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

def main():
    subprocess.run(['lake','build','emit_mpc'],cwd=ROOT,check=True)
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/'gate.json'
        with path.open('w') as out:
            subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),'tls-open-handshake-record','58'],stdout=out,check=True)
        image=load(path)
    key=bytes(range(16));iv=bytes(range(12));content=bytes(range(36));cases=[]
    for kind in (21,22,23):
        header=bytes.fromhex('1703030035')
        wire=header+AESGCM(key).encrypt(iv,content+bytes([kind]),header)
        for tamper in (False,True):
            altered=wire[:-1]+bytes([wire[-1]^1]) if tamper else wire
            inp=key+iv+bytes(8)+altered
            output=execute(image,[(b>>i)&1 for b in inp for i in range(7,-1,-1)],0,1)
            raw=bytes(sum(output[j+i]<<(7-i) for i in range(8)) for j in range(0,len(output),8))
            if tamper or kind==23: assert raw==bytes(len(raw))
            else: assert raw[:4]==bytes([255,kind,0,36]) and raw[4:40]==content
            cases.append({'type':kind,'bad_tag':tamper,'passed':True})
    report={'kind':'handshake_release_circuit_checks','cases':cases,'native_mpc_executed':False,
            'artifact_sha256':hashlib.sha256(json.dumps(image,sort_keys=True).encode()).hexdigest()}
    (ROOT/'benchmarks/results/lean-handshake-release-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))
if __name__=='__main__':main()
