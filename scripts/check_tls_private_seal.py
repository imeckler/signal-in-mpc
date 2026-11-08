#!/usr/bin/env python3
"""Kernel-check private TLS length/layout, evaluate fresh exports against AESGCM."""
from datetime import datetime,timezone
from pathlib import Path
import hashlib,json,subprocess,sys,random,re
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes
from scripts.prepare_tls_shape import Shape

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    work=ROOT/'handshake_backend/PayloadWork';out=ROOT/'benchmarks/results/raw/tls-private-seal';out.mkdir(parents=True,exist_ok=True)
    subprocess.run(['lake','build','private_tls_emitter'],cwd=ROOT,check=True,stdout=(out/'build.log').open('wb'),stderr=subprocess.STDOUT)
    audit=out/'KernelChecks.lean'
    endpoints=['eqLength_value','build_map','build_length','build_correct','build_valid','seal_map','seal_status','seal_valid_record','compiled_seal_correct']
    audit.write_text('import TlsMpc.TlsPrivateSeal\n'+''.join('#print axioms TlsMpc.TlsPrivateSeal.'+n+'\n' for n in endpoints))
    proof=subprocess.run(['lake','env','lean',str(audit)],cwd=ROOT,capture_output=True,text=True,check=True)
    (out/'proof.log').write_text(proof.stdout)
    allowed={'propext','Classical.choice','Quot.sound'}
    for line in proof.stdout.splitlines():
        if 'depends on axioms:' in line:
            found=set(re.search(r'\[(.*)\]',line).group(1).replace(' ','').split(','))
            assert found<=allowed,('unexpected proof axiom',line)
    assert 'sorryAx' not in proof.stdout and 'axiom' in proof.stdout
    checker=out/'shape-checks'
    subprocess.run(['c++','-std=c++20','-O2','-fsanitize=address,undefined',str(ROOT/'handshake_backend/kernel_shape_checks.cpp'),'-o',str(checker)],check=True)
    checked=subprocess.run([str(checker)],capture_output=True,text=True,check=True)
    for line in checked.stdout.splitlines():
        args,key,descriptor,size=line.split('|');shape=Shape(args.split())
        assert (shape.key,'Programs/Functions/'+shape.descriptor,shape.output_bytes)==(key,descriptor,int(size))
    cases=[];rng=random.Random(4051)
    for capacity in (0,1,16,257,900):
        image_path=out/f'tls-seal-private-record-{capacity}.json'
        with image_path.open('wb') as stream:
            subprocess.run([str(ROOT/'.lake/build/bin/private_tls_emitter'),'tls-seal-private-record',str(capacity)],stdout=stream,check=True)
        image=load(image_path)
        raw=[];expected=[]
        lengths=sorted(set([0,1,15,16,17,255,256,capacity,max(0,capacity-1),capacity+1,65535]))
        for length in lengths:
            for validity in (0,254,255):
                key=rng.randbytes(16);iv=rng.randbytes(12);seq=rng.randbytes(8)
                data=rng.randbytes(capacity)
                # Include trailing zeros inside the logical application data.
                if data and 0<length<=capacity:data=data[:max(0,length-1)]+bytes(1)+data[length:]
                assert len(data)==capacity
                raw.append(key+iv+seq+bytes([validity])+length.to_bytes(2,'big')+data)
                if length<=capacity:
                    inner=data[:length]+bytes([23])+bytes(capacity-length)
                else:inner=bytes(capacity+1)
                header=b'\x17\x03\x03'+(capacity+17).to_bytes(2,'big')
                nonce=bytes(a^b for a,b in zip(iv,bytes(4)+seq))
                wire=header+AESGCM(key).encrypt(nonce,inner,header)
                expected.append(bytes([255 if validity==255 and length<=capacity else 0])+wire)
        actual=evaluate_lanes(image,raw)
        assert actual==expected,capacity
        cases.append({'capacity':capacity,'cases':len(raw),'statistics':statistics(image),'artifact_sha256':digest(image_path)})
        print('Private TLS oracle passed capacity',capacity,'cases',len(raw),flush=True)
    sources=[ROOT/'TlsMpc/TlsPrivateSeal.lean',work/'EmitPrivateTls.lean',ROOT/'handshake_backend/KernelShape.h',ROOT/'scripts/prepare_tls_shape.py',Path(__file__),ROOT/'lakefile.toml']
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'passed':True,'kernel_endpoints':endpoints,
            'cases':cases,'total_oracle_cases':sum(c['cases'] for c in cases),'cpp_python_shapes':checked.stderr.strip(),
            'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sources},'emitter_sha256':digest(ROOT/'.lake/build/bin/private_tls_emitter'),
            'native_mpc_executed':False,'private_length_opened':False,
            'scope':'compiled numeric private-length TLS seal matches independent AESGCM and proved concrete placement; native status-release boundary tested separately'}
    (ROOT/'benchmarks/results/tls-private-seal-checks.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
