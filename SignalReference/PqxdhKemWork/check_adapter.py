#!/usr/bin/env python3
"""KEM/DH/KDF handoff: native-Rust KEM boundary, actual numeric DH/KDF/wire circuits.

The full numeric KEM stage is independently tested in MlKemWork. This test
explicitly supplies native fixture outputs at that stage boundary, not a claim
of native MPC execution or a proof of identity/prekey validation.
"""
import hashlib,json,subprocess,sys
from pathlib import Path
from types import SimpleNamespace
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.PqxdhKemWork.adapter import initiate,accept
from SignalReference.PqxdhWork.check import oracle as derive
from scripts.check_lean_signal_dh_ratchet import wire_bits,wire_bytes
from handshake_backend.field_dag import load as load_field,evaluate_clear,MODULUS
from backend_adapter.boolean import load,execute
from scripts.check_lean_signal_ratchet_step import digest

def main():
    directory=ROOT/'SignalReference/PqxdhWork/Artifacts/Export';field_path=directory/'signal-dh-field.json';field=load_field(field_path)
    native=ROOT/'.deps/signal-libcrux-mlkem-oracle-target/debug/signal-libcrux-mlkem-oracle';seed=bytes(range(64));entropy=bytes(range(32))
    native_response=subprocess.run([str(native)],input=f'kyber1024|{seed.hex()}|{entropy.hex()}\n',text=True,capture_output=True,check=True)
    sk,pk,ct,ss,recovered=map(bytes.fromhex,native_response.stdout.strip().split('|'));assert ss==recovered
    keys=[hashlib.sha256(b'PQXDH KEM handoff'+bytes([i])).digest() for i in range(5)]
    private=[X25519PrivateKey.from_private_bytes(k) for k in keys];public=[k.public_key().public_bytes_raw() for k in private]
    identity,ephemeral,remote,signed,one_time=map(wire_bits,keys)
    def as_field(bits,mask_high_bit=False):
        value=int.from_bytes(wire_bytes(bits),'little')
        if mask_high_bit:value&=(1<<255)-1
        return value%MODULUS
    field_calls=[]
    def run_field(image,inputs):field_calls.append(1);return evaluate_clear(image,inputs)
    primitives=SimpleNamespace(wire_bits_to_scalar_fields=lambda b:[b[8*(i//8)+7-i%8] for i in range(256)],wire_bits_to_field=as_field,execute_secret=run_field,field_to_wire_bits=lambda x:wire_bits(x.to_bytes(32,'little')),execute_boolean=lambda image,bits:execute(image,bits,0,1))
    wirepaths={mode:ROOT/f'.deps/signal-kem-wire-artifacts/signal-kem-wire-{mode}-kyber1024.json' for mode in ('encapsulate','decapsulate')};wires={mode:load(p) for mode,p in wirepaths.items()}
    rows=[]
    class Boundary:
        rank=4;du=11;dv=5;kyber=True
        status=255
        def encapsulate(self,bits):assert wire_bytes(bits)==pk+entropy;return wire_bits(bytes([self.status])+ct+ss)
        def decapsulate(self,bits):assert wire_bytes(bits)==sk+ct;return wire_bits(bytes([self.status])+ss)
    for present in (False,True):
        profile='present' if present else 'none';kdf=load(directory/f'signal-pqxdh-{profile}.json')
        agreements=[private[0].exchange(private[3].public_key()),private[1].exchange(private[2].public_key()),private[1].exchange(private[3].public_key())]+([private[1].exchange(private[4].public_key())] if present else [])
        derived=derive(agreements[:3]+([agreements[3]] if present else [b''])+[ss])
        for label,tag,status,validation,null_dh in [('valid',8,255,255,False),('wrong-tag',10,255,255,False),('kem-abort',8,0,255,False),('validation0',8,255,0,False),('validation1',8,255,1,False),('null-dh',8,255,255,True)]:
            kem=Boundary();kem.status=status;valid=label=='valid'
            incoming=wire_bits(bytes([tag])+pk)
            got=wire_bytes(initiate(kem,wires['encapsulate'],field,kdf,identity,ephemeral,wire_bits(public[2]),wire_bits(bytes(32) if null_dh else public[3]),wire_bits(public[4]) if present else None,incoming,wire_bits(entropy),wire_bits(bytes([validation])),primitives=primitives))
            want=b'\xff'+derived+b'\x08'+ct if valid else bytes(97+1+len(ct));assert got==want,(profile,label,'initiate')
            got=wire_bytes(accept(kem,wires['decapsulate'],field,kdf,remote,signed,one_time if present else None,wire_bits(public[0]),wire_bits(bytes(32) if null_dh else public[1]),wire_bits(b'\x08'+sk),wire_bits(bytes([tag])+ct),wire_bits(bytes([validation])),primitives=primitives))
            want=b'\xff'+derived if valid else bytes(97);assert got==want,(profile,label,'accept')
            rows.append({'one_time':present,'case':label,'initiator_recipient_match':True})
    sources=[Path(__file__),ROOT/'SignalReference/PqxdhKemWork/adapter.py',ROOT/'SignalReference/MlKemWork/adapter.py',ROOT/'SignalReference/PqxdhWork/check.py',field_path,*wirepaths.values(),directory/'signal-pqxdh-none.json',directory/'signal-pqxdh-present.json',ROOT/'SignalReference/MlKemPkeWork/Oracle/src/main.rs']
    report={'cases':rows,'numeric_dh_evaluations':len(field_calls),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sources},'all_outputs_match':True,'kem_stage':'native pinned Rust fixture boundary; full numeric stage independently checked in MlKemWork/adapter-report.json','numeric_wire_and_kdf_executed':True,'native_mpc_executed':False,'identity_prekey_validation_implemented':False,'signature_validation_status_is_explicit_shared_input':True}
    (ROOT/'SignalReference/PqxdhKemWork/adapter-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
