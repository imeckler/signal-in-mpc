#!/usr/bin/env python3
"""Public clear composition of three actual numeric X25519 DAG evaluations."""
from pathlib import Path
from types import SimpleNamespace
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.NewRatchetReceiveWork.adapter import receive
from scripts.check_lean_signal_new_ratchet_receive import fixtures,expected
from scripts.check_lean_signal_dh_ratchet import wire_bits,wire_bytes
from scripts.check_lean_crypto import evaluate_lanes
from handshake_backend.field_dag import load as load_field,evaluate_clear,MODULUS
from backend_adapter.boolean import load
field_path=ROOT/'.deps/signal-dh-ratchet-artifacts/signal-dh-field.json'
boolean_path=ROOT/'.deps/signal-new-ratchet-receive-artifacts/signal-new-ratchet-receive-2-2-96.json'
field=load_field(field_path);boolean=load(boolean_path)
captured=[]
def as_field(bits,mask_high_bit=False):
    value=int.from_bytes(wire_bytes(bits),'little')
    if mask_high_bit:value&=(1<<255)-1
    return value%MODULUS
primitives=SimpleNamespace(wire_bits_to_scalar_fields=lambda b:[b[8*(i//8)+7-i%8] for i in range(256)],
    wire_bits_to_field=as_field,execute_secret=evaluate_clear,
    field_to_wire_bits=lambda x:wire_bits(x.to_bytes(32,'little')),
    execute_boolean=lambda image,inputs:captured.append(wire_bytes(inputs)))
labels=[]
for label,raw,want in fixtures():
    if label not in ('counter-0','counter-2','bad-mac-0','presence-1'):continue
    receive(field,boolean,wire_bits(raw[:1]),wire_bits(raw[1:137]),wire_bits(raw[137:169]),
        wire_bits(raw[265:297]),wire_bits(raw[297:329]),wire_bits(raw[329:361]),wire_bits(raw[361:393]),
        wire_bits(raw[393:429]),wire_bits(raw[429:]),primitives=primitives)
    assert captured[-1]==raw,label
    labels.append(label)
# Unclamped supplied entropy is clamped by adapter wiring before persistence.
raw=fixtures()[0][1];entropy=bytearray(raw[137:169]);entropy[0]|=7;entropy[31]^=192
receive(field,boolean,wire_bits(raw[:1]),wire_bits(raw[1:137]),wire_bits(entropy),wire_bits(raw[265:297]),
    wire_bits(raw[297:329]),wire_bits(raw[329:361]),wire_bits(raw[361:393]),wire_bits(raw[393:429]),wire_bits(raw[429:]),primitives=primitives)
assert captured[-1]==raw;labels.append('unclamped-entropy')
assert evaluate_lanes(boolean,captured)==[expected(r) for r in captured]
files=[Path(__file__),ROOT/'SignalReference/NewRatchetReceiveWork/adapter.py',ROOT/'SignalReference/NewRatchetReceiveWork/program.mpc',ROOT/'handshake_backend/mixed.py',ROOT/'handshake_backend/field_dag.py',ROOT/'scripts/check_lean_signal_new_ratchet_receive.py',field_path,boolean_path]
report={'public_composition_cases':labels,'field_dag_evaluations':3*len(labels),'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'all_outputs_match':True,'native_mpc_executed':False,'mixed_compiler_executed':False,'joint_randomness_runtime_tested':False,'remaining':['retained-chain selection','persistent atomic commit','SPQR evolution','native security/runtime audit']}
(ROOT/'SignalReference/NewRatchetReceiveWork/adapter-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
