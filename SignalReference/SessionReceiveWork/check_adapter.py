#!/usr/bin/env python3
"""Public composition of numeric parser, three X25519 DAGs and session transaction."""
from pathlib import Path
from types import SimpleNamespace
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.SessionReceiveWork.adapter import receive
from scripts.check_lean_signal_session_receive import fixtures,expected
from scripts.check_lean_signal_proto_parse import parse,oracle_view
from scripts.check_lean_signal_dh_ratchet import wire_bits,wire_bytes
from scripts.check_lean_crypto import evaluate_lanes
from handshake_backend.field_dag import load as load_field,evaluate_clear,MODULUS
from backend_adapter.boolean import load
field_path=ROOT/'.deps/signal-dh-ratchet-artifacts/signal-dh-field.json'
parser_path=ROOT/'SignalReference/SessionReceiveWork/Artifacts/parser-96.json'
session_path=ROOT/'.deps/signal-session-receive-artifacts/signal-session-receive-2-5-2-96.json'
field=load_field(field_path);parser=load(parser_path);session=load(session_path)
all_cases=fixtures();wires=[raw[1464:] for _,raw,_ in all_cases];parsed=evaluate_lanes(parser,wires)
assert parsed==[parse(w) for w in wires]
oracle=ROOT/'.deps/signal-prost-oracle-target/debug/signal-prost-parser-oracle'
observed=subprocess.run([str(oracle)],input=''.join(w[1:-8].hex()+'\n' for w in wires),capture_output=True,text=True,check=True).stdout.splitlines()
assert observed==[oracle_view(w[1:-8]) for w in wires]
parsed_by_wire=dict(zip(wires,parsed));captured=[]
def execute_boolean(image,inputs):
    if image is parser:return wire_bits(parsed_by_wire[wire_bytes(inputs)])
    assert image is session
    captured.append(wire_bytes(inputs));return []
def as_field(bits,mask_high_bit=False):
    value=int.from_bytes(wire_bytes(bits),'little')
    if mask_high_bit:value&=(1<<255)-1
    return value%MODULUS
primitives=SimpleNamespace(wire_bits_to_scalar_fields=lambda b:[b[8*(i//8)+7-i%8] for i in range(256)],
    wire_bits_to_field=as_field,execute_secret=evaluate_clear,field_to_wire_bits=lambda x:wire_bits(x.to_bytes(32,'little')),execute_boolean=execute_boolean)
labels=[];wanted=[]
for label,raw,want in all_cases:
    if label not in ('new-counter-0','new-counter-0-full','new-counter-2','new-bad-mac-0','retained-target-7','retained-bad-mac-target-7'):continue
    receive(field,parser,session,wire_bits(raw[:1]),wire_bits(raw[1:137]),wire_bits(raw[429:1464]),wire_bits(raw[137:169]),
        wire_bits(raw[297:329]),wire_bits(raw[329:361]),wire_bits(raw[361:393]),wire_bits(raw[393:429]),wire_bits(raw[1464:]),primitives=primitives)
    assert captured[-1][265:297]==parse(raw[1464:])[1:33]
    wanted.append(want);labels.append(label)
assert [expected(r) for r in captured]==wanted
assert evaluate_lanes(session,captured)==wanted
files=[Path(__file__),ROOT/'SignalReference/SessionReceiveWork/adapter.py',ROOT/'SignalReference/SessionReceiveWork/program.mpc',ROOT/'SignalReference/NewRatchetReceiveWork/adapter.py',ROOT/'handshake_backend/mixed.py',ROOT/'handshake_backend/field_dag.py',ROOT/'scripts/check_lean_signal_session_receive.py',ROOT/'scripts/check_lean_signal_proto_parse.py',ROOT/'SignalReference/ProtoParseWork/Oracle/src/main.rs',oracle,field_path,parser_path,session_path]
report={'public_composition_cases':labels,'field_dag_evaluations':3*len(labels),'parser_numeric_and_prost_cases':len(wires),'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'all_outputs_match':True,'native_mpc_executed':False,'mixed_compiler_executed':False,'joint_randomness_runtime_tested':False,'all_session_outputs_remain_shared':True,'remaining':['SPQR evolution/KEM','persistent atomic commit/refresh/erasure','native security/runtime audit']}
(ROOT/'SignalReference/SessionReceiveWork/adapter-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
