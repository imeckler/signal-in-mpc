#!/usr/bin/env python3
from pathlib import Path
import hashlib,importlib.util,json,subprocess,sys
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
spec=importlib.util.spec_from_file_location('cases',ROOT/'scripts/check_lean_signal_proto_parse.py');cases=importlib.util.module_from_spec(spec);spec.loader.exec_module(cases)
subprocess.run(['lake','build','emit_parser_v2'],cwd=H,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
exe=H/'.lake/build/bin/emit_parser_v2';pk=bytes([5])+bytes(range(32))
body=cases.field(1,pk)+cases.scalar(2,7)+cases.field(4,b'')
# Same public capacity includes valid, duplicate, and malformed messages.
base=[body,body+cases.scalar(2,9),body+cases.field(2,b''),body+cases.field(4,b'')]
size=64;wire=[]
for b in base:
 n=size-(1+len(b)+8)-2
 b+=cases.field(7,bytes(n))
 wire.append(bytes([0x34])+b+bytes(8))
assert all(len(w)==size for w in wire)
out=H/'Artifacts';out.mkdir(exist_ok=True);artifact=out/'signal-parser-v2-64.json'
with artifact.open('w') as f:subprocess.run([str(exe),'signal-protobuf-parse',str(size)],stdout=f,check=True,timeout=180)
observed=evaluate_lanes(load(artifact),wire);expected=[cases.parse(w) for w in wire]
assert observed==expected,[(o.hex(),e.hex()) for o,e in zip(observed,expected)]
report={'capacity':size,'fixture_lanes':len(wire),'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),'compiled_outputs_match':True,'native_mpc_executed':False}
(H/'artifact-report.json').write_text(json.dumps(report,indent=2)+'\n');print('4 compiled AIG fixture lanes match')
