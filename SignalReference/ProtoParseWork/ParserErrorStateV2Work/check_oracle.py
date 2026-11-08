#!/usr/bin/env python3
"""Compare actual pinned Message::merge mutation/suffix on success AND rejection."""
from pathlib import Path
import hashlib,importlib.util,json,os,random,subprocess,sys
H=Path(__file__).resolve().parent;ROOT=H.parents[2]
spec=importlib.util.spec_from_file_location('public_cases',ROOT/'scripts/check_lean_signal_proto_parse.py');cases=importlib.util.module_from_spec(spec);spec.loader.exec_module(cases)
fixtures=[(name,w[1:-8]) for name,w in cases.fixtures() if len(w)>=9]
for tag in range(1,7):
 key=cases.vi(8*tag+(0 if tag in (2,3) else 2))
 valid=cases.scalar(tag,37) if tag in (2,3) else cases.field(tag,b'abc')
 for prefix in [b'',valid]:
  for name,tail in [('empty',b''),('truncated',b'\x80'),('fast-overflow',b'\x80'*9+b'\x02'),('slow-overflow',b'\x80'*10),('long-overflow',b'\x80'*11),('underflow',b'\x7f'),('empty-value',b'\x00')]:
   fixtures.append((f'field-{tag}-{len(prefix)}-{name}',prefix+key+tail))
  for kind in range(8):fixtures.append((f'wire-{tag}-{len(prefix)}-{kind}',prefix+cases.vi(8*tag+kind)+b'\x00'))
for depth in [0,1,99,100,101]:
 for tail in [b'',b'\x40\x80',b'\x40'+b'\x80'*10,b'\x0a\x01a',b'\x44']:
  fixtures.append((f'depth-{depth}-{tail.hex()}',b'\x3b'*depth+tail+b'\x3c'*depth))
rng=random.Random(0xE22026)
for n in range(300):fixtures.append((f'fuzz-{n}',rng.randbytes(rng.randrange(0,70))))
# All byte prefixes and suffix lengths exercise short vs contiguous fast decoding.
for n in [0,1,9,10,11,12]:
 for byte in [0,1,2,127,128,255]:fixtures.append((f'varint-{n}-{byte}',b'\x10'+b'\x80'*n+bytes([byte])))
fixtures=[(n,b) for n,b in fixtures if len(b)<=512]
print(f'{len(fixtures)} fixtures ready',flush=True)
wire='\n'.join(b.hex() for _,b in fixtures)+'\n'
env=os.environ.copy();env['RUSTC']=str(ROOT/'.deps/rust-nightly-2026-08-18/bin/rustc')
target=ROOT/'.deps/parser-error-v2-oracle-target'
subprocess.run([str(ROOT/'.deps/rust-nightly-2026-08-18/bin/cargo'),'build','--offline','--target-dir',str(target)],cwd=H/'Oracle',env=env,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print("Rust oracle built",flush=True)
actual=subprocess.run([str(target/'debug/signal-prost-parser-oracle')],input=wire,text=True,capture_output=True,check=True).stdout.splitlines()
print('Rust merge results captured',flush=True)
subprocess.run(['lake','build','numeric_parser'],cwd=H,check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print("Numeric native runner built",flush=True)
numeric=subprocess.run([str(H/'.lake/build/bin/numeric_parser')],cwd=ROOT,input=wire,text=True,capture_output=True,check=True).stdout.splitlines()
assert len(actual)==len(numeric)==len(fixtures),(len(actual),len(numeric),len(fixtures))
wrong=[{'name':name,'body':body.hex(),'prost':a,'numeric':b} for (name,body),a,b in zip(fixtures,actual,numeric) if a!=b]
report={'fixture_count':len(fixtures),'matching_count':len(fixtures)-len(wrong),'mismatches':wrong[:25],'comparison':'status, exact consumed cursor/suffix, all six Option field contents on both success and rejection','fixture_sha256':hashlib.sha256(wire.encode()).hexdigest(),'full_refinement_proved':False}
(H/'oracle-report.json').write_text(json.dumps(report,indent=2)+'\n')
assert not wrong,json.dumps(wrong[:8],indent=2)
print(f'{len(fixtures)} actual Prost error-state/suffix cases match')
