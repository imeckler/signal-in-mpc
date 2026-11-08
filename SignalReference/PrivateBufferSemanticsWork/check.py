#!/usr/bin/env python3
"""Kernel-only arithmetic/endian endpoints; no native reflection whitelist."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateBufferSemantics'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==7
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit and '_native' not in audit;(HERE/'axioms.txt').write_text(audit)
 files=[Path(__file__),HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateBufferSemantics.lean',ROOT/'TlsMpc/Signal/PrivateBuffer.lean']
 report={'kernel_endpoints':7,'standard_axioms_only':True,'native_reflection_used':False,
  'proved':['Byte reassembly and BE16 encode/decode roundtrip','Decoded BE16 bit-mask integer value',
   'Actual masked ripple-adder: integer sum plus explicit overflow carry','Actual masked comparator: unsigned integer comparison',
   'Actual decoded BE16 addition/comparison for all byte inputs'],
  'bounded_kernel_enumeration':'256-byte reconstruction/value and2048 byte/bit mask cases; Boolean full-adder/borrow truth tables.',
  'general_append_prefix_shift_packing_spec_established':False,'private_hash_padding_semantics_established':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('7 kernel-only endian/actual masked arithmetic endpoints passed')
if __name__=='__main__':main()
