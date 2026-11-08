#!/usr/bin/env python3
"""Kernel audit for actual oblivious barrel-shift semantic endpoints."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateBufferPacking'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==4
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit and '_native' not in audit;(HERE/'axioms.txt').write_text(audit)
 files=[Path(__file__),HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateBufferPacking.lean',ROOT/'TlsMpc/Signal/PrivateBufferSemantics.lean',ROOT/'TlsMpc/Signal/PrivateBuffer.lean']
 report={'kernel_endpoints':4,'standard_axioms_only':True,'native_reflection_used':False,
  'actual_shiftLoop_decoded_BE16_integer_shift_proved':True,'all_lengths_all_capacities':True,
  'full_append_normalization_prefix_concat_theorem':False,'private_hash_padding_semantic_refinement':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('4 actual barrel-shift kernel endpoints passed')
if __name__=='__main__':main()
