#!/usr/bin/env python3
"""Actual append-wire mathematical spec and compiler-link kernel audit."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateBufferWireSemantics'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==10
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit and '_native' not in audit;(HERE/'axioms.txt').write_text(audit)
 files=[Path(__file__),HERE/'Checks.lean']+[ROOT/f'TlsMpc/Signal/{name}.lean' for name in ['PrivateBuffer','PrivateBufferSemantics','PrivateBufferPacking','PrivateBufferAppendSemantics','PrivateBufferLengthEncoding','PrivateBufferWireSemantics']]
 report={'kernel_endpoints':10,'standard_axioms_only':True,'native_reflection_used':False,
  'capacity_domain':'Every natural capacity<65536; fixed input length capacity+3.',
  'all_status_and_BE16_input_values':True,'actual_appendWire_math_spec_proved':True,
  'accepted_result':'255 || canonical BE16(n+m) || left.take n ++right.take m ++zero tail',
  'acceptance':'Both computed input status bytes equal255 and n+m<=capacity; no supplied validity assumptions.',
  'rejection':'Any other status, input bound overflow, sum overflow or wrong public input dimensions produces capacity+3 zero bytes.',
  'compiler_model_agreement_endpoint_audited':True,'private_hash_semantic_refinement_proved':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('10 kernel endpoints: actual append normalization/prefix/length/rejection math spec + compiler model link passed')
if __name__=='__main__':main()
