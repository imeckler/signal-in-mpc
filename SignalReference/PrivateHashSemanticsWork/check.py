#!/usr/bin/env python3
"""Private SHA/HMAC semantics relative to existing primitive models, kernel-only."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateHashSemantics'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==12
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit and '_native' not in audit;(HERE/'axioms.txt').write_text(audit)
 files=[Path(__file__),HERE/'Checks.lean']+[ROOT/f'TlsMpc/Signal/{name}.lean' for name in ['PrivateHash','PrivateHashSemantics','PrivateBuffer','PrivateBufferSemantics','PrivateBufferPacking','PrivateBufferAppendSemantics','PrivateBufferLengthEncoding','PrivateBufferWireSemantics']]+[ROOT/'TlsMpc/Sha256.lean',ROOT/'TlsMpc/HmacPrepared.lean']
 report={'kernel_endpoints':12,'standard_axioms_only':True,'native_reflection_used':False,
  'capacity_domain':'Every natural capacity0..16384; all status bytes/BE16 input lengths and arbitrary capacity-byte data.',
  'actual_private_hash_padding_and_final_state_selection_proved':True,'actual_hmac_64_byte_prefix_bitlength_proved':True,
  'accepted_wire':'255 || BE16(32) || Sha256.hash/hmac(key, data.take decodedLength)',
  'rejected_wire':'35 zero bytes for non255 status, out-of-capacity length, malformed public dimensions or unsupported capacity.',
  'reference_boundary':'Existing executable Sha256.hash/hmac primitive models and prepared-key equivalence; no cryptographic-security theorem.',
  'compiler_model_agreement_endpoint_audited':True,'full_actual_rust_aeneas_refinement':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('12 kernel endpoints: actual private SHA/HMAC padding/state-selection/accepted+rejected wire semantics passed')
if __name__=='__main__':main()
