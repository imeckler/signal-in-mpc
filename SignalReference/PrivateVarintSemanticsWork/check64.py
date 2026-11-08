#!/usr/bin/env python3
"""Total actual uint64/private uint32+uint64 numeric varint refinement."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 prior=json.loads((HERE/'report.json').read_text());assert prior['kernel_endpoints']==19 and prior['foundation_axioms_only']
 for name,digest in prior['source_sha256'].items():assert sha(ROOT/name)==digest,name
 audit=subprocess.check_output([sys.executable,str(ROOT/'.deps/run-signal-lean.py'),'PrivateVarintSemanticsWork/Reference64','PrivateVarintSemanticsWork/Checks64'],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==11,audit
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'},audit
 assert 'sorryAx' not in audit and '_native' not in audit;(HERE/'axioms64.txt').write_text(audit)
 files=[Path(__file__),HERE/'Reference64.lean',HERE/'Checks64.lean',HERE/'report.json']
 report={'kernel_endpoints':11,'foundation_axioms_only':True,'native_reflection_used':False,'domain':'Every uint32 and uint64 value; no acceptance/public-width preconditions on total wire or total numeric artifact endpoints.',
 'proved':'Full private uint64 varint wire equals actual selected prost encoder bytes, exact private BE16 length,255validity and zero capacity padding. Total numeric uint32+uint64 artifacts refine actual encoder bytes, not just the executable varint model.',
 'trust_boundary':'Existing exact reviewed prost metadata selection, unchanged actual retained Rust bodies, official pinned Aeneas standard models and translator correctness. This does not close whole SS/HMAC/AES/session refinement.',
 'prior_packing_receipt_sha256':sha(HERE/'report.json'),'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files}}
 (HERE/'report64.json').write_text(json.dumps(report,indent=2)+'\n');print('11 kernel endpoints; total actual uint64 wire and total uint32+uint64 numeric artifact refinement passed')
if __name__=='__main__':main()
