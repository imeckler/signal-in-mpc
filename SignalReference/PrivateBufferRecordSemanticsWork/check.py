#!/usr/bin/env python3
"""Record-level arithmetic/resize/append semantics, all16-bit lengths."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateBufferRecordSemantics'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True);groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)+audit.count('does not depend on any axioms')==10,audit
 for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'},audit
 assert 'sorryAx'not in audit and '_native'not in audit;(HERE/'axioms.txt').write_text(audit)
 files=[Path(__file__),HERE/'Checks.lean']+[ROOT/f'TlsMpc/Signal/{n}.lean'for n in ['PrivateBufferRecordSemantics','PrivateBuffer','PrivateBufferSemantics','PrivateBufferPacking','PrivateBufferAppendSemantics','PrivateBufferLengthEncoding','PrivateBufferWireSemantics']]
 report={'kernel_endpoints':10,'foundation_axioms_only':True,'native_reflection_used':False,
 'proved':'Canonical16-mask encode/decode inverse and exact publicLength addition for all sums<65536; general source-capacity resize; actual record append equals ordered payload concatenation and canonical summed length, including empty payloads.',
 'domain':'Every targetcapacity<65536, arbitrary payloads/sourcecapacities with totalpayloadlength<=targetcapacity. Semantic length witnesses are proof parameters, never public circuit/host inputs.',
 'remaining':'Private protobuf/base64/decimal composition and full actual cryptographic/session implementation agreement are separate.',
 'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('10 kernel endpoints; general record add/resize/append contents semantics passed')
if __name__=='__main__':main()
