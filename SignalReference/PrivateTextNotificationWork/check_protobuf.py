#!/usr/bin/env python3
"""Exact private byte-field serialization in the text length domain."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateProtobufShortSemantics'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'ProtobufChecks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S)
 assert len(groups)+audit.count('does not depend on any axioms')==4
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in audit and '_native'not in audit
 files=[Path(__file__),HERE/'ProtobufChecks.lean',ROOT/'TlsMpc/Signal/PrivateProtobufShortSemantics.lean',ROOT/'TlsMpc/Signal/PrivateProtobuf.lean',ROOT/'TlsMpc/Signal/PrivateBufferRecordSemantics.lean']
 report=dict(kernel_endpoints=4,foundational_axioms_only=True,native_reflection=False,
  proved='Actual private uint32 encoder/BE16-to-word length conversion for all128 short lengths, general triple record append, and actual bytesField equals tag||length||payload for every canonical payload<128B fitting its declared capacity.',
  domain='sourceCapacity+4<65536; raw length<=sourceCapacity and<128. Covers both text body<=48 and DataMessage<=61 without opening lengths.',
  boundary='Canonical input record and upstream scalar/string encoding semantics remain separate; no whole application or source implementation agreement assumed.',
  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'protobuf-report.json').write_text(json.dumps(report,indent=2)+'\n');print('4 foundation-only exact private protobuf byte-field endpoints passed')
if __name__=='__main__':main()
