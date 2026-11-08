#!/usr/bin/env python3
"""Direct carry/value proof of the private original-prefix selection."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
subprocess.run(['lake','build','TlsMpc.Signal.PrivateMessageMacSemantics'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
audit=subprocess.check_output(['lake','env','lean',str(HERE/'SemanticsChecks.lean')],cwd=ROOT,text=True)
groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)+audit.count('does not depend on any axioms')==3
for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
assert '_native'not in audit and 'sorryAx'not in audit
files=[Path(__file__),HERE/'SemanticsChecks.lean',ROOT/'TlsMpc/Signal/PrivateMessageMacSemantics.lean',ROOT/'TlsMpc/Signal/PrivateMessageMac.lean',ROOT/'TlsMpc/Signal/PrivateBufferRecordSemantics.lean']
report=dict(kernel_endpoints=3,foundation_axioms_only=True,native_reflection=False,
 proved='Actual16-bit carry/length arithmetic removesMAC8 for every9..256B wire; actual contentBuffer selects exactly originalwire.take(length-8) and canonical zero tail for arbitrary wire bytes.',
 boundary='Canonical upstream wire record; complete private-tag extraction/HMAC/source composition remains separate.',
 source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
(HERE/'semantics-report.json').write_text(json.dumps(report,indent=2)+'\n');print('3 foundation-only exact private original-prefix endpoints passed')
