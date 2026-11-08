#!/usr/bin/env python3
"""Actual padding expression semantics, explicit upstream canonicality boundary."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def main():
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateTextNotificationSemantics'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'PaddingChecks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S)
 assert len(groups)+audit.count('does not depend on any axioms')==5
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in audit and '_native'not in audit
 files=[Path(__file__),HERE/'PaddingChecks.lean',ROOT/'TlsMpc/Signal/PrivateTextNotificationSemantics.lean',ROOT/'TlsMpc/Signal/PrivateBufferRecordSemantics.lean',ROOT/'TlsMpc/Signal/PrivateTextNotification.lean']
 report=dict(kernel_endpoints=5,foundational_axioms_only=True,native_reflection=False,
  proved='Actual join/append padding preserves canonical Content payload, appends0x80, zero-fills public80-byte bucket and succeeds for every payload<80B.',
  boundary='Preceding Content buffer equals canonical ofContents record. Full actual protobuf/UTF8 refinement remains separate, not assumed by a success flag.',
  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'padding-report.json').write_text(json.dumps(report,indent=2)+'\n');print('5 foundation-only exact padding semantics endpoints passed')
if __name__=='__main__':main()
