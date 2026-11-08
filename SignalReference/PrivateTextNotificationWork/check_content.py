#!/usr/bin/env python3
"""Composed bounded app wire plus actual prost timestamp bytes, no validity slots."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 prior=ROOT/'SignalReference/PrivateVarintSemanticsWork/report64.json';receipt=json.loads(prior.read_text())
 assert receipt['kernel_endpoints']==11 and receipt['foundation_axioms_only']
 for name,digest in receipt['source_sha256'].items():assert sha(ROOT/name)==digest,name
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateTextNotificationContentSemantics'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
 audit=subprocess.check_output([sys.executable,str(ROOT/'.deps/run-signal-lean.py'),'PrivateTextNotificationWork/Reference','PrivateTextNotificationWork/ContentChecks'],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S)
 assert len(groups)+audit.count('does not depend on any axioms')==7,audit
 for group in groups:assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in audit and '_native'not in audit
 files=[Path(__file__),HERE/'ContentChecks.lean',HERE/'Reference.lean',ROOT/'TlsMpc/Signal/PrivateTextNotificationContentSemantics.lean',ROOT/'TlsMpc/Signal/PrivateProtobufShortSemantics.lean',ROOT/'TlsMpc/Signal/PrivateTextNotificationSemantics.lean',prior]
 report=dict(kernel_endpoints=7,foundational_axioms_only=True,native_reflection=False,
  proved='Canonical private text-only DataMessage/body/timestamp, nested Content and80BISO7816 append composition. Top timestamp/source endpoints quantify alluint64 values and equate timestamp payload bytes to actual pinned prost encode_varint Vec writes.',
  width_input_or_acceptance_precondition=False,actual_timestamp_encoder_linked=True,
  domain='Canonical private body record<=48B; arbitrary uint64 timestamp; successful bounded Vec allocation/capacity from existing model.',
  boundary='Actual DataMessage/Content derive/full source agreement, strictUTF8 semantic language refinement, complete builder-input record refinement, and full cryptographic/session refinement remain separate. Existing official Aeneas/exact metadata-selection content models and translator are trusted.',
  prior_actual_varint_receipt_sha256=sha(prior),
  source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'content-report.json').write_text(json.dumps(report,indent=2)+'\n');print('7 foundation-only Content/padding composition and actual prost timestamp endpoints passed')
if __name__=='__main__':main()
