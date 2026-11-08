#!/usr/bin/env python3
"""Parse-once serialization and complete model/compiler agreement, no flags assumed."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
subprocess.run(['lake','build','TlsMpc.Signal.PrivateNewDhReceiveSplitProofs'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
audit=subprocess.check_output(['lake','env','lean',str(HERE/'SplitChecks.lean')],cwd=ROOT,text=True)
groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)+audit.count('does not depend on any axioms')==15
for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
assert 'sorryAx'not in audit and '_native'not in audit
files=[Path(__file__),HERE/'SplitChecks.lean',ROOT/'TlsMpc/Signal/PrivateNewDhReceiveSplit.lean',ROOT/'TlsMpc/Signal/PrivateNewDhReceiveSplitProofs.lean',ROOT/'TlsMpc/Signal/PrivateNewDhReceive.lean']
report=dict(kernel_endpoints=15,foundation_axioms_only=True,native_reflection=False,summary_bytes=75,
 proved='Parse-once summary extraction, exact encode/decode inverse including all64-bit fields, and decoded-summary transaction equals original whole receiving model; both parser-summary and crypto-stage compiler endpoints. Raw counter64 is preserved and explicituint32 truncation remains in the caller.',
 purpose='Avoid duplicate fullparser computation in the native point/DH/crypto composition; no repeated cryptographic computation across width profiles.',
 pending='Actual native same-parsed-point DH binding, emitted staged artifact differential and complete private receive/reply interoperability; full RustCrypto/session source and recoverable persistence remain open.',
 actual_native_pipeline_tested=False,full_RustCrypto_source_refinement=False,
 source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
(HERE/'split-report.json').write_text(json.dumps(report,indent=2)+'\n');print('15 foundation-only parse-once codec/whole-model/compiler endpoints passed')
