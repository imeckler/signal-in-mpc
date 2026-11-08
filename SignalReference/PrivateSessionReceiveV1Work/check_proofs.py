#!/usr/bin/env python3
"""Focused kernel/Hom/compiler audit; no actual full-source refinement claim."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
subprocess.run(['lake','build','TlsMpc.Signal.PrivateSessionReceiveV1Proofs'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)+audit.count('does not depend on any axioms')==10
for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
assert 'sorryAx'not in audit and '_native'not in audit
files=[Path(__file__),HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateSessionReceiveV1.lean',ROOT/'TlsMpc/Signal/PrivateSessionReceiveV1Proofs.lean'];sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
report=dict(kernel_endpoints=10,foundation_axioms_only=True,native_reflection=False,scope='Atomic finish rejection preservation, known sender/root selection preservation, all host-free model operations Hom, whole selected known/new transaction lowering, actual-private-parser composition lowering. One shared symmetric/MAC/CBC path.',whole_Hom_compiler_endpoint=True,actual_parser_composed=True,full_actual_source_refinement=False,native_MPC_executed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
(HERE/'proof-report.json').write_text(json.dumps(report,indent=2)+'\n');print('10 foundation-only preservation/Hom/whole compiler endpoints passed')
