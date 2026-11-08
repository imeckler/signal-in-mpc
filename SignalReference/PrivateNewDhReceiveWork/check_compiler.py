#!/usr/bin/env python3
"""Whole Boolean receiving pipeline numeric compiler agreement, explicit DH edge."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
subprocess.run(['lake','build','TlsMpc.Signal.PrivateNewDhReceiveProofs'],cwd=ROOT,stdout=subprocess.DEVNULL,check=True)
audit=subprocess.check_output(['lake','env','lean',str(HERE/'CompilerChecks.lean')],cwd=ROOT,text=True)
groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)+audit.count('does not depend on any axioms')==8
for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
assert 'sorryAx'not in audit and '_native'not in audit
files=[Path(__file__),HERE/'CompilerChecks.lean',ROOT/'TlsMpc/Signal/PrivateNewDhReceiveProofs.lean',ROOT/'TlsMpc/Signal/PrivateNewDhReceive.lean']
report=dict(kernel_endpoints=8,foundation_axioms_only=True,full_Boolean_pipeline_compiler_agreement=True,
 scope='Whole private parser/PQ/root-KDF/MAC/CBC/state-selection Boolean model, including malformed inputs and public shape branches. No supplied auth/PQ verification flag.',
 pending='Native mixed DH fresh-pair/agreement binding to SAME parsed remote point; numeric artifact/native full transaction interoperability; full private parser take-n/source theorem; RustCrypto/session source refinement; persistent share recovery.',
 native_DH_composition_proved=False,full_Rust_implementation_refinement=False,
 source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
(HERE/'compiler-report.json').write_text(json.dumps(report,indent=2)+'\n');print('8 foundation-only whole receiving model compiler endpoints passed')
