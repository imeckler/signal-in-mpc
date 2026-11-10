"""Kernel-check backend-neutral value invariants, with explicit axiom audit."""
import hashlib,json,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;BASE=ROOT/'.deps/two-party-comparison'
p=HERE/'ConversionSemantics.lean'
r=subprocess.run(['lake','env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=60,check=True)
endpoints=re.findall(r"'EmpHybrid\.(\w+)' (?:depends on axioms: (\[[^\n]+\])|does not depend on any axioms)",r.stdout)
assert len(endpoints)==5 and 'sorryAx' not in r.stdout and 'native_decide' not in r.stdout
report=dict(passed=True,endpoints={name:axioms or '[]' for name,axioms in endpoints},source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='Nat/Bool value semantics only:canonical masks/range,recovery,injectivity,bit decoding. No gate/compiler or malicious backend security/uniform sampling theorem.')
(HERE/'conversion-semantics-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
