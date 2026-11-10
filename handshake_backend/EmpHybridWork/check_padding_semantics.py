"""Kernel-check the padding original-output theorem, with explicit axiom audit."""
import hashlib,json,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
p=HERE/'PaddingSemantics.lean'
r=subprocess.run(['lake','env','lean',str(p)],cwd=ROOT,capture_output=True,text=True,timeout=300,check=True)
endpoints=re.findall(r"'EmpHybrid\.Padding\.(\w+)' (?:depends on axioms: (\[[^\n]+\])|does not depend on any axioms)",r.stdout)
allowed={'propext','Quot.sound','Classical.choice'}
assert len(endpoints)==2 and 'sorryAx' not in r.stdout and 'native_decide' not in r.stdout
for _,axioms in endpoints:assert set(re.findall(r'[\w.]+',axioms or ''))<=allowed
report=dict(passed=True,endpoints={name:axioms or '[]' for name,axioms in endpoints},source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),pad_program_sha256=hashlib.sha256((HERE/'pad_program.h').read_bytes()).hexdigest(),scope='Value semantics of a hand-written Lean model of pad_program.h (dense SSA, And/Xor/Not/Const, any dummy count): the first original_outputs outputs of the padded program equal the original outputs for every dummy-input assignment. The model mirrors the C++ by inspection, not extraction. No statement about backend checks, dummy-input secrecy or pruning.')
(HERE/'padding-semantics-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
