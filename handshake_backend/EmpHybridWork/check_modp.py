"""Independent finite arithmetic model for the exact fixed mod-p gate builder.
C++ fixture emits/evaluates actual builder; Python bigint supplies expected values.
"""
import hashlib,json,pathlib,random,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';HERE=pathlib.Path(__file__).resolve().parent
source=HERE/'modp_program_test.cpp';binary=BASE/'modp-program-test'
subprocess.run(['c++','-std=c++20','-O2','-I/opt/homebrew/include','-I'+str(BASE/'modern-install/include'),str(source),'-o',str(binary)],check=True)
p=2**255-19;rng=random.Random(7122);cases=[(r,c) for r in [0,1,18,19,p-1,p,p+1,2**255-1] for c in [0,1,18,p-1]]
cases += [(rng.randrange(2**255),rng.randrange(p)) for _ in range(128)]
wire=''.join(f'{r:x} {c:x}\n' for r,c in cases)
out=subprocess.run([str(binary)],input=wire,text=True,capture_output=True,check=True).stdout.splitlines()
assert len(out)==len(cases)
for (r,c),line in zip(cases,out):
    valid,value=map(lambda x:int(x,16),line.split());assert valid==int(r<p)
    # No accepted conversion may use r>=p; still check builder's bounded sum.
    assert value==(r+c if r+c<p else r+c-p)
report=dict(passed=True,cases=len(cases),scope='Actual C++ range/modp gate builder versus Python bigints. No Lean theorem or native field conversion claim.',sources={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [source,HERE/'modp_program.h']})
(HERE/'modp-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
