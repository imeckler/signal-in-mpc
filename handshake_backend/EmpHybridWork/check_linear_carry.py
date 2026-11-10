"""Paired frozen-stock/candidate regression for zero-AND authenticated carry."""
import hashlib,json,pathlib,sys
HERE=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(HERE))
import check_nonlinear_state as fixture
ROOT=HERE.parents[1];BASE=ROOT/'.deps/two-party-comparison'
case=json.loads((ROOT/'benchmarks/TwoPartyComparisonWork/emp-smoke-report.json').read_text())['results'][0]
fixture.BIN=BASE/'build-linear-carry-stock/emp-linear-carry';stock=fixture.run(case,31780)
# Expected stock failure is the actual nonlinear gamma check, not an adapter
# or startup failure. Keep original fixture report unchanged.
logs=[(pathlib.Path(stock['directory'])/(w+'.log')).read_text() for w in ('alice','bob')]
stock['expected_failure_observed']=all(c!=0 for c in stock['exit_codes']) and any('lambda c_gamma check failed' in s for s in logs)
stock['binary_sha256']=hashlib.sha256(fixture.BIN.read_bytes()).hexdigest()
fixture.BIN=BASE/'build-linear-carry-candidate/emp-linear-carry';candidate=fixture.run(case,31790);fault=fixture.run(case,31800,True)
report=dict(passed=stock['expected_failure_observed'] and candidate['passed'] and fault['passed'],stock=stock,candidate=candidate,retained_delta_fault=fault,source_sha256=hashlib.sha256((HERE/'linear_carry_fixture.cpp').read_bytes()).hexdigest(),candidate_binary_sha256=hashlib.sha256(fixture.BIN.read_bytes()).hexdigest(),overlay=json.loads((BASE/'linear-mask-overlay.json').read_text()),scope='Same imported AES→zero-AND two-NOT identity→AES, original first result remains private; output matches independent double-AES fixture only on corrected candidate. Retained Delta corruption still rejects. No backend security proof or erasure claim.')
target=HERE/'linear-carry-report.json';target.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=report['passed'],report=str(target))))
if not report['passed']:raise SystemExit(1)
