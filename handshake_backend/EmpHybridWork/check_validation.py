"""Reproduce the evaluator masked-value leak and check the v3 candidate rejects it.

Attack regressions and functional controls only. Passing does NOT prove
malicious security; `secure_hybrid_backend` stays false until the review items
in VALIDATION_ROUTE.md close. Fixture bits are fresh random test data.
"""
import hashlib,json,os,pathlib,re,subprocess,sys,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;BASE=ROOT/'.deps/two-party-comparison'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
DIAG,V3='lambda-diagnostic-v2','validated-v3'
def run(variant,mode,port,fault=None,value='1'):
    work=pathlib.Path(tempfile.mkdtemp(prefix='validation-',dir=BASE));bit=os.urandom(1)[0]&1;(work/'private.bin').write_bytes(bytes([bit]))
    worker=BASE/('build-'+variant)/'emp-validation-probe';logs=[];children=[];failure=None;start=time.monotonic()
    try:
        for p in (1,2):
            f=open(work/f'{p}.log','w');logs.append(f);env=dict(os.environ)
            if fault and p==2:env[fault]=value
            own=str(work/'private.bin') if p==1 else '/dev/null'
            children.append(subprocess.Popen([str(worker),str(p),str(port),mode,own],env=env,stdout=f,stderr=subprocess.STDOUT))
        deadline=start+30
        for c in children:c.wait(timeout=max(1,deadline-time.monotonic()))
    except Exception as e:failure=type(e).__name__
    finally:
        for c in children:
            if c.poll() is None:c.kill()
            c.wait()
        for f in logs:f.close()
    text=[(work/f'{p}.log').read_text() for p in (1,2)];codes=[c.returncode for c in children]
    recovered=re.findall(r'lambda_leak recovered_wire_value=(\w+)',text[1])
    return dict(variant=variant,mode=mode,fault=fault,exit_codes=codes,failure_category=failure,seconds=time.monotonic()-start,directory=str(work),binary_sha256=sha(worker),log_sha256=[sha(work/f'{p}.log') for p in (1,2)],
        accepted=[re.findall(r'output_fixture accepted_value=([01])',s) for s in text],
        # Only whether the attacker's recovered bit equals the garbler's private fixture bit is recorded.
        leak_attempted=bool(recovered),leak_matches_private_bit=recovered==[str(bit)],
        label_check_rejection='masked-value label check failed' in text[0],share_mac_rejection='peer share-MAC hash mismatch' in text[0],open_mac_rejection='authenticated open: peer MAC digest mismatch' in text[0],
        settled=all('leak_fixture settled_without_opening=1' in s for s in text))
if __name__=='__main__':
    port=iter(range(32400,33400,10));TRIALS=8
    leaks=[run(DIAG,'leak',next(port),'EMP_TEST_LAMBDA_LEAK','0,1') for _ in range(TRIALS)]
    blocked=[run(V3,'leak',next(port),'EMP_TEST_LAMBDA_LEAK','0,1') for _ in range(TRIALS)]
    honest_leak=run(V3,'leak',next(port));false_gamma=run(V3,'and-A',next(port),'EMP_TEST_FALSE_GAMMA')
    a,b,p=run(V3,'and-A',next(port)),run(V3,'and-B',next(port)),run(V3,'and-P',next(port))
    share_lie_a=run(V3,'and-A',next(port),'EMP_TEST_OUTPUT_SHARE_LIE');share_lie_p=run(V3,'and-P',next(port),'EMP_TEST_OUTPUT_SHARE_LIE')
    open_lie=run(V3,'and-A',next(port),'EMP_TEST_OPEN_LIE')
    public=run(V3,'public',next(port));public_lie=run(V3,'public',next(port),'EMP_TEST_OUTPUT_SHARE_LIE')
    rejected=lambda r:all(x!=0 for x in r['exit_codes'])
    assertions=dict(
        input_repair_only_leaks_garbler_wire_value=all(r['exit_codes']==[0,0] and r['settled'] and r['leak_matches_private_bit'] for r in leaks),
        v3_false_masked_value_rejected_before_digest=all(rejected(r) and r['label_check_rejection'] and not r['leak_attempted'] and not r['settled'] for r in blocked),
        v3_honest_two_gate_chunk_passes=honest_leak['exit_codes']==[0,0] and honest_leak['settled'],
        v3_false_gamma_rejected=rejected(false_gamma) and false_gamma['label_check_rejection'] and false_gamma['accepted']==[[],[]],
        v3_triple_generation_false_opening_rejected=rejected(open_lie) and open_lie['open_mac_rejection'] and open_lie['accepted']==[[],[]],
        v3_honest_A_output=a['exit_codes']==[0,0] and a['accepted']==[['1'],[]],
        v3_honest_B_output=b['exit_codes']==[0,0] and b['accepted']==[[],['1']],
        v3_honest_PUBLIC_output=p['exit_codes']==[0,0] and p['accepted']==[['1'],['1']],
        v3_A_output_share_lie_rejected=rejected(share_lie_a) and share_lie_a['share_mac_rejection'] and share_lie_a['accepted'][0]==[],
        # No fairness: B legitimately holds its own (correct) value before A rejects.
        v3_PUBLIC_share_lie_rejected_at_A=share_lie_p['exit_codes'][0]!=0 and share_lie_p['share_mac_rejection'] and share_lie_p['accepted'][0]==[] and share_lie_p['accepted'][1] in ([],['1']),
        v3_honest_PUBLIC_without_nonlinear_chunk=public['exit_codes']==[0,0] and public['accepted']==[['1'],['1']],
        v3_PUBLIC_input_share_lie_rejected_at_A=public_lie['exit_codes'][0]!=0 and public_lie['share_mac_rejection'] and public_lie['accepted'][0]==[])
    sys.path.insert(0,str(ROOT/'benchmarks/TwoPartyComparisonWork'));import run_modern_smoke as smoke
    smoke.WORKER=BASE/('build-'+V3)/'modern-worker';cases=json.loads((ROOT/'benchmarks/TwoPartyComparisonWork/emp-smoke-report.json').read_text())['results'][:2]
    components=[smoke.run(cases[0],next(port)),smoke.run(cases[1],next(port))]
    # Two nonlinear calls consuming carried authenticated state, plus retained-key corruption.
    sys.path.insert(0,str(HERE));import check_nonlinear_state as nonlinear
    nonlinear.BIN=BASE/('build-'+V3)/'emp-nonlinear-state';components+=[nonlinear.run(cases[0],next(port)),nonlinear.run(cases[0],next(port),True)]
    # Zero-AND carry between two nonlinear calls, and its retained-key fault.
    nonlinear.BIN=BASE/('build-'+V3)/'emp-linear-carry';components+=[nonlinear.run(cases[0],next(port)),nonlinear.run(cases[0],next(port),True)]
    # Tiny kernel padded to 1024 checked ANDs, and its corrupted-key fault.
    import check_padding as padding
    padding.BIN=BASE/('build-'+V3)/'emp-padded-kernel';components+=[padding.run(next(port),False),padding.run(next(port),True)]
    # Earlier input-boundary regressions, re-pointed at v3.
    import check_input_boundary as boundary
    i1,i2,i3,i4=boundary.run(V3,'input',next(port)),boundary.run(V3,'input',next(port),'EMP_TEST_NONCANONICAL_SHARE'),boundary.run(V3,'bob-input',next(port),'EMP_TEST_NONCANONICAL_INPUT'),boundary.run(V3,'gamma',next(port))
    assertions.update(
        v3_owner_only_input_regression=i1['exit_codes']==[0,0] and i1['all_inputs_settled'] and i1['observed_peer_masked_nonmatch'] and not i1['observed_peer_clear_match'],
        v3_malformed_mask_share_rejected=rejected(i2) and i2['canonical_rejection'] and not i2['all_inputs_settled'],
        v3_malformed_Gamma_rejected=rejected(i3) and i3['canonical_rejection'] and not i3['all_inputs_settled'],
        v3_boundary_probe_honest_A_output=i4['exit_codes']==[0,0] and i4['accepted'][0]==['1'])
    boundary_results=[i1,i2,i3,i4]
    ok=all(assertions.values()) and all(r['passed'] for r in components)
    report=dict(regressions_passed=ok,secure_hybrid_backend=False,assertions=assertions,
        results=dict(leaks=leaks,blocked=blocked,honest_leak=honest_leak,false_gamma=false_gamma,open_lie=open_lie,and_A=a,and_B=b,and_P=p,share_lie_A=share_lie_a,share_lie_P=share_lie_p,public=public,public_lie=public_lie),
        components=components,boundary_results=boundary_results,source_variants=json.loads((BASE/'validation-v3-build-source.json').read_text()),probe_source_sha256=sha(HERE/'validation_probe.cpp'),
        scope='Reproduces a malicious-evaluator wire-value leak that survives the input-only repair, and exercises the v3 label check and directed outputs. Regression evidence for an unaudited candidate; not a security proof. Preprocessing, parameters and lifecycle remain unreviewed.')
    (HERE/'validation-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(regressions_passed=ok,secure_hybrid_backend=False,assertions=assertions,components=[r['passed'] for r in components])))
    if not ok:raise SystemExit(1)
