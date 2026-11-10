"""Reproduce known privacy/correctness failures, not a secure-backend benchmark."""
import hashlib,json,os,pathlib,re,subprocess,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;BASE=ROOT/'.deps/two-party-comparison'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def run(variant,mode,port,fault=None):
    work=pathlib.Path(tempfile.mkdtemp(prefix='input-boundary-',dir=BASE));private=bytes((b>>i)&1 for b in os.urandom(32) for i in range(7,-1,-1));(work/'private.bin').write_bytes(private)
    target=hashlib.sha256(private).hexdigest();worker=BASE/('build-'+variant)/'emp-input-boundary-probe';logs=[];children=[];failure=None;start=time.monotonic()
    try:
        for p in (1,2):
            f=open(work/f'{p}.log','w');logs.append(f);env=dict(os.environ)
            if mode=='input':env['EMP_HYBRID_OBSERVE_INPUT_HASH']=target
            if fault and p==2:env[fault]='1'
            owner=2 if mode=='bob-input' else 1
            own=str(work/'private.bin') if p==owner else '/dev/null'
            children.append(subprocess.Popen([str(worker),str(p),str(port),mode,own],env=env,stdout=f,stderr=subprocess.STDOUT))
        deadline=start+20
        for c in children:c.wait(timeout=max(1,deadline-time.monotonic()))
    except Exception as e:failure=type(e).__name__
    finally:
        for c in children:
            if c.poll() is None:c.kill()
            c.wait()
        for f in logs:f.close()
    text=[(work/f'{p}.log').read_text() for p in (1,2)];codes=[c.returncode for c in children]
    return dict(variant=variant,mode=mode,fault=fault,exit_codes=codes,failure_category=failure,seconds=time.monotonic()-start,directory=str(work),binary_sha256=sha(worker),log_sha256=[sha(work/f'{p}.log') for p in (1,2)],observed_peer_clear_match='input_observer recovered_peer_input=1' in text[1],observed_peer_masked_nonmatch='input_observer recovered_peer_input=0' in text[1],accepted=[re.findall(r'output_fixture accepted_value=([01])',s) for s in text],public_gate=any('two-sided opening gated' in s for s in text),canonical_rejection=any('noncanonical peer' in s for s in text),all_inputs_settled=all('input_fixture settled_without_opening=1' in s for s in text))
if __name__=='__main__':
    results=[run('input-diagnostic-v1','input',32300),run('input-diagnostic-v1','public',32310,'EMP_TEST_PUBLIC_LIE'),run('input-diagnostic-v1','gamma',32320),run('input-diagnostic-v1','gamma',32330,'EMP_TEST_FALSE_GAMMA'),run('private-input-v2','input',32340),run('private-input-v2','public',32350),run('private-input-v2','input',32360,'EMP_TEST_NONCANONICAL_SHARE'),run('private-input-v2','bob-input',32370,'EMP_TEST_NONCANONICAL_INPUT')]
    a,b,c,d,e,f,g,h=results
    assertions=dict(stock_clear_input_leak_reproduced=a['exit_codes']==[0,0] and a['observed_peer_clear_match'],stock_public_plaintext_lie_accepted=b['exit_codes']==[0,0] and b['accepted']==[['0'],['1']],stock_honest_A_output_correct=c['exit_codes']==[0,0] and c['accepted'][0]==['1'],stock_false_Gamma_accepted=d['exit_codes']==[0,0] and d['accepted'][0]==['0'],owner_only_input_regression=e['exit_codes']==[0,0] and e['all_inputs_settled'] and e['observed_peer_masked_nonmatch'],unsupported_public_failclosed=all(x!=0 for x in f['exit_codes']) and f['public_gate'] and f['accepted']==[[],[]],malformed_mask_share_rejected=all(x!=0 for x in g['exit_codes']) and g['canonical_rejection'] and not g['all_inputs_settled'],malformed_Gamma_rejected=all(x!=0 for x in h['exit_codes']) and h['canonical_rejection'] and not h['all_inputs_settled'])
    # Functional imported AES/SHA controls use B-only openings, which the input
    # repair profile supports; they DO NOT validate all malicious security.
    import sys;sys.path.insert(0,str(ROOT/'benchmarks/TwoPartyComparisonWork'));import run_modern_smoke as smoke
    smoke.WORKER=BASE/'build-private-input-v2/modern-worker';cases=json.loads((ROOT/'benchmarks/TwoPartyComparisonWork/emp-smoke-report.json').read_text())['results'][:2]
    components=[smoke.run(cases[0],32380),smoke.run(cases[1],32390)]
    report=dict(diagnostics_completed=all(assertions.values()) and all(r['passed'] for r in components),secure_hybrid_backend=False,assertions=assertions,results=results,components=components,source_variants=json.loads((BASE/'input-fix-build-source.json').read_text()),probe_source_sha256=sha(HERE/'input_boundary_probe.cpp'),scope='Known vulnerabilities reproduced in pinned unaudited EMP rewrite. Input-only repair removes direct raw-input transmission and rejects unsupported PUBLIC/A outputs; full validation/security/bridge acceptance remains blocked. No private input bytes are logged; receiver reports only match against a public256-bit commitment.')
    target=HERE/'input-boundary-report.json';target.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(diagnostics_completed=report['diagnostics_completed'],secure_hybrid_backend=False,assertions=assertions)))
    if not report['diagnostics_completed']:raise SystemExit(1)
