#!/usr/bin/env python3
"""Compile already-audited Signal receive artifacts without re-exporting them.
Public synthetic fixture harness only; no network/native MPC or security claim.
"""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_crypto import compile_and_check

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    cli=argparse.ArgumentParser(description=__doc__);cli.add_argument('profiles',nargs='+',choices=['proto-receive','chain-receive','skipped-receive']);args=cli.parse_args()
    for profile in args.profiles:
        path=ROOT/f'benchmarks/results/lean-signal-{profile}-checks.json';report=json.loads(path.read_text());report_hash=digest(path)
        for n,h in report['source_sha256'].items():assert digest(ROOT/n)==h,n
        rows=[]
        for case in report['cases']:
            prefix='protobuf-receive' if profile=='proto-receive' else profile
            shape=f"4-{case['wire_bytes']}" if profile=='skipped-receive' else str(case['wire_bytes'])
            artifact=ROOT/f'.deps/signal-{profile}-artifacts/signal-{prefix}-{shape}.json';fixture=artifact.with_name(artifact.stem+'-fixtures.json')
            assert digest(artifact)==case['artifact_sha256'];assert digest(fixture)==case['fixture_sha256']
            cases=json.loads(fixture.read_text());inputs=[bytes.fromhex(c['input']) for c in cases];outputs=[bytes.fromhex(c['output']) for c in cases]
            row={'wire_bytes':case['wire_bytes'],'artifact_sha256':digest(artifact),'fixture_sha256':digest(fixture),'mpc_compilations':[compile_and_check(artifact,inputs,outputs,n) for n in(1,16)]}
            rows.append(row);print(json.dumps({'profile':profile,**row}),flush=True)
        assert digest(path)==report_hash
        backend=ROOT/'.deps/MP-SPDZ';sources=[Path(__file__),ROOT/'scripts/check_lean_crypto.py',ROOT/'scripts/clear_circuit.py',ROOT/'test_support/circuit.py',ROOT/'programs/lean_artifact.mpc',backend/'compile.py',*sorted((backend/'Compiler').rglob('*.py'))]
        out={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'artifact_report_sha256':report_hash,'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sources},'cases':rows,'parties':5,'native_mpc_executed':False,'public_fixture_reveal_harness':True,'deployment_security_configuration_tested':False}
        (ROOT/f'benchmarks/results/lean-signal-{profile}-backend-checks.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
