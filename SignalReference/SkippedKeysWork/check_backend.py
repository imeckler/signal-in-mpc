#!/usr/bin/env python3
"""Compile capacity4 skipped-seed artifacts for public synthetic fixture checks."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import tarfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
sys.path.insert(0,str(ROOT))
from scripts.check_lean_crypto import compile_and_check


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    proof_path=HERE/'proof-report.json';proof=json.loads(proof_path.read_text())
    assert proof['checked_endpoints']==31 and proof['custom_axioms']==[]
    for name,want in proof['source_sha256'].items():assert digest(ROOT/name)==want,name
    fixture_path=HERE/'fixture-results.json'
    assert digest(fixture_path)==proof['fixture_report_sha256']
    fixtures=json.loads(fixture_path.read_text())['cases']
    backend=ROOT/'.deps/MP-SPDZ'
    compiler=[backend/'compile.py',*sorted((backend/'Compiler').rglob('*.py'))]
    pin_path=ROOT/'benchmarks/config/dependencies.json';pin=json.loads(pin_path.read_text())['mp_spdz']
    archive=ROOT/'.deps/mp-spdz-v0.4.4.tar.gz'
    assert digest(archive)==pin['source_archive_sha256']
    with tarfile.open(archive) as bundle:
        members={m.name.split('/',1)[1]:m for m in bundle.getmembers() if m.isfile()}
        for path in compiler:assert path.read_bytes()==bundle.extractfile(members[str(path.relative_to(backend))]).read()
    sources=[Path(__file__),proof_path,fixture_path,pin_path,ROOT/'scripts/check_lean_crypto.py',
             ROOT/'scripts/clear_circuit.py',ROOT/'test_support/circuit.py',ROOT/'programs/lean_artifact.mpc',
             ROOT/'backend_adapter/aig.py',ROOT/'backend_adapter/boolean.py',*compiler]
    snapshot={str(p.relative_to(ROOT)):digest(p) for p in sources}
    records=[]
    for mode in ['consume','insert']:
        artifact=next(a for a in proof['artifacts'] if a['mode']==mode and a['capacity']==4)
        path=ROOT/artifact['artifact'];assert digest(path)==artifact['artifact_sha256']
        rows=[r for r in fixtures if r['mode']==mode and r['capacity']==4]
        if mode=='consume':
            labels=['hit-position0','duplicates-first-wins','authentication0','authentication1','authentication254',
                    'authentication255','invalid-first-valid-second','miss','wrong-key-position0','wrong-counter-position0',
                    'validity0','validity1','validity254','validity255','hit-position3','random-hit1']
            rows=[next(r for r in rows if r['label']==label) for label in labels]
        raw=[bytes.fromhex(r['input']) for r in rows];want=[bytes.fromhex(r['output']) for r in rows]
        for batch in [1,16]:
            result=compile_and_check(path,raw,want,batch)
            assert result['bit_triples']==artifact['adapter_operations']['executed_and_gates']*batch
            records.append({'mode':mode,'artifact_sha256':digest(path),**result})
            print(json.dumps(records[-1]),flush=True)
    assert snapshot=={str(p.relative_to(ROOT)):digest(p) for p in sources}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':snapshot,
            'proof_report_sha256':digest(proof_path),'backend_pin':pin,'compiler_sources_match_pinned_archive':True,
            'compilations':records,'backend_bytecode_compiled':True,'public_clear_mpc_source_outputs_checked':True,
            'public_fixture_harness_reveals_synthetic_outputs':True,'native_mpc_executed':False,
            'actual_rust_wrapper_equivalence':False,'throughput_measured':False}
    out=HERE/'backend-report.json';out.write_text(json.dumps(report,indent=2)+'\n')
    print('backend-report.json SHA256: '+digest(out))


if __name__=='__main__':main()
