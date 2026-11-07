#!/usr/bin/env python3
"""Compile frozen session/store/KEM-hash artifacts and check public fixture execution."""
import hashlib,json,sys,os,re,shutil,subprocess
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_crypto import execute_mpc_source,input_tokens

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def compile_and_check(path, raw, expected, batch):
    backend = ROOT / '.deps/MP-SPDZ'
    copied = backend / 'Programs/Source/lean-artifacts'
    copied.mkdir(parents=True, exist_ok=True)
    shutil.copy2(path, copied / path.name)
    source = ROOT / 'programs/lean_artifact.mpc'
    shutil.copy2(source, backend / 'Programs/Source/lean_artifact.mpc')
    args = [path.stem, str(batch), '5']
    program = 'lean_artifact-' + '-'.join(args)
    environment = os.environ.copy()
    environment['PYTHONPATH'] = str(ROOT) + os.pathsep + environment.get('PYTHONPATH', '')
    compiled = subprocess.run([sys.executable, './compile.py', '-M', '-B', '128', 'lean_artifact', *args],
                              cwd=backend, env=environment, capture_output=True, text=True, timeout=1800)
    logs = ROOT / 'benchmarks/results/raw' / program
    logs.mkdir(parents=True, exist_ok=True)
    log = compiled.stdout + compiled.stderr
    (logs / 'compile.log').write_text(log)
    if compiled.returncode:
        raise RuntimeError(log[-4000:])
    inputs = [raw[i % len(raw)] for i in range(batch)]
    outputs = [expected[i % len(expected)] for i in range(batch)]
    values = [int.from_bytes(x[offset:offset + 8], 'big')
              for offset in range(0, len(outputs[0]), 8) for x in outputs]
    previous = Path.cwd()
    try:
        os.chdir(backend)
        observed = execute_mpc_source(source, backend / 'Programs/Circuits', ['lean_artifact', *args],
                                      input_tokens({'raw': inputs}))
    finally:
        os.chdir(previous)
    if observed != values:
        raise AssertionError(f'MPC-source fixture mismatch: {program}')
    triples = re.findall(r'(\d+) bit triples', log)
    return {'batch': batch, 'parties': 5, 'bit_triples': int(triples[-1]) if triples else 0,
            'fixture_output_values_checked': len(values),
            'bytecode_sha256': hashlib.sha256((backend / f'Programs/Bytecode/{program}-0.bc').read_bytes()).hexdigest()}


def main():
    rows=[];snapshots={}
    profiles=[('session-receive','signal-session-receive-2-5-2-96'),
        *[('receiver-store',f'signal-receiver-store-{op}-5-2') for op in('lookup','replace','insert')],
        ('keccak','signal-keccak-sha3-256-136-32'),('keccak','signal-keccak-sha3-512-64-64'),
        ('keccak','signal-keccak-shake128-34-504'),('keccak','signal-keccak-shake256-33-272')]
    for category,name in profiles:
        reportpath=ROOT/f'benchmarks/results/lean-signal-{category}-checks.json';report=json.loads(reportpath.read_text());snapshots[str(reportpath.relative_to(ROOT))]=digest(reportpath)
        for path,value in report['source_sha256'].items():assert digest(ROOT/path)==value,path
        artifact=ROOT/f'.deps/signal-{category}-artifacts/{name}.json';fixture=artifact.with_name(name+'-fixtures.json')
        matches=[row for row in report['cases'] if row['artifact_sha256']==digest(artifact)];assert len(matches)==1
        assert digest(fixture)==matches[0]['fixture_sha256']
        cases=json.loads(fixture.read_text());inputs=[bytes.fromhex(c['input']) for c in cases];outputs=[bytes.fromhex(c['output']) for c in cases]
        row={'category':category,'name':name,'artifact_sha256':digest(artifact),'fixture_sha256':digest(fixture),'mpc_compilations':[compile_and_check(artifact,inputs,outputs,n) for n in(1,16)]}
        rows.append(row);print(json.dumps(row),flush=True)
        backend=ROOT/'.deps/MP-SPDZ';sources=[Path(__file__),ROOT/'scripts/check_lean_crypto.py',ROOT/'scripts/clear_circuit.py',ROOT/'test_support/circuit.py',ROOT/'programs/lean_artifact.mpc',backend/'compile.py',*sorted((backend/'Compiler').rglob('*.py'))]
        result={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'fixture_report_sha256':snapshots,'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sources},'cases':rows,'complete':len(rows)==len(profiles),'parties':5,'native_mpc_executed':False,'public_fixture_reveal_harness':True,'deployment_security_configuration_tested':False}
        for path,value in snapshots.items():assert digest(ROOT/path)==value,path
        (ROOT/'benchmarks/results/lean-signal-session-store-keccak-backend-checks.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
