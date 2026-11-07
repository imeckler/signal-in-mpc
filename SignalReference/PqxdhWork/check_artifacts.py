#!/usr/bin/env python3
"""Native PQXDH artifact, numeric fixtures, backend compilation, mixed adapter audit."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load, execute
from backend_adapter.aig import statistics
from handshake_backend.field_dag import load as load_field, evaluate_clear, MODULUS
from scripts.check_lean_crypto import evaluate_lanes
from scripts.clear_circuit import execute as execute_mpc_source
from test_support.circuit import input_tokens
from SignalReference.PqxdhWork.adapter import initiate
from SignalReference.PqxdhWork.check import oracle
import cryptography
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def wire_bits(data):
    return [(byte >> shift) & 1 for byte in data for shift in range(7, -1, -1)]


def wire_bytes(bits):
    return bytes(sum(bits[i+j] << (7-j) for j in range(8)) for i in range(0, len(bits), 8))


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--reuse-backend-compilation', action='store_true', help='Reuse matching successful local compiler logs/bytecode; rerun artifact and clear-source fixtures.')
    options = cli.parse_args()
    backend = ROOT / '.deps/MP-SPDZ'
    directory = HERE / 'Artifacts/Export'
    directory.mkdir(parents=True, exist_ok=True)
    proof_path = HERE / 'proof-report.json'
    proof = json.loads(proof_path.read_text())
    assert proof['checked_endpoints'] == 10 and proof['custom_axioms'] == []
    for name, expected in proof['source_sha256'].items():
        assert digest(ROOT / name) == expected, name
    fixture_path = HERE / 'fixture-results.json'
    assert digest(fixture_path) == proof['fixture_report_sha256']
    fixtures = json.loads(fixture_path.read_text())['fixtures']
    pin_path = ROOT / 'benchmarks/config/dependencies.json'
    pin = json.loads(pin_path.read_text())['mp_spdz']
    archive = ROOT / '.deps/mp-spdz-v0.4.4.tar.gz'
    assert digest(archive) == pin['source_archive_sha256']
    compiler_sources = [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    with tarfile.open(archive) as bundle:
        members = {m.name.split('/', 1)[1]: m for m in bundle.getmembers() if m.isfile()}
        for path in compiler_sources:
            assert path.read_bytes() == bundle.extractfile(members[str(path.relative_to(backend))]).read(), path
    sources = {Path(__file__), HERE/'Export.lean', HERE/'adapter.py', HERE/'program.mpc', HERE/'lakefile.toml',
               HERE/'lean-toolchain', HERE/'lake-manifest.json', proof_path, fixture_path, pin_path,
               ROOT/'backend_adapter/boolean.py', ROOT/'backend_adapter/aig.py',
               ROOT/'handshake_backend/field_dag.py', ROOT/'handshake_backend/mixed.py',
               ROOT/'programs/lean_artifact.mpc', ROOT/'scripts/check_lean_crypto.py',
               ROOT/'scripts/clear_circuit.py', ROOT/'test_support/circuit.py', *compiler_sources,
               *[ROOT/name for name in proof['source_sha256']]}
    def visit(module):
        if not module.startswith('TlsMpc'):
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        if path in sources:
            return
        sources.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(imported)
    visit('TlsMpc.X25519')
    before = {str(p.relative_to(ROOT)): digest(p) for p in sorted(sources)}
    subprocess.run(['lake', '-d', str(HERE), 'build', 'emit_pqxdh'], cwd=ROOT, check=True)
    binary = HERE / '.lake/build/bin/emit_pqxdh'
    paths = {}
    for profile in ['none', 'present', 'signal-dh-field']:
        output = directory / (('signal-pqxdh-' + profile) if profile != 'signal-dh-field' else profile)
        output = output.with_suffix('.json')
        with output.open('w') as target:
            subprocess.run([str(binary), profile], cwd=ROOT, stdout=target, check=True, timeout=600)
        paths[profile] = output
        print('Native export complete: ' + profile, flush=True)
    env = os.environ.copy()
    env['PYTHONPATH'] = str(ROOT) + os.pathsep + env.get('PYTHONPATH', '')
    source = ROOT / 'programs/lean_artifact.mpc'
    if options.reuse_backend_compilation:
        assert source.read_bytes() == (backend / 'Programs/Source/pqxdh_artifact.mpc').read_bytes()
    else:
        shutil.copy2(source, backend / 'Programs/Source/pqxdh_artifact.mpc')

    def compile_boolean(path, raw, expected, batch):
        copied = backend / 'Programs/Source/lean-artifacts'
        copied.mkdir(exist_ok=True)
        if not options.reuse_backend_compilation:
            shutil.copy2(path, copied/path.name)
        args = [path.stem, str(batch), '5']
        program = 'pqxdh_artifact-' + '-'.join(args)
        command = [sys.executable, './compile.py', '-M', '-B', '128', 'pqxdh_artifact', *args]
        logpath = directory/(program+'.log')
        if options.reuse_backend_compilation:
            assert path.read_bytes() == (copied/path.name).read_bytes()
            log = logpath.read_text()
            assert 'Program requires at most:' in log and 'Writing to Programs/Bytecode/' + program in log
        else:
            compiled = subprocess.run(command, cwd=backend, env=env, capture_output=True, text=True, timeout=600)
            log = compiled.stdout + compiled.stderr
            logpath.write_text(log)
            assert compiled.returncode == 0, log[-4000:]
        inputs = [raw[i % len(raw)] for i in range(batch)]
        outputs = [expected[i % len(expected)] for i in range(batch)]
        values = [int.from_bytes(x[offset:offset+8], 'big') for offset in range(0,96,8) for x in outputs]
        previous = Path.cwd()
        try:
            os.chdir(backend)
            observed = execute_mpc_source(source, backend/'Programs/Circuits', ['pqxdh_artifact', *args], input_tokens({'raw': inputs}))
        finally:
            os.chdir(previous)
        assert observed == values, program
        triples = re.findall(r'(\d+) bit triples', log)
        bytecodes = sorted((backend/'Programs/Bytecode').glob(program+'*.bc'))
        assert bytecodes
        return {'batch':batch,'parties':5,'bit_triples':int(triples[-1]) if triples else 0,
                'fixture_output_values_checked':len(values),'log_sha256':digest(logpath),
                'bytecode_sha256':{p.name:digest(p) for p in bytecodes}}

    cases, images = [], {}
    for profile in ['none','present']:
        path = paths[profile]
        image = load(path); images[profile] = image
        rows = [row for row in fixtures if row['accepted'] and bool(row['input_hex'][3]) == (profile == 'present')]
        raw = [b''.join(bytes.fromhex(p) for p in row['input_hex']) for row in rows]
        outputs = [bytes.fromhex(row['keys_hex']) for row in rows]
        assert evaluate_lanes(image, raw) == outputs
        ops = statistics(image)
        compilations = [compile_boolean(path,raw,outputs,batch) for batch in [1,16]]
        for result in compilations:
            assert result['bit_triples'] == ops['executed_and_gates'] * result['batch']
        cases.append({'profile':profile,'artifact_sha256':digest(path),'input_bits':image['input_bits'],
                      'output_bits':len(image['outputs']),'numeric_fixture_lanes':len(rows),
                      'adapter_operations':ops,'backend_compilations':compilations})
        print(json.dumps(cases[-1]),flush=True)

    field = load_field(paths['signal-dh-field'])
    def as_field(bits, mask_high_bit=False):
        value = int.from_bytes(wire_bytes(bits),'little')
        if mask_high_bit:
            value &= (1 << 255)-1
        return value % MODULUS
    primitives = SimpleNamespace(
        wire_bits_to_scalar_fields=lambda bits:[bits[8*(i//8)+7-i%8] for i in range(256)],
        wire_bits_to_field=as_field, execute_secret=evaluate_clear,
        field_to_wire_bits=lambda value:wire_bits(value.to_bytes(32,'little')),
        execute_boolean=lambda image, bits:execute(image,bits,0,1))
    mixed_rows = []
    for profile in ['none','present']:
        for fixture in range(3):
            keys = [hashlib.sha256(b'PQXDH public artifact fixture'+bytes([fixture,slot])).digest() for slot in range(6)]
            identity, ephemeral, their_identity, signed, one_time, kem = keys
            if fixture == 2:
                signed = bytes(32)
            optional = one_time if profile == 'present' else None
            dh = []
            for private, peer in [(identity,signed),(ephemeral,their_identity),(ephemeral,signed)]+([(ephemeral,one_time)] if optional else []):
                try:
                    shared = X25519PrivateKey.from_private_bytes(private).exchange(X25519PublicKey.from_public_bytes(peer))
                except ValueError:
                    shared = bytes(32)
                dh.append(shared)
            want = b'\xff'+oracle(dh[:3]+([dh[3]] if optional else [b''])+[kem]) if all(x != bytes(32) for x in dh) else bytes(97)
            got = wire_bytes(initiate(field,images[profile],wire_bits(identity),wire_bits(ephemeral),
                wire_bits(their_identity),wire_bits(signed),wire_bits(optional) if optional else None,
                wire_bits(kem),primitives=primitives))
            assert got == want,(profile,fixture)
            mixed_rows.append({'profile':profile,'case':fixture,'identity_private':identity.hex(),
                'ephemeral_private':ephemeral.hex(),'their_identity':their_identity.hex(),'signed_prekey':signed.hex(),
                'one_time_prekey':optional.hex() if optional else None,'kem_secret':kem.hex(),
                'agreements':[x.hex() for x in dh],'output':got.hex()})
    mixed_fixture_path = directory/'mixed-fixtures.json'
    mixed_fixture_path.write_text(json.dumps(mixed_rows,indent=2)+'\n')
    if not options.reuse_backend_compilation:
        shutil.copy2(HERE/'program.mpc',backend/'Programs/Source/pqxdh_mixed.mpc')
    mixed_compilations = []
    for profile in ['none','present']:
        command = [sys.executable,'./compile.py','-X','-P',str(MODULUS),'pqxdh_mixed',str(paths['signal-dh-field']),str(paths[profile]),profile]
        logpath = directory/('mixed-'+profile+'.log')
        if options.reuse_backend_compilation:
            assert (HERE/'program.mpc').read_bytes() == (backend/'Programs/Source/pqxdh_mixed.mpc').read_bytes()
            logtext = logpath.read_text()
            assert 'Program requires at most:' in logtext and 'Writing to Programs/Bytecode/pqxdh_mixed' in logtext
        else:
            result = subprocess.run(command,cwd=backend,env=env,capture_output=True,text=True,timeout=900)
            logtext = result.stdout + result.stderr
            logpath.write_text(logtext)
            assert result.returncode == 0,logtext[-4000:]
        # MP-SPDZ includes artifact arguments in the program filename; identify this compile from its log.
        bytecodes = [Path(name) for name in re.findall(r'Writing to (Programs/Bytecode/\S+\.bc)',logtext)]
        if not bytecodes:
            bytecodes = [p.relative_to(backend) for p in (backend/'Programs/Bytecode').glob('pqxdh_mixed*.bc')]
        assert bytecodes
        mixed_compilations.append({'profile':profile,'log_sha256':digest(logpath),
            'compiler_flags':['-X','-P',str(MODULUS)],
            'bit_triples':int(re.search(r'(\d+) bit triples',logtext).group(1)),
            'integer_simple_multiplications':int(re.search(r'(\d+) integer simple multiplications',logtext).group(1)),
            'compiler_default_security_parameter':int(re.search(r'Default security parameter for compilation: (\d+)',logtext).group(1)),
            'bytecode_sha256':{str(p):digest(backend/p) for p in bytecodes},'native_execution':False})
        print('Same-VM compilation complete: '+profile,flush=True)
    assert before == {str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)},'sources changed'
    report = {'checked_at_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':before,
        'proof_report_sha256':digest(proof_path),'native_exporter':str(binary.relative_to(ROOT)),
        'native_exporter_sha256':digest(binary),'artifacts':{k:{'path':str(p.relative_to(ROOT)),'sha256':digest(p)} for k,p in paths.items()},
        'cases':cases,'backend_pin':pin,'compiler_sources_match_pinned_archive':True,
        'numeric_artifact_fixture_evaluation':True,'boolean_batch1_and16_compiled':True,'clear_mpc_source_checked':True,
        'mixed_adapter_fixture_count':len(mixed_rows),
        'independent_x25519_oracle':{'library':'cryptography','version':cryptography.__version__},'mixed_fixtures_sha256':digest(mixed_fixture_path),
        'mixed_compilations':mixed_compilations,'same_vm_x25519_stages':{'none':3,'present':4},
        'mixed_input_layout':'identityPrivate32||ephemeralPrivate32||theirIdentity32||signedPrekey32||optionalOneTimePrekey0/32||KyberSharedSecret32; five-party XOR shares, MSB-first bits per byte',
        'mixed_output_layout':'shared status255/0||root32||chain32||PQR32, zeroed on any all-zero DH agreement',
        'kyber_shared_secret_is_unresolved_input':True,'identity_and_prekey_validation':False,
        'native_mpc_executed':False,'throughput_measured':False,'actual_rust_wrapper_equivalence':False,
        'backend_compilation_reused':options.reuse_backend_compilation,
        'boolean_harness_is_public_fixture_only':True,
        'boolean_harness_reveals_synthetic_outputs':True,
        'mixed_harness_keeps_outputs_in_secret_memory':True,
        'trust_boundary':'Lean proves numeric KDF artifact correctness; native exporter/JSON/backend and same-VM field conversion/composition remain unverified; fixture checks do not close those proof gaps.',
        'actual_extraction_blocker':proof['actual_extraction']}
    out = HERE/'artifact-report.json'; out.write_text(json.dumps(report,indent=2)+'\n')
    print('artifact-report.json SHA256: '+digest(out),flush=True)


if __name__ == '__main__':
    main()
