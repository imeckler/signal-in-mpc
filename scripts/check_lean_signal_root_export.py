#!/usr/bin/env python3
"""Compare root native Signal CLI artifacts to independently checked exports.

Only descriptive text may differ; all numeric fields/nodes/output references
must be byte-identical. Existing TLS dispatch is exercised separately.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def numeric_digest(path):
    raw = path.read_bytes()
    raw, count = re.subn(rb'"input_description":"(?:[^"\\]|\\.)*",', b'', raw, count=1)
    assert count == 1, path
    return hashlib.sha256(raw).hexdigest()


def main():
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    executable = ROOT / '.lake/build/bin/emit_mpc'
    sources = [ROOT/'Main.lean', ROOT/'TlsMpc.lean', ROOT/'TlsMpc/Signal/Export.lean',
               ROOT/'lean-toolchain', ROOT/'lakefile.toml', Path(__file__)]
    snapshot = {str(p.relative_to(ROOT)):digest(p) for p in sources}
    directory = ROOT / '.deps/signal-root-artifacts'; directory.mkdir(exist_ok=True)
    profiles = [
        ('send', ['signal-serialize','0','0','1','1','none']),
        ('send', ['signal-serialize','128','1','5','1','present']),
        ('send', ['signal-send','0','0','1','1','none']),
        ('send', ['signal-send','16','7','5','3','present']),
        ('chain-send', ['signal-chain-send','0','0','1','1','none']),
        ('chain-send', ['signal-chain-send','17','5','5','2','present']),
        ('spqr-chain', ['signal-spqr-chain']),
        ('spqr-message', ['signal-spqr-message','1','1','0','none']),
        ('spqr-message', ['signal-spqr-message','10','5','3','present']),
        ('spqr-send', ['signal-spqr-send','0','1','1','1','1','0','none','none']),
        ('spqr-send', ['signal-spqr-send','17','5','2','10','5','3','present','present']),
        ('spqr-decode', ['signal-spqr-decode','10']),
        ('spqr-decode', ['signal-spqr-decode-at','64']),
        ('spqr-parse', ['signal-spqr-parse','0']),
        ('spqr-parse', ['signal-spqr-parse','64']),
        ('spqr-parse', ['signal-spqr-parse','256']),
        ('spqr-epoch', ['signal-spqr-epoch-new']),
        ('spqr-epoch', ['signal-spqr-epoch-add']),
        ('dh-ratchet', ['signal-dh-field']),
        ('dh-ratchet', ['signal-dh-ratchet']),
        ('proto-parse', ['signal-protobuf-parse','64']),
        ('proto-parse', ['signal-protobuf-parse','128']),
        ('proto-receive', ['signal-protobuf-receive','96']),
        ('proto-receive', ['signal-protobuf-receive','160']),
        ('chain-receive', ['signal-chain-receive','96']),
        ('skipped-receive', ['signal-skipped-receive','4','96']),
        ('skipped-keys', ['signal-skipped-consume','4']),
        ('skipped-keys', ['signal-skipped-insert','4']),
        ('pqxdh', ['signal-pqxdh','none']),
        ('pqxdh', ['signal-pqxdh','present']),
        ('receive-advance', ['signal-receive-advance','2','2']),
        ('receive-advance', ['signal-receive-committed','2','2']),
        ('bounded-receive', ['signal-bounded-receive','2','4','96']),
        ('ratchet-step', ['signal-ratchet-step']),
        ('new-ratchet-receive', ['signal-new-ratchet-receive','2','2','96']),
        ('receiver-store', ['signal-receiver-store','lookup','5','2']),
        ('receiver-store', ['signal-receiver-store','replace','5','2']),
        ('receiver-store', ['signal-receiver-store','insert','5','2']),
        ('retained-receive', ['signal-retained-receive','2','5','4','96']),
        ('session-receive', ['signal-session-receive','2','5','2','96']),
    ]
    results = []
    reports = {}
    for category, arguments in profiles:
        name = '-'.join(arguments)+'.json'
        reference = ROOT/f'.deps/signal-{category}-artifacts'/name
        report_path = ROOT/f'benchmarks/results/lean-signal-{category}-checks.json'
        if category == 'pqxdh':
            reference = ROOT/'SignalReference/PqxdhWork/Artifacts/Export'/name
            report_path = ROOT/'SignalReference/PqxdhWork/artifact-report.json'
        if category in ('skipped-keys', 'receive-advance'):
            work = 'SkippedKeysWork' if category == 'skipped-keys' else 'ReceiveAdvanceWork'
            reference = ROOT/'SignalReference'/work/'Artifacts'/name
            report_path = ROOT/'SignalReference'/work/'proof-report.json' 
        reports[str(report_path.relative_to(ROOT))] = digest(report_path)
        expected_hash = digest(reference)
        assert expected_hash in report_path.read_text(), f'Cached artifact lacks checked-report hash: {reference}'
        output = directory/name
        with output.open('w') as stream:
            subprocess.run([str(executable),*arguments],cwd=ROOT,stdout=stream,check=True,timeout=600)
        numeric = numeric_digest(reference)
        assert numeric_digest(output) == numeric, f'Root numeric artifact changed for {arguments}'
        row = {'arguments':arguments,'reference_artifact_sha256':expected_hash,
               'root_artifact_sha256':digest(output),'numeric_artifact_sha256_without_description':numeric,
               'all_numeric_fields_byte_identical':True}
        results.append(row); print(json.dumps(row),flush=True)
    # Representative argument counts that traverse tryRun and fall through to
    # the unchanged TLS/primitive modes; validate their existing named schemas.
    tls = []
    for arguments in [ ['tls-nonce'], ['tls-header','16','0'], ['tls-inner','3','2'],
                       ['tls-parse-inner','1'], ['tls-open-handshake-record','22'],
                       ['sha256','0'], ['hkdf-sha256','0','0','0','0'] ]:
        result = subprocess.run([str(executable),*arguments],cwd=ROOT,capture_output=True,text=True,check=True,timeout=120)
        value = json.loads(result.stdout)
        assert value['name'] == arguments[0] and value['format'] in ('tls-mpc-boolean-v1','tls-mpc-aig-v1')
        tls.append({'arguments':arguments,'name':value['name'],'format':value['format']})
    rejected = [ ['signal-bounded-receive','17','4','96'], ['signal-receive-advance','2','65'],
                 ['signal-skipped-receive','4','513'], ['signal-pqxdh','invalid'],
                 ['signal-protobuf-parse','513'], ['signal-protobuf-receive','513'], ['signal-chain-receive','513'],
                 ['signal-spqr-parse','257'], ['signal-spqr-decode-at','257'],
                 ['signal-send','1025','0','1','1','none'],
                 ['signal-chain-send','0','0','0','1','none'],
                 ['signal-spqr-message','11','1','0','none'],
                 ['signal-spqr-message','1','1','1','none'],
                 ['signal-spqr-send','0','1','1','1','1','0','present','none'] ]
    for arguments in rejected:
        result = subprocess.run([str(executable),*arguments],cwd=ROOT,capture_output=True,text=True,timeout=30)
        assert result.returncode != 0 and result.stdout == '', arguments
    assert snapshot == {str(p.relative_to(ROOT)):digest(p) for p in sources}
    assert reports == {name:digest(ROOT/name) for name in reports}
    report = {'checked_at_utc':datetime.now(timezone.utc).isoformat(),'executable_sha256':digest(executable),
              'source_sha256':snapshot,'independent_fixture_reports_sha256':reports,
              'signal_profiles':results,'tls_dispatch_smoke_checks':tls,'invalid_profiles_rejected':rejected,
              'native_exporter_executed':True,'native_mpc_executed':False,
              'scope':'CLI integration equivalence only; does not extend actual Rust refinement or deployment-security claims.'}
    (ROOT/'benchmarks/results/lean-signal-root-export-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'Passed {len(results)} exact numeric artifact comparisons, {len(tls)} TLS dispatch checks and {len(rejected)} invalid-profile checks.')


if __name__ == '__main__':
    main()
