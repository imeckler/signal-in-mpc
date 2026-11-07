#!/usr/bin/env python3
"""Independent scope/provenance review for shared parsing and translation candidates.
Does not accept unfinished actual-Rust refinements or model extensions.
"""
import hashlib,json,re,subprocess,tarfile
from datetime import datetime,timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    report_path=ROOT/'benchmarks/results/lean-signal-proto-parse-checks.json';report=json.loads(report_path.read_text())
    for n,h in report['source_sha256'].items():assert digest(ROOT/n)==h,n
    assert report['prost_oracle_all_match'] and report['concrete_all_match'] and report['custom_axioms']==[]
    proto=ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/proto/wire.proto';text=proto.read_text()
    message=re.search(r'message SignalMessage\s*\{([^}]+)\}',text).group(1)
    fields=re.findall(r'optional\s+(bytes|uint32)\s+(\w+)\s*=\s*(\d+)\s*;',message)
    expected=[('bytes','ratchet_key','1'),('uint32','counter','2'),('uint32','previous_counter','3'),('bytes','ciphertext','4'),('bytes','pq_ratchet','5'),('bytes','addresses','6')]
    assert fields==expected,fields
    oracle=(HERE/'Oracle/src/main.rs').read_text()
    attrs=re.findall(r'#\[prost\(([^)]+)\)\]\s+(\w+):\s+Option<([^>]+(?:>?)?)>',oracle)
    assert len(attrs)==6,attrs
    for (ty,_,tag),(attr,name,rty) in zip(expected,attrs):
        assert 'optional' in attr and 'tag="'+tag+'"' in attr
        assert ('bytes="vec"' in attr) if ty=='bytes' else ('uint32' in attr)
    manifests=[]
    for package in ('prost-0.14.4','prost-derive-0.14.4','bytes-1.12.0'):
        vendor=ROOT/'.deps/libsignal-vendor'/package;manifest=vendor/'.cargo-checksum.json';checks=json.loads(manifest.read_text())
        for n,h in checks['files'].items():assert digest(vendor/n)==h,(package,n)
        manifests.append({'package':package,'checksum_manifest_sha256':digest(manifest),'verified_files':len(checks['files'])})
    fixture=ROOT/'.deps/signal-proto-parse-artifacts/fixtures.json';assert digest(fixture)==report['fixture_sha256'];cases=json.loads(fixture.read_text())
    raw=[bytes.fromhex(c['input']) for c in cases];bodies=[w[1:-8] if len(w)>=9 else b'' for w in raw]
    binary=ROOT/'.deps/signal-prost-oracle-target/debug/signal-prost-parser-oracle'
    observed=subprocess.run([str(binary)],input=''.join(b.hex()+'\n' for b in bodies),text=True,capture_output=True,check=True).stdout.splitlines()
    assert observed==[c['prost'] for c in cases]
    for profile in ('varint','slice'):
        inv=json.loads((HERE/f'Artifacts/{profile}/inventory.json').read_text());assert inv['charon_exit_code']==0 and not inv['has_errors']
        assert inv['source_patches']==[] and not inv['llbc_preprocessing']
        for n,h in inv['source_sha256'].items():assert digest(ROOT/n)==h,n
        for n,h in inv.get('generated_files',{}).items():assert digest(ROOT/'SignalReference'/n)==h,n
    axioms=(HERE/'slice-boundary-axioms.txt').read_text();assert 'sorryAx' in axioms
    model=HERE/'ModelCandidate';build=json.loads((model/'build-report.json').read_text())
    assert build['candidate_only'] and not build['accepted_reference'] and not build['original_models_modified']
    assert digest(model/'Aeneas/Std/Slice.lean')==build['candidate_source_sha256']
    assert digest(ROOT/'.deps/aeneas-2026-08-27/backends/lean/Aeneas/Std/Slice.lean')==build['original_source_sha256']
    assert digest(model/'slice-model.diff')==build['diff_sha256']
    out={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'script_sha256':digest(Path(__file__)),'parser_report_sha256':digest(report_path),'schema_sha256':digest(proto),'exact_optional_schema_verified':expected,'vendored_sources':manifests,'native_prost_fixture_rechecks':len(cases),'native_oracle_binary_sha256':digest(binary),'parser_compiler_theorems_checked':report['checked_endpoints'],'actual_whole_rust_parser_refinement_accepted':False,'unmodified_slice_decoder_contains_sorryAx':True,'original_slice_axiom_report_sha256':digest(HERE/'slice-boundary-axioms.txt'),'model_extension_build_report_sha256':digest(model/'build-report.json'),'model_extension_accepted':False,'model_translation_precondition':build['trust_boundary'],'step_metadata_candidate_accepted':False,'remaining_full_varint_external_wrappers':3}
    (HERE/'review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
