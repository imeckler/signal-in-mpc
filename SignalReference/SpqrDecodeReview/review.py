#!/usr/bin/env python3
"""Independent acceptance checks for the unchanged actual SPQR decoder lane."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
WORK = ROOT / 'SignalReference/VarintDecodeWork'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    # Reviewed independently: root operation/body, complete loop and all cursor
    # branches correspond to pinned Rust lib.rs:524-554. Official Slice/min and
    # checked scalar arithmetic constitute the only modeled computational calls.
    subprocess.run(['python3', str(WORK / 'check.py')], cwd=ROOT, check=True)
    report_path = WORK / 'proof-report.json'
    report = json.loads(report_path.read_text())
    inv = json.loads((WORK / 'Artifacts/spqr/inventory.json').read_text())
    assert report['checked_endpoints'] == 19
    assert report['custom_axioms'] == report['llbc_preprocessing'] == report['custom_standard_models'] == []
    assert report['upstream_spqr_files_compared_byte_for_byte'] == 99
    assert report['all_standard_model_files_match_pinned_archive'] == 87
    assert report['aeneas_regeneration_byte_identical'] and report['aeneas_binary_matches_pinned_release_archive']
    assert inv['body_kinds'] == {'Structured': 2, 'Opaque': 5}
    assert {x['name'] for x in inv['external_functions']} == {
        'core::slice::{impl}::len', 'core::cmp::min', 'core::cmp::impls::{impl}::cmp',
        'core::cmp::impls::{impl}::partial_cmp', 'core::cmp::impls::{impl}::eq'}
    assert inv['external_or_union_types'] == [] and inv['remaining_external_templates'] == []
    for name, expected in report['source_sha256'].items():
        assert digest(ROOT / name) == expected, name
    lean = [WORK / (name + '.lean') for name in report['reference_modules_recompiled_in_isolation']]
    for path in lean:
        assert not re.search(r'^\s*(axiom|opaque)\s|\bsorry\b|\badmit\b|\bnative_decide\b', path.read_text(), re.M), path
    generated = (WORK / 'Generated/spqr/Funs.lean').read_text()
    assert re.findall(r'^def ([^\s]+)', generated, re.M) == ['decode_varint_loop.body', 'decode_varint_loop', 'decode_varint']
    assert 'import VarintDecodeWork.Generated.spqr.Types' in generated
    assert 'External' not in generated
    offset = (WORK / 'OffsetBridge.lean').read_text()
    assert 'big-endian' in offset and 'little-endian' not in offset
    review = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'reviewer': '/root/signal_astra_high', 'author': '/root/signal_astra_high/decoder_reference',
        'accepted': True, 'proof_report_sha256': digest(report_path),
        'script_sha256': digest(Path(__file__)), 'original_llbc_sha256': report['original_llbc_sha256'],
        'reviewed_scope': 'Actual decode_varint, unchanged loop/body, success/error and absolute cursor, prefix/shared-offset AIG bridges.',
        'independent_findings': [
            'Original LLBC is used directly; there is no metadata/body rewriting or declaration selection.',
            'All generated references resolve to actual retained operations or the pinned official models; no generated external template remains.',
            'The theorem domain includes every official Slice and Usize, including starts at and beyond end.',
            'Noncanonical encodings and truncated excess payload bits in byte ten are retained.',
            'All19 proof endpoints were rebuilt and audited; only standard foundational axioms occur.',
            'Corrected a documentation-only cursor endianness typo before acceptance; encodeLength was already big-endian in the proof.'
        ],
        'trusted_boundary': ['Pinned Rust/Charon/Aeneas extraction', 'Official Aeneas scalar/Slice/min/loop models',
                             'Lean kernel and standard foundational axioms'],
        'full_message_parser_refinement': False, 'state_machine_or_crypto_refinement': False,
        'native_mpc_execution': False,
    }
    review_path = HERE / 'review.json'
    review_path.write_text(json.dumps(review, indent=2) + '\n')
    acceptance = {
        'accepted_reference': True,
        'accepted_scope': review['reviewed_scope'],
        'spqr_commit': report['spqr_commit'],
        'author': report['author'], 'reviewer': review['reviewer'],
        'proof_report': 'SignalReference/VarintDecodeWork/proof-report.json',
        'proof_report_sha256': digest(report_path),
        'independent_review': 'SignalReference/SpqrDecodeReview/review.json',
        'independent_review_sha256': digest(review_path),
        'checked_endpoints': 19,
        'actual_operation_domain': report['operation_domain'],
        'artifact_domain': report['artifact_domain'],
        'prefix_theorem': report['prefix_numeric_artifact_theorem'],
        'offset_theorem': report['offset_numeric_artifact_theorem'],
        'llbc_preprocessing': [], 'custom_standard_models': [], 'custom_axioms': [], 'rust_source_changes': [],
        'full_message_parser_refinement': False, 'full_spqr_state_machine_refinement': False,
        'note': 'Author report intentionally retains accepted_reference:false; this separate independent record accepts only stated decoder scope.',
    }
    (WORK / 'acceptance.json').write_text(json.dumps(acceptance, indent=2) + '\n')
    print('Accepted actual prefix and arbitrary-offset SPQR varint decoder refinement; full parser remains separate.')


if __name__ == '__main__':
    main()
