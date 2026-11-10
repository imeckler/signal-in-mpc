#!/usr/bin/env python3
"""Freeze the locally checked decoder candidate; acceptance stays external."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    report = json.loads((HERE / 'report.json').read_text())
    assert report['candidate_only'] and not report['accepted_reference']
    assert report['standard_axioms_only']
    assert report['actual_aeneas_field_decoder_refinement']
    for name, digest in report['checked_inputs_sha256'].items():
        assert sha(HERE / name) == digest, name
    for name, key in [('axioms.txt', 'axioms_sha256'),
                      ('fixtures.json', 'fixtures_sha256'),
                      ('baf-provenance.json', 'baf_provenance_sha256')]:
        assert sha(HERE / name) == report[key], name
    files = {str(p.relative_to(ROOT)): sha(p) for p in sorted(HERE.rglob('*'))
             if p.is_file() and p.name != 'completion.json'
             and not any(x in {'Build', '__pycache__', '.lake'}
                         for x in p.relative_to(HERE).parts)}
    receipt = {'candidate_only': True, 'accepted_reference': False,
               'files': files, 'proof_endpoints': report['proof_endpoints'],
               'generated_decoder_cases': report['generated_decoder_cases'],
               'native_normalization_pairs': report['native_original_vs_normalized_recovery_pairs'],
               'full_xeddsa_or_to_edwards_refinement': False,
               'new_circuit_gates': 0, 'new_backend_artifacts': 0,
               'trust_boundary': 'Pinned Charon/Aeneas translation and Lean kernel; '
               'standard Lean axioms only. No full Rust compiler or cryptographic security proof.'}
    (HERE / 'completion.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(f'Frozen {len(files)} candidate files; completion sha256 {sha(HERE / "completion.json")}')


if __name__ == '__main__':
    main()
