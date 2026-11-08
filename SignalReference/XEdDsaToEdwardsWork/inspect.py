#!/usr/bin/env python3
"""Verify exact selected entry and bounded BAF entry-body provenance; no proof claim."""
import hashlib,json,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
COMMIT='95b5831c63ff1c5f6287bd3a77569412a9afdbfb'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def body(p):
    s=p.read_text();start=s.index('pub fn to_edwards(');i=s.index('{',start)+1;depth=1
    while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
    return s[start:i]
def main():
    inventory=json.loads((HERE/'Artifacts/ToEdwards/inventory.json').read_text())
    assert inventory['charon_exit_code']==0 and inventory['aeneas_exit_code']==2
    assert not inventory['has_errors'] and inventory['source_patches']==[]
    assert sha(HERE/'extract.py')==inventory['script_sha256']
    assert any(x['name'].endswith('::to_edwards') for x in inventory['selected_functions'])
    for name,digest in inventory['source_sha256'].items():assert sha(ROOT/name)==digest,name
    log=(HERE/'Artifacts/ToEdwards/aeneas.log').read_text()
    assert 'forward_overflowing' in log and 'core::iter::range::Step' in log
    archive=ROOT/'.deps/baf-curve25519-dalek-fork.tar.gz'
    review=json.loads((ROOT/'SignalReference/Extraction/baf-review.json').read_text())
    pin=next(x for x in review['repositories'] if x['commit']==COMMIT)
    assert sha(archive)==pin['archive_sha256']
    baf=ROOT/'.deps/baf-review'/('curve25519-dalek-fork-'+COMMIT)
    selected=['curve25519-dalek/src/montgomery.rs','curve25519-dalek/lean/Proofs/Montgomery/ToEdwards.lean']
    with tarfile.open(archive) as tar:
        for name in selected:
            member=next(m for m in tar.getmembers() if m.isfile() and m.name.endswith('/'+name))
            assert tar.extractfile(member).read()==(baf/name).read_bytes()
    actual=ROOT/'.deps/libsignal-vendor/curve25519-dalek-5.0.0/src/montgomery.rs'
    assert body(actual)==body(baf/selected[0])
    report={'actual_entry_selected':True,'charon_function_declarations':inventory['counts']['fun_decls'],
        'aeneas_translation_succeeded':False,'actual_to_edwards_agreement_proved':False,
        'blocker':'Pinned Step builtin lacks forward_overflowing (transitive field.rs:60).',
        'baf_commit':COMMIT,'baf_archive_sha256':sha(archive),'selected_entry_body_identical':True,
        'selected_entry_body_sha256':hashlib.sha256(body(actual).encode()).hexdigest(),
        'baf_files_verified_against_archive':{name:sha(baf/name) for name in selected},
        'baf_proof_imported':False,'custom_models_or_translator_edits':[],
        'scope':'Diagnostic only. Full Subtle/arithmetic/decompression and exact rejection/sign/circuit agreements remain.',
        'local_sha256':{str(p.relative_to(HERE)):sha(p) for p in [HERE/'extract.py',Path(__file__),
            HERE/'Artifacts/ToEdwards/inventory.json',HERE/'Artifacts/ToEdwards/aeneas.log']}}
    (HERE/'blocker.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Verified selected actual entry, matching BAF body provenance, and reproduced Step translation blocker')
if __name__=='__main__':main()
