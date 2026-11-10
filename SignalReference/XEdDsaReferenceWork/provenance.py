#!/usr/bin/env python3
"""Record exact bounded BAF proof reuse and byte-identical selected Rust body."""
import difflib,hashlib,json,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
COMMIT='95b5831c63ff1c5f6287bd3a77569412a9afdbfb'
BAF=ROOT/'.deps/baf-review'/('curve25519-dalek-fork-'+COMMIT)
PROOF=BAF/'curve25519-dalek/lean/Proofs/Backend/Serial/U64/Field/FromBytes.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def body(p):
    text=p.read_text();start=text.index('pub const fn from_bytes(');begin=text.index('{',start);depth=1;end=begin+1
    while depth:
        depth+=(text[end]=='{')-(text[end]=='}');end+=1
    return text[start:end]
def main():
    archive=ROOT/'.deps/baf-curve25519-dalek-fork.tar.gz'
    review=json.loads((ROOT/'SignalReference/Extraction/baf-review.json').read_text())
    pin=next(x for x in review['repositories'] if x['commit']==COMMIT)
    assert sha(archive)==pin['archive_sha256']
    selected=['curve25519-dalek/lean/Proofs/Backend/Serial/U64/Field/FromBytes.lean',
      *['curve25519-dalek/lean/Proofs/Helpers/'+n+'.lean' for n in ['Array','Bitwise','AsNat','Limbs','StepSpecs']],
      'curve25519-dalek/lean/Defs/FieldElement51.lean','curve25519-dalek/src/backend/serial/u64/field.rs']
    with tarfile.open(archive) as tar:
        for rel in selected:
            member=next(m for m in tar.getmembers() if m.isfile() and m.name.endswith('/'+rel))
            assert tar.extractfile(member).read()==(BAF/rel).read_bytes(),rel
    actual=ROOT/'.deps/libsignal-vendor/curve25519-dalek-5.0.0/src/backend/serial/u64/field.rs'
    baf=BAF/'curve25519-dalek/src/backend/serial/u64/field.rs'
    assert body(actual)==body(baf)
    diff=''.join(difflib.unified_diff(PROOF.read_text().splitlines(True),(HERE/'FieldDecodeProof.lean').read_text().splitlines(True),fromfile='BAF/FromBytes.lean',tofile='candidate/FieldDecodeProof.lean'))
    (HERE/'baf-port.diff').write_text(diff)
    report={'baf_commit':COMMIT,'baf_archive_sha256':sha(archive),'archive_files_verified':{p:sha(BAF/p) for p in selected},
      'selected_rust_function_body_identical':True,'selected_body_sha256':hashlib.sha256(body(actual).encode()).hexdigest(),
      'whole_rust_file_identical':sha(actual)==sha(baf),'full_baf_build_claimed':False,
      'imported_baf_module_dependencies':[],'baf_model_axioms_imported':[],
      'adaptation':'Selected arithmetic/index/mask lemmas compiled locally against our actual generated decoder. Namespace/import adaptation, local finite-sum Array.asNat definition and five-limb interpretation, dependent rewrite compatibility and Array.make simplification for pinned Lean4.31/Aeneas; all adaptations kernel checked.',
      'local_port_sha256':{p:sha(HERE/p) for p in ['BafSupport.lean','FieldDecodeProof.lean','baf-port.diff']}}
    (HERE/'baf-provenance.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Verified BAF selected body identity and proof provenance')
if __name__=='__main__':main()
