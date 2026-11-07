#!/usr/bin/env python3
"""Reproduce and audit the candidate actual Prost slice decoder bridge.

This does not grant independent acceptance, change upstream/generated sources,
or claim semantics for Rust out-of-bounds undefined behavior.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

HERE=Path(__file__).resolve().parent
REFERENCE=HERE.parent
ROOT=REFERENCE.parent
MODEL=ROOT/'.deps/aeneas-2026-08-27/backends/lean'
BUILD=HERE/'BridgeBuild'
NAMESPACE='LibSignalReference.Candidate.ProstSlice.'


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def environment():
    report=json.loads((HERE/'ModelCandidate/build-report.json').read_text())
    assert report['candidate_only'] and not report['accepted_reference']
    assert digest(HERE/'ModelCandidate/Aeneas/Std/Slice.lean')==report['candidate_source_sha256']
    assert digest(MODEL/'Aeneas/Std/Slice.lean')==report['original_source_sha256']
    assert digest(HERE/'ModelCandidate/slice-model.diff')==report['diff_sha256']
    assert digest(HERE/'ModelCandidate/build.py')==report['script_sha256']
    for name,sha in report['source_sha256'].items(): assert digest(ROOT/name)==sha,name
    cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
    paths=[HERE/'ModelCandidate/Build',BUILD,ROOT/'.lake/build/lib/lean',REFERENCE/'.lake/build/lib/lean',
        MODEL/'.lake/build/lib/lean',*[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]]
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths));return env


def main():
    env=environment()
    if len(sys.argv)>1:
        subprocess.run(['lean',*sys.argv[1:]],cwd=REFERENCE,env=env,check=True);return
    inventory_path=HERE/'Artifacts/slice/inventory.json'
    inventory=json.loads(inventory_path.read_text())
    pins_path=REFERENCE/'pins.json';pins=json.loads(pins_path.read_text())
    assert inventory['charon_exit_code']==inventory['aeneas_exit_code']==0
    assert not inventory['has_errors'] and inventory['source_patches']==[] and not inventory['llbc_preprocessing']
    assert inventory['remaining_external_templates']==[]
    assert digest(HERE/'extract.py')==inventory['script_sha256']
    llbc=HERE/'Artifacts/slice/prost.llbc'
    assert digest(llbc)==inventory['llbc_sha256']=='3f3827ab8889e9723c1bef798c579869e1e17be5d99e55fa696f8cadaa9e354f'
    for name,sha in inventory['source_sha256'].items(): assert digest(ROOT/name)==sha,name
    for name,sha in inventory['generated_files'].items(): assert digest(REFERENCE/name)==sha,name
    vendor=ROOT/'.deps/libsignal-vendor/prost-0.14.4';crate=ROOT/'.deps/libsignal-crates/prost-0.14.4.crate'
    checksum=json.loads((vendor/'.cargo-checksum.json').read_text())
    assert digest(crate)==checksum['package']
    upstream=[]
    with tarfile.open(crate) as archive:
        for member in archive.getmembers():
            if member.isfile():
                prefix,name=member.name.split('/',1);assert prefix=='prost-0.14.4'
                path=vendor/name;assert path.read_bytes()==archive.extractfile(member).read(),name
                upstream.append(path)
    assert set(vendor.rglob('*')) & {p for p in vendor.rglob('*') if p.is_file()} == set(upstream)|{vendor/'.cargo-checksum.json'}
    translated=json.loads(llbc.read_text())['translated']
    selected=[d for d in translated['fun_decls'] if d is not None and d['item_meta'].get('source_text') and
        'fn decode_varint_slice' in d['item_meta']['source_text']]
    assert len(selected)==1
    assert selected[0]['item_meta']['source_text'] in (vendor/'src/encoding/varint.rs').read_text()
    aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve()
    binary_archive=ROOT/'.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    assert digest(binary_archive)==pins['aeneas']['macos_aarch64_archive_sha256']
    with tarfile.open(binary_archive) as archive: assert aeneas.read_bytes()==archive.extractfile('aeneas').read()
    version=subprocess.check_output([str(aeneas),'-version'],text=True).strip()
    assert version==inventory['versions']['aeneas'] and pins['aeneas']['release'] in version
    with tempfile.TemporaryDirectory(prefix='prost-slice-reference-') as temp:
        command=[str(aeneas),'-backend','lean',str(llbc),'-dest',temp,'-subdir','/ProtoParseWork/Generated/slice',
            '-split-files','-namespace','ProstParserReference','-warnings-as-errors','-no-progress-bar']
        subprocess.run(command,cwd=ROOT,check=True,capture_output=True,text=True)
        generated=Path(temp)/'ProtoParseWork/Generated/slice'
        assert {p.name for p in generated.glob('*.lean')}=={'Types.lean','Funs.lean'}
        for path in generated.glob('*.lean'): assert path.read_bytes()==(HERE/'Generated/slice'/path.name).read_bytes(),path.name
    print('Original LLBC reproduced unchanged generated Types/Funs with pinned accepted Aeneas.',flush=True)
    model_archive=REFERENCE/'ProstEncodingWork/AdvanceWork/TranslatorCandidate/aeneas-5b9dcf33.tar.gz'
    assert digest(model_archive)=='ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453'
    official=sorted((MODEL/'Aeneas').rglob('*.lean'))
    with tarfile.open(model_archive) as archive:
        members={m.name.split('/',1)[1]:m for m in archive.getmembers() if m.isfile() and '/' in m.name}
        for path in official:
            relative='backends/lean/'+str(path.relative_to(MODEL))
            assert path.read_bytes()==archive.extractfile(members[relative]).read(),relative
    model_report_path=HERE/'ModelCandidate/build-report.json';model_report=json.loads(model_report_path.read_text())
    shadow_objects={str((HERE/'ModelCandidate/Build'/(m.replace('.','/')+'.olean')).relative_to(ROOT)):
        digest(HERE/'ModelCandidate/Build'/(m.replace('.','/')+'.olean')) for m in model_report['rebuilt_modules']}
    sources={Path(__file__),HERE/'extract.py',inventory_path,llbc,pins_path,crate,binary_archive,aeneas,model_archive,
        model_report_path,HERE/'ModelCandidate/build.py',HERE/'ModelCandidate/slice-model.diff',
        HERE/'ModelCandidate/Aeneas/Std/Slice.lean',HERE/'SliceReference.lean',HERE/'SliceBridge.lean',
        HERE/'Generated/slice/Types.lean',HERE/'Generated/slice/Funs.lean',*official,*upstream,
        *[ROOT/name for name in inventory['source_sha256']]}
    root_modules=[]
    def visit(module):
        if not module.startswith('TlsMpc'):return
        path=ROOT/(module.replace('.','/')+'.lean')
        if path in sources:return
        sources.add(path)
        for name in re.findall(r'^import ([A-Za-z0-9_.]+)',path.read_text(),re.M):visit(name)
        root_modules.append(module)
    visit('TlsMpc.Signal.ProtoParseProofs')
    snapshot={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    # A complete local namespace prevents first-hit module lookup from falling
    # through to an incomplete shadow tree; all used root modules are rebuilt.
    shutil.copytree(ROOT/'.lake/build/lib/lean/TlsMpc',BUILD/'TlsMpc',dirs_exist_ok=True)
    compile_log=[]
    for module in root_modules+['ProtoParseWork.Generated.slice.Types','ProtoParseWork.Generated.slice.Funs',
        'ProtoParseWork.SliceReference','ProtoParseWork.SliceBridge']:
        path=(ROOT if module.startswith('TlsMpc') else REFERENCE)/(module.replace('.','/')+'.lean')
        target=BUILD/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        print('Checking '+module,flush=True)
        run=subprocess.run(['lean','-o',str(target),str(path)],cwd=ROOT if module.startswith('TlsMpc') else REFERENCE,
            env=env,check=True,capture_output=True,text=True)
        compile_log.append(module+'\n'+run.stdout+run.stderr)
    (HERE/'bridge-build.log').write_text('\n'.join(compile_log))
    endpoints=['Aeneas.Std.core.slice.Slice.get_unchecked',
        'Aeneas.Std.core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec',
        'ProstParserReference.encoding.varint.decode_varint_slice']
    for file in ['SliceReference.lean','SliceBridge.lean']:
        endpoints += [NAMESPACE+n for n in re.findall(r'^theorem (\w+)',(HERE/file).read_text(),re.M)]
    audit=BUILD/'Audit.lean';audit.write_text('import ProtoParseWork.SliceBridge\n\n'+'\n'.join('#print axioms '+n for n in endpoints)+'\n')
    run=subprocess.run(['lean',str(audit)],cwd=REFERENCE,env=env,check=True,capture_output=True,text=True)
    found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",run.stdout)
    assert [n for n,_ in found]==endpoints
    allowed={'propext','Quot.sound','Classical.choice'}
    for name,axioms in found: assert not ({a.strip() for a in axioms.split(',') if a.strip()}-allowed),name
    (HERE/'bridge-axioms.txt').write_text(run.stdout)
    assert snapshot=={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    assert shadow_objects=={name:digest(ROOT/name) for name in shadow_objects}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_only':True,'accepted_reference':False,
        'independent_review':'Pending parent review; this check does not self-accept the model extension or reference.',
        'source_sha256':snapshot,'model_shadow_olean_sha256':shadow_objects,
        'model_build_report_sha256':digest(model_report_path),'model_diff_sha256':digest(HERE/'ModelCandidate/slice-model.diff'),
        'actual_rust_function':'prost0.14.4::encoding::varint::decode_varint_slice',
        'actual_rust_source':'src/encoding/varint.rs:71-147','upstream_crate_sha256':digest(crate),
        'verified_upstream_files':len(upstream),'verified_original_aeneas_sources':len(official),
        'llbc_sha256':digest(llbc),'unchanged_generated_files':inventory['generated_files'],
        'original_llbc_retranslation_matched':True,'translator_binary_archive_verified':True,
        'source_patches':[],'llbc_preprocessing':False,'generated_lean_modified':False,
        'isolated_root_modules_recompiled':root_modules,'reference_modules_recompiled':4,
        'checked_endpoints':len(endpoints),'endpoints':endpoints,'allowed_foundational_axioms':sorted(allowed),
        'custom_axioms':[],'axiom_report_sha256':digest(HERE/'bridge-axioms.txt'),
        'compile_log_sha256':digest(HERE/'bridge-build.log'),
        'full_functional_bridge':True,'all_11_branches_proved':True,
        'preconditions':'Nonempty slice and (length>10 or final byte<128). preconditions_iff establishes exact final-byte formulation.',
        'unsafe_access_coverage':'access_bound/prefix_access prove every reached index0..9 bounded from prior continuation bytes and actual preconditions; each actual branch uses these bounds.',
        'success':'Strict ProtoParse.decodePrefix status255, exact u64 value, exact consumed count1..10, including noncanonical encodings.',
        'error':'Exact Rust InvalidVarint error and strict prefix status0 when tenth byte>=2; rejected raw cursor/value fields are not constrained.',
        'numeric_bridge':'decode_refines_artifact proves all numeric AIG output bits for normalized status1||consumedBE8||valueBE8; all17 bytes zero on error.',
        'quantification':'Arbitrary Slice U8 satisfying actual preconditions, arbitrary symbolic inputs/assignment matching its bytes; no fixed byte values or fixtures used as axioms.',
        'model_extension_trust':'Only ModelCandidate/slice-model.diff: get_unchecked delegates to checked SliceIndexInst.index; valid usize spec proved. Rust valid unsafe usize indexing returns that element. No out-of-bounds UB semantics claim.',
        'not_claimed':['Actual outer decode_varint wrapper, streaming slow path, decode_key, skip_field or whole Prost/Signal parser equivalence.',
            'Empty slices or short slices whose final byte has the continuation bit set: outside the actual fast-path preconditions.',
            'Independent model acceptance, new security guarantees, runtime fixtures, backend compilation or native MPC execution.']}
    path=HERE/'bridge-proof-report.json';path.write_text(json.dumps(report,indent=2)+'\n')
    print('bridge-proof-report.json SHA256: '+digest(path),flush=True)

if __name__=='__main__':main()
