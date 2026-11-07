#!/usr/bin/env python3
"""Freeze/reproduce the candidate actual Prost full-varint bridge, without self-acceptance.
No original Rust, generated computational Lean, frozen leaf proof, or backend files are modified.
"""
from datetime import datetime, timezone
import copy,difflib,hashlib,json,re,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
import check,port_slice
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent;REFERENCE=PARENT.parent;ROOT=REFERENCE.parent
BUILD=HERE/'Build';FULL='LibSignalReference.Candidate.ProstFull.';SLICE='LibSignalReference.Candidate.ProstFullSlice.'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def walk(x):
    yield x
    if isinstance(x,dict):
        for y in x.values():yield from walk(y)
    elif isinstance(x,list):
        for y in x:yield from walk(y)
def main():
    env=check.env() # verifies every source frozen by the separately accepted leaf audit
    accepted_path=PARENT/'root-review.json';accepted=json.loads(accepted_path.read_text())
    assert accepted['decision']=='accepted_with_explicit_model_boundary'
    for name,sha in accepted['artifact_sha256'].items():assert digest(PARENT/name)==sha,name
    frozen=json.loads((PARENT/'bridge-proof-report.json').read_text())
    for name,sha in frozen['model_shadow_olean_sha256'].items():assert digest(ROOT/name)==sha,name
    inventory_path=PARENT/'Artifacts/varint/inventory.json';inventory=json.loads(inventory_path.read_text())
    assert inventory['charon_exit_code']==0 and not inventory['has_errors']
    assert inventory['source_patches']==[] and not inventory['llbc_preprocessing']
    assert digest(PARENT/'extract.py')==inventory['script_sha256']
    for name,sha in inventory['source_sha256'].items():assert digest(ROOT/name)==sha,name
    original=PARENT/'Artifacts/varint/prost.llbc';selected=PARENT/'Artifacts/varint-step/selected.llbc'
    changes_path=PARENT/'Artifacts/varint-step/changes.json';selection_path=PARENT/'Artifacts/varint-step/review.json'
    selection=json.loads(selection_path.read_text())
    assert selection['candidate_only'] and not selection['accepted_reference']
    assert digest(original)==inventory['llbc_sha256']==selection['original_sha256']
    assert digest(selected)==selection['selected_sha256'] and digest(changes_path)==selection['changes_sha256']
    assert digest(PARENT/'select_step_metadata.py')==selection['script_sha256']
    before=json.loads(original.read_text());after=json.loads(selected.read_text());changes=json.loads(changes_path.read_text())
    expected={('translated','fun_decls',i) for i in (297,301)}|{('translated',k,i,'methods',j) for k,i in [('trait_decls',11),('trait_impls',19)] for j in (2,6)}|{('translated','ordered_decls')}
    assert len(changes)==7 and {tuple(c['path']) for c in changes}==expected
    replay=copy.deepcopy(before);restored=copy.deepcopy(after)
    for change in changes:
        a=replay;b=restored
        for k in change['path'][:-1]:a=a[k];b=b[k]
        key=change['path'][-1]
        assert a[key]==change['before'] and b[key]==change['after']
        a[key]=change['after'];b[key]=change['before']
    assert replay==after and restored==before
    tr=after['translated'];retained=0
    for i,f in enumerate(before['translated']['fun_decls']):
        if f and f['body']!='Opaque':assert f==tr['fun_decls'][i];retained+=1
    for slot,fid,name in ((2,297,'forward_overflowing'),(6,301,'backward_overflowing')):
        assert before['translated']['trait_decls'][11]['methods'][slot]['skip_binder']['name']==name
        assert before['translated']['trait_impls'][19]['methods'][slot]['skip_binder']['id']==fid
        assert before['translated']['fun_decls'][fid]['body']=='Opaque'
        assert tr['trait_decls'][11]['methods'][slot] is None and tr['trait_impls'][19]['methods'][slot] is None and tr['fun_decls'][fid] is None
    assert tr['ordered_decls']==[d for d in before['translated']['ordered_decls'] if d not in [{'Fun':{'NonRec':i}} for i in (297,301)]]
    for node in walk({k:v for k,v in tr.items() if k not in ('item_names','short_names')}):
        if isinstance(node,dict):
            assert node.get('Regular') not in (297,301)
            assert node.get('TraitMethod') not in [[11,2],[11,6]]
            if isinstance(node.get('skip_binder'),dict):assert node['skip_binder'].get('id') not in (297,301)
    upstream=[];crates=[]
    for package in ('prost-0.14.4','bytes-1.12.0'):
        vendor=ROOT/'.deps/libsignal-vendor'/package;crate=ROOT/'.deps/libsignal-crates'/(package+'.crate');crates.append(crate)
        checksum=json.loads((vendor/'.cargo-checksum.json').read_text());assert digest(crate)==checksum['package']
        with tarfile.open(crate) as archive:
            for member in archive.getmembers():
                if not member.isfile():continue
                prefix,name=member.name.split('/',1);assert prefix==package
                path=vendor/name;assert path.read_bytes()==archive.extractfile(member).read(),name
                upstream.append(path)
    rust=ROOT/'.deps/libsignal-vendor/prost-0.14.4/src/encoding/varint.rs'
    names=('decode_varint','decode_varint_slice','decode_varint_slow')
    actual={}
    for name in names:
        fs=[f for f in before['translated']['fun_decls'] if f and re.search(r'\bfn '+name+r'\s*[<(]',f['item_meta'].get('source_text') or '')]
        assert len(fs)==1 and fs[0]['item_meta']['source_text'] in rust.read_text(),name
        actual[name]=hashlib.sha256(fs[0]['item_meta']['source_text'].encode()).hexdigest()
    pins=json.loads((REFERENCE/'pins.json').read_text());aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve()
    binary_archive=ROOT/'.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    assert digest(binary_archive)==pins['aeneas']['macos_aarch64_archive_sha256']
    with tarfile.open(binary_archive) as archive:assert aeneas.read_bytes()==archive.extractfile('aeneas').read()
    assert subprocess.check_output([str(aeneas),'-version'],text=True).strip()==inventory['versions']['aeneas']
    for name,sha in selection['generated_files'].items():assert digest(REFERENCE/name)==sha,name
    with tempfile.TemporaryDirectory(prefix='prost-full-reference-') as temp:
        subprocess.run([str(aeneas),'-backend','lean',str(selected),'-dest',temp,'-subdir','/ProtoParseWork/Generated/varint_step','-split-files','-namespace','ProstParserFullCandidate','-warnings-as-errors','-no-progress-bar'],cwd=ROOT,check=True,capture_output=True,text=True)
        generated=Path(temp)/'ProtoParseWork/Generated/varint_step'
        assert {p.name for p in generated.glob('*.lean')}=={'Types.lean','Funs.lean','FunsExternal_Template.lean'}
        for path in generated.glob('*.lean'):assert path.read_bytes()==(PARENT/'Generated/varint_step'/path.name).read_bytes(),path.name
    print('Verified exactly seven metadata changes and unchanged generated computational bodies.',flush=True)
    replay_before={p.name:digest(p) for p in [HERE/'SliceReference.lean',HERE/'SliceBridge.lean']}
    port_slice.main()
    assert replay_before=={p.name:digest(p) for p in [HERE/'SliceReference.lean',HERE/'SliceBridge.lean']}
    external=HERE/'Modules/ProtoParseWork/Generated/varint_step/FunsExternal.lean'
    template=PARENT/'Generated/varint_step/FunsExternal_Template.lean'
    delta=HERE/'buf-model.diff';delta.write_text(''.join(difflib.unified_diff(template.read_text().splitlines(True),external.read_text().splitlines(True),fromfile='generated/FunsExternal_Template.lean',tofile='candidate/FunsExternal.lean')))
    sources={ROOT/name for name in frozen['source_sha256']}|{ROOT/name for name in inventory['source_sha256']}
    sources|={Path(__file__),HERE/'check.py',HERE/'port_slice.py',HERE/'slice-proof-replay.json',external,delta,accepted_path,PARENT/'bridge-proof-report.json',inventory_path,original,selected,changes_path,selection_path,PARENT/'select_step_metadata.py',*upstream,*crates}
    sources|=set(HERE.glob('*.lean'))|set((PARENT/'Generated/varint_step').glob('*.lean'))|{HERE/'REVIEW.md'}
    snapshot={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    logs=[]
    shutil.copytree(PARENT/'BridgeBuild/TlsMpc',BUILD/'TlsMpc',dirs_exist_ok=True)
    for module in frozen['isolated_root_modules_recompiled']:
        source=ROOT/(module.replace('.','/')+'.lean');out=BUILD/(module.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
        print('Checking '+module,flush=True)
        run=subprocess.run(['lean','-o',str(out),str(source)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
        logs.append(module+'\n'+run.stdout+run.stderr)
    run=subprocess.run([sys.executable,str(HERE/'check.py')],cwd=ROOT,check=True,capture_output=True,text=True)
    logs.append(run.stdout+run.stderr);(HERE/'build.log').write_text('\n'.join(logs))
    endpoints=['Aeneas.Std.core.slice.Slice.get_unchecked','Aeneas.Std.core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec',
      'ProstParserFullCandidate.bytes.buf.buf_impl.Buf.get_u8.default',
      'ProstParserFullCandidate.Mut0T.Insts.BytesBufBuf_implBuf.remaining',
      'ProstParserFullCandidate.Mut0T.Insts.BytesBufBuf_implBuf.chunk',
      *['ProstParserFullCandidate.encoding.varint.'+name for name in ('decode_varint_slice','decode_varint_slow_loop.body','decode_varint_slow_loop','decode_varint_slow','decode_varint')]]
    for name in ('SliceReference','SliceBridge','BufModel','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption'):
        prefix=SLICE if name.startswith('Slice') else FULL
        endpoints += [prefix+n for n in re.findall(r'^theorem (\w+)',(HERE/(name+'.lean')).read_text(),re.M)]
    audit=BUILD/'Audit.lean';audit.write_text('import ProtoParseWork.FullReferenceWork.Consumption\n\n'+'\n'.join('#print axioms '+n for n in endpoints)+'\n')
    run=subprocess.run(['lean',str(audit)],cwd=REFERENCE,env=env,check=True,capture_output=True,text=True)
    found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",run.stdout)
    assert [n for n,_ in found]==endpoints
    allowed={'propext','Quot.sound','Classical.choice'}
    for name,axioms in found:assert not ({a.strip() for a in axioms.split(',') if a.strip()}-allowed),name
    (HERE/'axioms.txt').write_text(run.stdout)
    assert snapshot=={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    for name,sha in frozen['model_shadow_olean_sha256'].items():assert digest(ROOT/name)==sha,name
    reference_modules=['ProtoParseWork.Generated.varint_step.'+n for n in ('Types','FunsExternal','Funs')]+['ProtoParseWork.FullReferenceWork.'+n for n in ('BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption')]
    object_hashes={str((BUILD/(m.replace('.','/')+'.olean')).relative_to(ROOT)):digest(BUILD/(m.replace('.','/')+'.olean')) for m in frozen['isolated_root_modules_recompiled']+reference_modules}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_only':True,'accepted_reference':False,
      'independent_review':'Pending independent acceptance of the seven metadata changes and Buf models; scoped leaf accepted separately.',
      'source_sha256':snapshot,'accepted_leaf_review_sha256':digest(accepted_path),'model_shadow_olean_sha256':frozen['model_shadow_olean_sha256'],
      'actual_rust_functions':actual,'verified_prost_and_bytes_upstream_files':len(upstream),'source_patches':[],
      'llbc_preprocessing':{'reversible_changes':7,'retained_computational_bodies_identical':retained,'removed_opaque_function_ids':[297,301],
        'no_retained_semantic_references_to_removed_slots':True,'trait_slot_numbers_preserved':True,'changes_sha256':digest(changes_path),'additional_translation_trust':True},
      'generated_lean_modified':False,'selected_llbc_retranslation_matched':True,'pinned_translator_binary_verified':True,
      'slice_proof_replay':json.loads((HERE/'slice-proof-replay.json').read_text()),
      'new_model_boundary':{'external_functions':3,'source':'bytes1.12.0/src/buf/buf_impl.rs:320-331,2464-2471,2894-2918',
        'description':'Default get_u8 checks remaining, reads chunk[0], advances1; mutable remaining/chunk forward to Buf; concrete &[u8] remaining/chunk/advance are length/self/checked suffix.',
        'diff_sha256':digest(delta),'standard_model_specs_kernel_checked':True,'rust_model_faithfulness_is_explicit_review_assumption':True},
      'unsafe_index_boundary':'Separately accepted leaf model: valid usize unsafe indexing agrees with checked indexing. Every reached access bounded. No UB semantics claim.',
      'isolated_root_modules_recompiled':frozen['isolated_root_modules_recompiled'],'reference_modules_recompiled':reference_modules,'rebuilt_olean_sha256':object_hashes,
      'checked_endpoints':len(endpoints),'endpoints':endpoints,'allowed_foundational_axioms':sorted(allowed),'custom_axioms':[],
      'axiom_report_sha256':digest(HERE/'axioms.txt'),'compile_log_sha256':digest(HERE/'build.log'),
      'full_functional_bridge':True,'preconditions':'Every contiguous Slice U8, including empty, truncated, overflowing and noncanonical encodings. Slice length is represented by valid usize. No nonempty/last-byte caller promise.',
      'success':'Strict prefix status255, exact u64 value, consumed count<=10 and<=original length, exact remaining suffix.',
      'error':'Exact InvalidVarint and strict prefix status0. Fast guard (length>10 or last<128) preserves original buffer on error; otherwise consumes min(10,length). Empty input remains empty.',
      'numeric_bridge':'ArtifactBridge.decode_refines_artifact universally proves all17-byte numeric AIG bits: status1||consumedBE8||valueBE8; all17 bytes zero on error. Success count measured from actual mutable suffix.',
      'not_claimed':['Arbitrary segmented/custom Buf implementations.','Whole Prost parser, decode_key, skip_field or whole Signal refinement.','Runtime fixtures, backend compilation, native MPC execution or new security guarantees.','Independent acceptance of this new full-wrapper candidate.']}
    path=HERE/'proof-report.json';path.write_text(json.dumps(report,indent=2)+'\n')
    print('Audited '+str(len(endpoints))+' endpoints. proof-report.json SHA256: '+digest(path),flush=True)
if __name__=='__main__':main()
