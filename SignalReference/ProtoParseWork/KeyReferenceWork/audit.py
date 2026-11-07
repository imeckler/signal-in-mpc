#!/usr/bin/env python3
"""Reproduce the actual Prost decode_key candidate without self-acceptance."""
from datetime import datetime,timezone
import copy,hashlib,json,re,shutil,subprocess,sys,tarfile,tempfile
from pathlib import Path
import check,replay
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent;FULL=PARENT/'FullReferenceWork';REFERENCE=PARENT.parent;ROOT=REFERENCE.parent;BUILD=HERE/'Build'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def walk(x):
    yield x
    if isinstance(x,dict):
        for y in x.values():yield from walk(y)
    elif isinstance(x,list):
        for y in x:yield from walk(y)
def verify_selection(profile,trait,impl,removed,expected_original,aeneas):
    inventory_path=HERE/'Artifacts'/profile/'inventory.json';inventory=json.loads(inventory_path.read_text())
    dest=HERE/'Artifacts'/(profile+'-step');review_path=dest/'review.json';r=json.loads(review_path.read_text())
    original=HERE/'Artifacts'/profile/'prost.llbc';selected=dest/'selected.llbc';delta=dest/'changes.json'
    script=HERE/('select_step_metadata.py' if profile=='key' else 'select_skip_metadata.py')
    assert inventory['charon_exit_code']==0 and not inventory['has_errors']
    assert inventory['source_patches']==[] and not inventory['llbc_preprocessing']
    assert digest(HERE/'extract.py')==inventory['script_sha256']
    for name,sha in inventory['source_sha256'].items():assert digest(ROOT/name)==sha,name
    assert digest(original)==expected_original==inventory['llbc_sha256']==r['original_sha256']
    assert digest(selected)==r['selected_sha256'] and digest(delta)==r['changes_sha256'] and digest(script)==r['script_sha256']
    before=json.loads(original.read_text());after=json.loads(selected.read_text());changes=json.loads(delta.read_text())
    expected={('translated','fun_decls',i) for i in removed}|{('translated',k,i,'methods',j) for k,i in [('trait_decls',trait),('trait_impls',impl)] for j in (2,6)}|{('translated','ordered_decls')}
    assert len(changes)==7 and {tuple(c['path']) for c in changes}==expected
    patched=copy.deepcopy(before);restored=copy.deepcopy(after)
    for c in changes:
      a=patched;b=restored
      for k in c['path'][:-1]:a=a[k];b=b[k]
      k=c['path'][-1];assert a[k]==c['before'] and b[k]==c['after'];a[k]=c['after'];b[k]=c['before']
    assert patched==after and restored==before
    tr=after['translated'];retained=0
    for i,f in enumerate(before['translated']['fun_decls']):
      if f and f['body']!='Opaque':assert f==tr['fun_decls'][i];retained+=1
    for slot,fid,name in ((2,removed[0],'forward_overflowing'),(6,removed[1],'backward_overflowing')):
      assert before['translated']['trait_decls'][trait]['methods'][slot]['skip_binder']['name']==name
      assert before['translated']['trait_impls'][impl]['methods'][slot]['skip_binder']['id']==fid
      assert before['translated']['fun_decls'][fid]['body']=='Opaque'
    assert tr['ordered_decls']==[d for d in before['translated']['ordered_decls'] if d not in [{'Fun':{'NonRec':i}} for i in removed]]
    for node in walk({k:v for k,v in tr.items() if k not in ('item_names','short_names')}):
      if isinstance(node,dict):
        assert node.get('Regular') not in removed and node.get('TraitMethod') not in [[trait,2],[trait,6]]
        if isinstance(node.get('skip_binder'),dict):assert node['skip_binder'].get('id') not in removed
    for name,sha in r['generated_files'].items():assert digest(REFERENCE/name)==sha,name
    ns='ProstKeyCandidate' if profile=='key' else 'ProstSkipCandidate';expected_exit=0 if profile=='key' else 1
    assert r['aeneas_exit_code']==expected_exit
    with tempfile.TemporaryDirectory(prefix='prost-'+profile+'-reference-') as temp:
      run=subprocess.run([str(aeneas),'-backend','lean',str(selected),'-dest',temp,'-subdir','/ProtoParseWork/KeyReferenceWork/Generated/'+profile+'_step','-split-files','-namespace',ns,'-warnings-as-errors','-no-progress-bar'],cwd=ROOT,capture_output=True,text=True)
      assert run.returncode==expected_exit
      if profile=='skip':assert 'Early returns inside of loops are not supported yet' in run.stdout+run.stderr and "Ignoring the body of 'prost::encoding::skip_field'" in run.stdout+run.stderr
      generated=Path(temp)/('ProtoParseWork/KeyReferenceWork/Generated/'+profile+'_step')
      assert {p.name for p in generated.glob('*.lean')}=={'Types.lean','Funs.lean','FunsExternal_Template.lean'}
      for p in generated.glob('*.lean'):assert p.read_bytes()==(HERE/'Generated'/(profile+'_step')/p.name).read_bytes(),p.name
    sources={inventory_path,review_path,original,selected,delta,script,HERE/'Artifacts'/profile/'charon.log',dest/'aeneas.log',*[REFERENCE/name for name in r['generated_files']]}
    return {'original_sha256':digest(original),'selected_sha256':digest(selected),'changes_sha256':digest(delta),'script_sha256':digest(script),'reversible_changes':7,'trait_id':trait,'impl_id':impl,'removed_opaque_functions':list(removed),'retained_computational_bodies_identical':retained,'no_retained_semantic_references_to_removed_slots':True,'retranslation_matched':True,'aeneas_exit_code':expected_exit},sources,before

def main():
    env=check.env();full_report_path=FULL/'proof-report.json';frozen=json.loads(full_report_path.read_text())
    full_review_path=FULL/'root-review.json';review=json.loads(full_review_path.read_text())
    # Scoped acceptance is recorded separately; candidate reports remain unchanged.
    assert 'accepted' in review['decision']
    for name,sha in frozen['rebuilt_olean_sha256'].items():assert digest(ROOT/name)==sha,name
    for name,sha in frozen['model_shadow_olean_sha256'].items():assert digest(ROOT/name)==sha,name
    pins=json.loads((REFERENCE/'pins.json').read_text());aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve()
    archive=ROOT/'.deps/aeneas-macos-aarch64-2026-08-27.tar.gz';assert digest(archive)==pins['aeneas']['macos_aarch64_archive_sha256']
    with tarfile.open(archive) as tar:assert aeneas.read_bytes()==tar.extractfile('aeneas').read()
    key,source_key,before=verify_selection('key',13,21,(302,306),'ed7af1b2aa58bd39ef192a7f39262ce0117e6faf0ff7dcbd0dcc102dde1d6915',aeneas)
    skip,source_skip,_=verify_selection('skip',13,26,(311,315),'329cf546c014e6f6c81b2660048676ec896aa3a48a1f787121979fc98b44322d',aeneas)
    skip.update({'proof_reference':False,'compiled_or_imported':False,'blocker':'Early returns inside of loops are not supported yet','source':'prost0.14.4/src/encoding.rs:166-199','consequence':'Aeneas ignores the entire skip_field body, including scalar branches. Partial generated files are provenance artifacts only. No actual scalar/group skip proof claimed.'})
    (HERE/'skip-boundary.json').write_text(json.dumps(skip,indent=2)+'\n')
    source_text={}
    for name,path in [('decode_key','encoding.rs'),('try_from','encoding/wire_type.rs')]:
      fs=[f for f in before['translated']['fun_decls'] if f and re.search(r'\bfn '+name+r'\s*[<(]',f['item_meta'].get('source_text') or '')]
      assert len(fs)==1
      text=fs[0]['item_meta']['source_text'];assert text in (ROOT/'.deps/libsignal-vendor/prost-0.14.4/src'/path).read_text()
      source_text[name]=hashlib.sha256(text.encode()).hexdigest()
    replay.main()
    sources={ROOT/name for name in frozen['source_sha256']}|source_key|source_skip|{full_report_path,full_review_path,HERE/'skip-boundary.json',HERE/'replay-report.json',HERE/'REVIEW.md'}
    sources|=set(HERE.glob('*.py'))|set(HERE.glob('*.lean'))|set((HERE/'Replayed').glob('*.lean'))|set((HERE/'Modules').rglob('*.lean'))
    snapshot={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    logs=[];root_modules=frozen['isolated_root_modules_recompiled']
    shutil.copytree(FULL/'Build/TlsMpc',BUILD/'TlsMpc',dirs_exist_ok=True)
    for module in root_modules:
      source=ROOT/(module.replace('.','/')+'.lean');out=BUILD/(module.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
      print('Checking '+module,flush=True)
      run=subprocess.run(['lean','-o',str(out),str(source)],cwd=ROOT,env=env,check=True,capture_output=True,text=True);logs.append(module+'\n'+run.stdout+run.stderr)
    run=subprocess.run([sys.executable,str(HERE/'check.py')],cwd=ROOT,check=True,capture_output=True,text=True);logs.append(run.stdout+run.stderr)
    (HERE/'build.log').write_text('\n'.join(logs))
    endpoints=[n.replace('LibSignalReference.Candidate.ProstFullSlice','LibSignalReference.Candidate.ProstKeySlice').replace('LibSignalReference.Candidate.ProstFull','LibSignalReference.Candidate.ProstKeyVarint').replace('ProstParserFullCandidate','ProstKeyCandidate') for n in frozen['endpoints']]
    endpoints+=['ProstKeyCandidate.encoding.wire_type.WireType.Insts.CoreConvertTryFromU64DecodeError.try_from','ProstKeyCandidate.encoding.decode_key']
    for name in ('KeyValue','KeyReference','KeyCircuit','PlanBridge','ArtifactBridge'):
      endpoints+=['LibSignalReference.Candidate.ProstKey.'+n for n in re.findall(r'^theorem (\w+)',(HERE/(name+'.lean')).read_text(),re.M)]
    audit=BUILD/'KeyAudit.lean';audit.write_text('import ProtoParseWork.KeyReferenceWork.ArtifactBridge\n\n'+'\n'.join('#print axioms '+n for n in endpoints)+'\n')
    run=subprocess.run(['lean',str(audit)],cwd=REFERENCE,env=env,check=True,capture_output=True,text=True)
    found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",run.stdout)
    assert [n for n,_ in found]==endpoints
    allowed={'propext','Classical.choice','Quot.sound'}
    for name,axioms in found:assert not ({a.strip() for a in axioms.split(',') if a.strip()}-allowed),name
    (HERE/'axioms.txt').write_text(run.stdout)
    assert snapshot=={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    for name,sha in frozen['rebuilt_olean_sha256'].items():assert digest(ROOT/name)==sha,name
    for name,sha in frozen['model_shadow_olean_sha256'].items():assert digest(ROOT/name)==sha,name
    modules=['ProtoParseWork.KeyReferenceWork.Generated.key_step.'+n for n in ('Types','FunsExternal','Funs')]+['ProtoParseWork.KeyReferenceWork.Replayed.'+n for n in replay.FILES]+['ProtoParseWork.KeyReferenceWork.'+n for n in ('KeyValue','KeyReference','KeyCircuit','PlanBridge','ArtifactBridge')]
    objects={str((BUILD/(m.replace('.','/')+'.olean')).relative_to(ROOT)):digest(BUILD/(m.replace('.','/')+'.olean')) for m in root_modules+modules}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'candidate_only':True,'accepted_reference':False,'independent_review':'Pending independent review of this key extraction, selection and bridge. Full varint accepted separately within explicit model scope.',
      'source_sha256':snapshot,'rebuilt_olean_sha256':objects,'model_shadow_olean_sha256':frozen['model_shadow_olean_sha256'],
      'full_varint_review_sha256':digest(full_review_path),'full_varint_report_sha256':digest(full_report_path),'actual_rust_function_source_sha256':source_text,
      'metadata_selection':key,'additional_translation_trust':True,'source_patches':[],'generated_computational_files_modified':False,
      'proof_and_model_replay':json.loads((HERE/'replay-report.json').read_text()),'new_external_models':0,'reused_buf_wrappers':3,
      'model_boundary':'Separately accepted contiguous &[u8] Buf wrappers and valid-usize unsafe-index model; every replayed proof rechecked against unchanged key-extraction bodies. No arbitrary Buf or Rust UB claim.',
      'isolated_root_modules_recompiled':root_modules,'reference_modules_recompiled':modules,'checked_endpoints':len(endpoints),'endpoints':endpoints,'allowed_foundational_axioms':sorted(allowed),'custom_axioms':[],
      'axiom_report_sha256':digest(HERE/'axioms.txt'),'compile_log_sha256':digest(HERE/'build.log'),
      'preconditions':'Every contiguous Slice U8, including empty/truncated/overflowing/noncanonical input. No caller fast-path promise.',
      'success':'Exact tag=value/8, wireType=value%8, tag>=1, key<=u32::MAX, wireType<=5, strict-prefix value/count and actual suffix.',
      'errors':'Exact validation order and InvalidKey(value)/InvalidWireType(low3bits)/InvalidTag after successful varint; validation leaves its consumed suffix unchanged. Varint errors propagate exact InvalidVarint and inherited failure mutation.',
      'parser_connection':'Existing ProtoParse.plan tag/kind fields coincide; every actual key error forces plan.ok=0 for all payloads and states. No payload success equivalence asserted.',
      'numeric_artifact':'Universally quantified bitwise25-byte AIG refinement: status1||consumedBE8||tagBE8||wireTypeBE8; all25 bytes zero on error.',
      'skip_field':skip,'not_claimed':['Actual scalar/group skip_field refinement: translator omits its body.','Arbitrary segmented Buf, whole Prost parser or whole Signal refinement.','Runtime fixture evaluation, backend compilation or native MPC execution.','Independent acceptance of this new key candidate.']}
    path=HERE/'proof-report.json';path.write_text(json.dumps(report,indent=2)+'\n')
    print('Audited '+str(len(endpoints))+' endpoints. proof-report.json SHA256: '+digest(path),flush=True)
if __name__=='__main__':main()
