#!/usr/bin/env python3
"""Candidate-only exact removal of unused opaque Step dictionary metadata.
All retained computational bodies and trait slot numbering remain unchanged.
This is explicit additional translation trust, not a Lean theorem.
"""
import copy,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;REFERENCE=HERE.parent.parent;ROOT=REFERENCE.parent
sys.path.insert(0,str(REFERENCE))
from MetadataWork.trim_step_metadata import walk,reviewed_input_fingerprint,digest
FINGERPRINT='c6eac4086e925dc1a6b56c8b6e08ad1ff692520083e84a1fd44457b416003570'
def main():
    original=HERE/'Artifacts/skip/prost.llbc';before=json.loads(original.read_text());assert reviewed_input_fingerprint(before)==FINGERPRINT
    after=copy.deepcopy(before);tr=after['translated'];changes=[]
    def remove(path):
        p=after
        for k in path[:-1]:p=p[k]
        changes.append({'path':path,'before':p[path[-1]],'after':None});p[path[-1]]=None
    removed=(311,315);trait=13;impl=26
    for slot,fid,name in ((2,311,'forward_overflowing'),(6,315,'backward_overflowing')):
        assert tr['trait_decls'][trait]['methods'][slot]['skip_binder']['name']==name
        assert tr['trait_impls'][impl]['methods'][slot]['skip_binder']['id']==fid
        assert tr['fun_decls'][fid]['body']=='Opaque'
        remove(['translated','trait_decls',trait,'methods',slot]);remove(['translated','trait_impls',impl,'methods',slot]);remove(['translated','fun_decls',fid])
    old=tr['ordered_decls'];tr['ordered_decls']=[d for d in old if d not in [{'Fun':{'NonRec':i}} for i in removed]]
    changes.append({'path':['translated','ordered_decls'],'before':old,'after':tr['ordered_decls']})
    restored=copy.deepcopy(after)
    for change in changes:
        p=restored
        for k in change['path'][:-1]:p=p[k]
        p[change['path'][-1]]=change['before']
    assert restored==before
    semantic={k:v for k,v in tr.items() if k not in('item_names','short_names')}
    for node in walk(semantic):
        if isinstance(node,dict):
            assert node.get('Regular') not in removed
            assert node.get('TraitMethod') not in [[trait,2],[trait,6]]
            if isinstance(node.get('skip_binder'),dict):assert node['skip_binder'].get('id') not in removed
    for i,fun in enumerate(before['translated']['fun_decls']):
        if fun and fun['body']!='Opaque':assert fun==tr['fun_decls'][i]
    dest=HERE/'Artifacts/skip-step';dest.mkdir(parents=True,exist_ok=True);selected=dest/'selected.llbc';selected.write_text(json.dumps(after,separators=(',',':'))+'\n')
    delta=dest/'changes.json';delta.write_text(json.dumps(changes,indent=2)+'\n');generated=HERE/'Generated/skip_step';generated.mkdir(parents=True,exist_ok=True)
    for p in generated.glob('*.lean'):p.unlink()
    command=[str(ROOT/'.deps/aeneas-2026-08-27/aeneas'),'-backend','lean',str(selected),'-dest',str(REFERENCE),'-subdir','/ProtoParseWork/KeyReferenceWork/Generated/skip_step','-split-files','-namespace','ProstSkipCandidate','-warnings-as-errors','-no-progress-bar']
    with(dest/'aeneas.log').open('w') as log:r=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    report={'candidate_only':True,'accepted_reference':False,'original_sha256':digest(original),'original_fingerprint':FINGERPRINT,'selected_sha256':digest(selected),'changes_sha256':digest(delta),'script_sha256':digest(Path(__file__)),'reversible_changes':len(changes),'removed_functions':list(removed),'all_retained_computational_bodies_identical':True,'no_retained_semantic_references_to_removed_slots':True,'additional_trusted_preprocessing':True,'source_or_translator_changes':[],'aeneas_exit_code':r.returncode,'generated_files':{str(p.relative_to(REFERENCE)):digest(p) for p in generated.glob('*.lean')},'external_templates':[p.name for p in generated.glob('*_Template.lean')],'independent_review':'pending'}
    (dest/'review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
