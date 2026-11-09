#!/usr/bin/env python3
"""Scoped unused opaque Step metadata selector; extra trusted preprocessing, not a theorem."""
import copy,hashlib,json,pathlib,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sys.path.insert(0,str(REF));from MetadataWork.trim_step_metadata import walk,reviewed_input_fingerprint
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 original=HERE/'Artifacts/xor.llbc';before=json.loads(original.read_text());assert reviewed_input_fingerprint(before)=='45a98c73f2cebfd50619ec2a8e979989af4debe50a6e375c986e2c590fa942ac'
 after=copy.deepcopy(before);tr=after['translated'];changes=[]
 def change(path,value):
  p=after
  for k in path[:-1]:p=p[k]
  changes.append(dict(path=path,before=copy.deepcopy(p[path[-1]]),after=value));p[path[-1]]=value
 for slot,fid,name in [(2,96,'forward_overflowing'),(6,100,'backward_overflowing')]:
  assert tr['trait_decls'][2]['methods'][slot]['skip_binder']['name']==name
  assert tr['trait_impls'][4]['methods'][slot]['skip_binder']['id']==fid
  assert tr['fun_decls'][fid]['body']=='Opaque'
  change(['translated','trait_decls',2,'methods',slot],None);change(['translated','trait_impls',4,'methods',slot],None);change(['translated','fun_decls',fid],None)
 change(['translated','ordered_decls'],[x for x in tr['ordered_decls']if x not in [{'Fun':{'NonRec':96}},{'Fun':{'NonRec':100}}]])
 restored=copy.deepcopy(after)
 for c in changes:
  p=restored
  for k in c['path'][:-1]:p=p[k]
  p[c['path'][-1]]=c['before']
 assert restored==before
 semantic={k:v for k,v in tr.items()if k not in ['item_names','short_names']}
 for node in walk(semantic):
  if isinstance(node,dict):
   assert node.get('Regular')not in[96,100];assert node.get('TraitMethod')not in[[2,2],[2,6]]
   if isinstance(node.get('skip_binder'),dict):assert node['skip_binder'].get('id')not in[96,100]
 for i,f in enumerate(before['translated']['fun_decls']):
  if f and f['body']!='Opaque':assert f==tr['fun_decls'][i]
 art=HERE/'ArtifactsSelected';art.mkdir(exist_ok=False);selected=art/'selected.llbc';selected.write_text(json.dumps(after,separators=(',',':'))+'\n');(art/'changes.json').write_text(json.dumps(changes,indent=2)+'\n')
 dest=HERE/'GeneratedSelected';dest.mkdir();a=ROOT/'.deps/aeneas-2026-08-27/aeneas';args=[str(a),'-backend','lean',str(selected),'-dest',str(REF),'-subdir','/CtrReferenceV1Work/XorContentV1Work/GeneratedSelected','-split-files','-namespace','ActualXorContent16','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report=dict(candidate_only=True,accepted=False,additional_translation_trust_not_mechanized=True,reversible_metadata_changes=len(changes),all_retained_computational_bodies_identical=True,no_retained_semantic_refs_to_removed_opaque_fields=True,removed_functions=[96,100],original_sha256=sha(original),selected_sha256=sha(selected),changes_sha256=sha(art/'changes.json'),script_sha256=sha(pathlib.Path(__file__)),aeneas_exit=r.returncode,command=args,generated_sha256={str(p.relative_to(ROOT)):sha(p)for p in dest.glob('*.lean')});(HERE/'selection-report.json').write_text(json.dumps(report,indent=2)+'\n');print('metadata-only XOR translation',r.returncode)
if __name__=='__main__':main()
