#!/usr/bin/env python3
"""Replay exact unused Step metadata selection; reject unresolved packaging."""
import copy,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 original=HERE/'Artifacts/WireFields/ss_content.llbc';selected=HERE/'Artifacts/WireFieldsSelected/selected.llbc'
 before=json.loads(original.read_text());after=json.loads(selected.read_text());changes=json.loads((selected.parent/'changes.json').read_text())
 replay=copy.deepcopy(before)
 for change in changes:
  at=replay
  for k in change['path'][:-1]:at=at[k]
  assert at[change['path'][-1]]==change['before'];at[change['path'][-1]]=change['after']
 assert replay==after and len(changes)==7
 originalBodies=[]
 for i,f in enumerate(before['translated']['fun_decls']):
  if f and f['body']!='Opaque':assert after['translated']['fun_decls'][i]==f;originalBodies.append(i)
 assert len(before['translated']['ordered_decls'])>0
 root=before['translated']['fun_decls'][0];assert root['body']!='Opaque'
 assert 'encode_raw' in str(root['item_meta']['name'])
 review=json.loads((selected.parent/'review.json').read_text());assert review['aeneas_exit_code']==0
 for name,digest in review['generated_files'].items():assert sha(HERE.parent/name)==digest,name
 templates=list((HERE/'Generated/WireFieldsSelected').glob('*_Template.lean'));assert templates
 report={'candidate_only':True,'accepted_reference':False,'actual_SS_packaging_refinement_established':False,'step_metadata_changes':7,'all_retained_computational_bodies_unchanged':originalBodies,'source_patches':[],'manual_generated_body_edits':False,
 'real_derive_encoder_roots_present':True,'unresolved_external_templates':[p.name for p in templates],
 'remaining':['Actual full constructor pulls mixed recursive bytes vtables through prost Message trait.','Actual derive encoder still needs closed concrete BytesAdapter/BufMut payload append bridge. Std Vec access/default calls and unused unsafe metadata are not silently interpreted as proved implementations.','Generated primitive field references are candidates only; exact seven Step deletions require separate review.'],
 'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__),HERE/'extract.py',HERE/'select_step_metadata.py',HERE/'translate_loop_candidate.py',original,selected,selected.parent/'changes.json',selected.parent/'review.json']}}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Exact7 metadata replay/unchanged real encoder bodies passed; unresolved packaging remains rejected')
if __name__=='__main__':main()
