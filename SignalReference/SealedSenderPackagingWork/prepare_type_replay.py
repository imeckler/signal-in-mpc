#!/usr/bin/env python3
"""Deterministic type-export naming replay; generated Funs bytes untouched.
Anonymous discriminant instance names otherwise collide between independent
actual extraction namespaces. Preserve the original API through definitional
aliases; rename only the type family export, never a computation.
"""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];REF=HERE.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 rows=[]
 for namespace,module,path in [
  ('ProstBytesField','SignalMessageWork/BytesFieldWork/GeneratedSelected','encoding.wire_type.WireType'),
  ('SealedSenderPackaging','SealedSenderPackagingWork/Generated/WireContent','prost.encoding.wire_type.WireType')]:
  original=REF/module/'Types.lean';before=original.read_text();assert before.count('inductive '+path+' where')==1
  qualified=namespace+'.'+path;fresh=path+'_n_'+qualified.encode().hex()
  changed=before.replace(path,fresh)
  variants=['Varint','SixtyFourBit','LengthDelimited','StartGroup','EndGroup','ThirtyTwoBit']
  assert [line.split(':')[0].strip()for line in before.split('inductive '+path+' where',1)[1].split('\n\n',1)[0].splitlines()if line.startswith('| ')]==['| '+v for v in variants]
  aliases='\n/- Definitional compatibility aliases for deterministic export naming only. -/\nnamespace '+namespace+'\nabbrev '+path+' := '+fresh+'\nnamespace '+path+'\n'
  for variant in variants:aliases+='@[match_pattern] abbrev '+variant+' := _root_.'+namespace+'.'+fresh+'.'+variant+'\n'
  aliases+='abbrev read_discriminant := _root_.'+namespace+'.'+fresh+'.read_discriminant\nend '+path+'\nend '+namespace+'\n'
  replay=changed+aliases;assert replay.removesuffix(aliases).replace(fresh,path)==before
  out=HERE/'TypeReplay/Modules'/module/'Types.lean';out.parent.mkdir(parents=True,exist_ok=True);out.write_text(replay)
  funs=REF/module/'Funs.lean'
  rows.append({'original_type_file':str(original.relative_to(ROOT)),'original_type_sha256':sha(original),'replayed_type_file':str(out.relative_to(ROOT)),'replayed_type_sha256':sha(out),'full_qualified_type':qualified,'fresh_export':namespace+'.'+fresh,'compatibility_aliases_definitional':True,'original_Funs_sha256':sha(funs),'Funs_file':str(funs.relative_to(ROOT)),'Funs_modified':False,'exact_inverse_replay_checked':True})
 report={'candidate_only':True,'independent_review':'pending','canonical_Aeneas_library_changed':False,'generated_computational_Funs_modified':False,'scope':'Only deterministic enum type-family export alpha-renaming plus definitional type/constructor aliases; actual Rust metadata and variant order unchanged. No computation/body rewrite.', 'script_sha256':sha(Path(__file__)),'rows':rows}
 (HERE/'TypeReplay/replay.json').write_text(json.dumps(report,indent=2)+'\n');print('Two deterministic type-export replays; generated Funs unchanged')
if __name__=='__main__':main()
