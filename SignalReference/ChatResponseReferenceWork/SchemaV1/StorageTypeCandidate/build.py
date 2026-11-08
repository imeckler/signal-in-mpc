#!/usr/bin/env python3
from pathlib import Path
import os,subprocess,shutil,json,hashlib,difflib,time
H=Path(__file__).resolve().parent;ROOT=H.parents[3];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();base=ROOT/'SignalReference/ProtoParseWork/MessageReferenceWork/FnItemCandidate';receipt=json.loads((base/'build-report.json').read_text());original=base/'Source/aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3';source=H/'Source/aeneas';source.parent.mkdir(exist_ok=True)
for name,digest in {**receipt['original_source_sha256'],**receipt['changed_source_sha256']}.items():assert sha(original/name)==digest,name
if not source.exists():shutil.copytree(original,source,symlinks=True,ignore=shutil.ignore_patterns('_build','.git'))
(source/'charon').unlink(missing_ok=True);(source/'charon').symlink_to((base/'Source/charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8').resolve())
name='src/interp/InterpPaths.ml';before=(original/name).read_text();after=before.replace('if updated_ty <> v.ty then (','if updated_ty <> v_ty then (');assert after!=before;(source/name).write_text(after)
for name0,digest in {**receipt['original_source_sha256'],**receipt['changed_source_sha256']}.items():
 if name0!=name:assert sha(source/name0)==digest,name0
(H/'patch.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='inherited/'+name,tofile='candidate/'+name)))
prefix=ROOT/'SignalReference/ProstEncodingWork/AdvanceWork/TranslatorCandidate/Opam/aeneas-never';env=os.environ.copy();env.update(PATH=str(prefix/'bin')+':/Users/izzy/.opam/default/bin:/opt/homebrew/bin:/usr/bin:/bin',OCAMLPATH=str(prefix/'lib'),CAML_LD_LIBRARY_PATH=str(prefix/'lib/stublibs')+':/Users/izzy/.opam/default/lib/stublibs',OCAML_TOPLEVEL_PATH=str(prefix/'lib/toplevel'),OPAM_SWITCH_PREFIX=str(prefix),AENEAS_VERSION='5b9dcf33-storage-erased-type-candidate')
command=[str(prefix/'bin/dune'),'build','--profile','release','main.exe','-j','4']
with (H/'build.log').open('w') as f:
 p=subprocess.Popen(command,cwd=source/'src',env=env,stdout=f,stderr=subprocess.STDOUT);process={'parent_pid':os.getpid(),'parent_pgid':os.getpgrp(),'child_pid':p.pid,'child_pgid':os.getpgid(p.pid),'command':command,'status':'running'};assert process['parent_pgid']==process['child_pgid'];(H/'process.json').write_text(json.dumps(process,indent=2)+'\n');print(json.dumps(process),flush=True)
 try:code=p.wait()
 except KeyboardInterrupt:code=p.wait(timeout=20)
 process.update(status='terminal',exit_code=code);(H/'process.json').write_text(json.dumps(process,indent=2)+'\n')
report={'candidate_only':True,'scope':'Compare the two already-computed erased storage types, as the existing comment intends; preserve every non-region type check, computation and argument check.','inherited_receipt_sha256':sha(base/'build-report.json'),'inherited_source_files':len(receipt['original_source_sha256']),'source_file':name,'inherited_source_sha256':sha(original/name),'candidate_source_sha256':sha(source/name),'patch_sha256':sha(H/'patch.diff'),'script_sha256':sha(Path(__file__)),'exit_code':code,'command':command}
if code==0:
 (H/'Bin').mkdir(exist_ok=True);shutil.copy2(source/'src/_build/default/main.exe',H/'Bin/candidate');report['binary_sha256']=sha(H/'Bin/candidate')
(H/'build-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report));raise SystemExit(code)
