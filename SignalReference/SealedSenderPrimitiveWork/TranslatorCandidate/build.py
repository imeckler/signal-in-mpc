#!/usr/bin/env python3
"""Isolated missing-declaration guard; no computational LLBC edits."""
import difflib,hashlib,json,os,shutil,subprocess,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
LEGACY=ROOT/'SignalReference/ProstEncodingWork/AdvanceWork/TranslatorCandidate'
SOURCE=HERE/'Source/aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 archive=LEGACY/'aeneas-5b9dcf33.tar.gz';assert sha(archive)=='ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453'
 charon=ROOT/'.deps/charon-4ad295c.tar.gz';assert sha(charon)=='6201c2f41fee4e20e2d565db6790aeb14d4f356bfe7632ca3ea8f18f2da2532b'
 original={}
 with tarfile.open(archive) as tar:
  for m in tar.getmembers():
   if m.isfile():original[m.name.split('/',1)[1]]=hashlib.sha256(tar.extractfile(m).read()).hexdigest()
  if not SOURCE.exists():
   (HERE/'Source').mkdir(exist_ok=True);tar.extractall(HERE/'Source',filter='data')
 if not (SOURCE/'charon').exists():
  with tarfile.open(charon) as tar:tar.extractall(HERE/'Source',filter='data')
  (SOURCE/'charon').symlink_to('../charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8')
 name='src/PrePasses.ml';path=SOURCE/name
 with tarfile.open(archive) as tar:before=tar.extractfile('aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3/'+name).read().decode()
 old='''    let trait_decl =
      [%silent_unwrap_opt_span] (Some impl.item_meta.span)
        (TraitDeclId.Map.find_opt impl.impl_trait.id crate.trait_decls)
    in
    if not (match_name impl_pat trait_decl.item_meta.name) then None
    else'''
 new='''    (* An excluded trait has no declaration to match against Default.
       Leave its impl and all references untouched; this pass only rewrites
       recognized Default-array implementations. *)
    match TraitDeclId.Map.find_opt impl.impl_trait.id crate.trait_decls with
    | None -> None
    | Some trait_decl ->
    if not (match_name impl_pat trait_decl.item_meta.name) then None
    else'''
 assert before.count(old)==1;after=before.replace(old,new);path.write_text(after)
 for n,h in original.items():assert sha(SOURCE/n)==(sha(path) if n==name else h),n
 (HERE/'patch.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='upstream/'+name,tofile='candidate/'+name)))
 prefix=LEGACY/'Opam/aeneas-never';env=dict(os.environ)
 env.update(PATH=str(prefix/'bin')+':/Users/izzy/.opam/default/bin:/opt/homebrew/bin:/usr/bin:/bin',OCAMLPATH=str(prefix/'lib'),CAML_LD_LIBRARY_PATH=str(prefix/'lib/stublibs')+':/Users/izzy/.opam/default/lib/stublibs',OCAML_TOPLEVEL_PATH=str(prefix/'lib/toplevel'),OPAM_SWITCH_PREFIX=str(prefix),AENEAS_VERSION='5b9dcf33-array-default-missing-decl-candidate')
 command=[str(prefix/'bin/dune'),'build','--profile','release','main.exe','-j','4']
 with (HERE/'build.log').open('w') as out:r=subprocess.run(command,cwd=SOURCE/'src',env=env,stdout=out,stderr=subprocess.STDOUT)
 report={'candidate_only':True,'accepted_toolchain_modified':False,'source_archive_sha256':sha(archive),'charon_archive_sha256':sha(charon),'original_source_sha256':original,'changed_source_sha256':{name:sha(path)},'patch_sha256':sha(HERE/'patch.diff'),'script_sha256':sha(Path(__file__)),'exit_code':r.returncode,'command':command,'scope':'Retain all excluded trait impls/references; only skip unmatchable declarations in Default-array recognizing prepass. No source/LLBC/generated-body edits; not accepted.'}
 if r.returncode==0:
  built=SOURCE/'src/_build/default/main.exe';binary=HERE/('candidate-'+sha(built)[:16]);shutil.copy2(built,binary)
  report.update(binary_path=str(binary.relative_to(ROOT)),binary_sha256=sha(binary),version=subprocess.check_output([str(binary),'-version'],text=True).strip())
 (HERE/'build-report.json').write_text(json.dumps(report,indent=2)+'\n');print('Build exit',r.returncode,flush=True)
 return r.returncode
if __name__=='__main__':raise SystemExit(main())
