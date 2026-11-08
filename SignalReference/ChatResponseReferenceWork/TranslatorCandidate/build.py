#!/usr/bin/env python3
"""Isolated naming-only repair; no LLBC, pure expression, or model alteration."""
from pathlib import Path
import difflib,hashlib,json,os,shutil,subprocess,tarfile
H=Path(__file__).resolve().parent;ROOT=H.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
legacy=ROOT/'SignalReference/ProstEncodingWork/AdvanceWork/TranslatorCandidate'
archive=legacy/'aeneas-5b9dcf33.tar.gz';charon=ROOT/'.deps/charon-4ad295c.tar.gz'
assert sha(archive)=='ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453'
assert sha(charon)=='6201c2f41fee4e20e2d565db6790aeb14d4f356bfe7632ca3ea8f18f2da2532b'
S=H/'Source/aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3';original={}
with tarfile.open(archive) as t:
 for m in t.getmembers():
  if m.isfile():original[m.name.split('/',1)[1]]=hashlib.sha256(t.extractfile(m).read()).hexdigest()
 if not S.exists():(H/'Source').mkdir(exist_ok=True);t.extractall(H/'Source',filter='data')
if not (S/'charon').exists():
 with tarfile.open(charon) as t:t.extractall(H/'Source',filter='data')
 (S/'charon').symlink_to('../charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8')
name='src/extract/ExtractBase.ml';p=S/name
with tarfile.open(archive) as t:before=t.extractfile('aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3/'+name).read().decode()
a='''  let clause = clause ^ "Inst" in
  match backend () with'''
b='''  let clause = clause ^ "Inst" in
  (* Naming only: equal parent trait names can denote different bounds.
     Preserve both slots and disambiguate their printed record field names. *)
  let same_name (other : trait_param) =
    let n =
      ctx_compute_trait_clause_name ctx trait_decl.item_meta.name
        trait_decl.llbc_generics trait_decl.llbc_parent_clauses other.clause_id
    in
    let n =
      if !Config.record_fields_short_names then n
      else ctx_compute_trait_decl_name ctx trait_decl ^ "_" ^ n
    in
    n ^ "Inst" = clause
  in
  let clause =
    if List.length (List.filter same_name trait_decl.parent_clauses) > 1 then
      clause ^ "_" ^ TraitClauseId.to_string parent_clause_id
    else clause
  in
  match backend () with'''
start=before.index('let ctx_compute_trait_parent_clause_name');stop=before.index('let ctx_compute_trait_type_name',start)
section=before[start:stop];assert section.count(a)==1
section=section.replace('''    (trait_decl : trait_decl) (clause : trait_param) : string =
  (* We derive''','''    (trait_decl : trait_decl) (clause : trait_param) : string =
  let parent_clause_id = clause.clause_id in
  (* We derive''',1).replace(a,b)
after=before[:start]+section+before[stop:]
a='''              let cl = Collections.List.last name in
              name_from_type_ident (TypesUtils.as_ident cl))'''
b='''              match
                List.find_opt
                  (function T.PeIdent _ -> true | _ -> false)
                  (List.rev name)
              with
              | Some cl -> name_from_type_ident (TypesUtils.as_ident cl)
              | None -> "x")'''
assert after.count(a)==1;after=after.replace(a,b);p.write_text(after)
for n,digest in original.items():
 if n!=name:assert sha(S/n)==digest,n
(H/'naming.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='upstream/'+name,tofile='candidate/'+name)))
prefix=legacy/'Opam/aeneas-never';env=os.environ.copy();env.update(PATH=str(prefix/'bin')+':/Users/izzy/.opam/default/bin:/opt/homebrew/bin:/usr/bin:/bin',OCAMLPATH=str(prefix/'lib'),CAML_LD_LIBRARY_PATH=str(prefix/'lib/stublibs')+':/Users/izzy/.opam/default/lib/stublibs',OCAML_TOPLEVEL_PATH=str(prefix/'lib/toplevel'),OPAM_SWITCH_PREFIX=str(prefix),AENEAS_VERSION='5b9dcf33dccdb1560ea7203ac57ea202476b6ed3-chat-names')
command=[str(prefix/'bin/dune'),'build','--profile','release','main.exe','-j','4']
with (H/'build.log').open('w') as f:r=subprocess.run(command,cwd=S/'src',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=240)
report={'candidate_only':True,'scope':'Printed identifier/record field names only; no computational body/model/LLBC changes','source_archive_sha256':sha(archive),'charon_archive_sha256':sha(charon),'source_delta':[name],'original_file_sha256':original[name],'modified_file_sha256':sha(p),'diff_sha256':sha(H/'naming.diff'),'exit_code':r.returncode,'script_sha256':sha(Path(__file__)),'command':command}
if r.returncode==0:
 (H/'Bin').mkdir(exist_ok=True);binary=H/'Bin/candidate';shutil.copy2(S/'src/_build/default/main.exe',binary);report.update(binary_sha256=sha(binary),version=subprocess.check_output([str(binary),'-version'],text=True).strip())
(H/'build-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report));raise SystemExit(r.returncode)
