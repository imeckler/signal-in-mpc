#!/usr/bin/env python3
"""Quarantined total literal zero-argument function-item lifting experiment."""
import difflib,hashlib,json,os,shutil,subprocess,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];LEGACY=ROOT/'SignalReference/ProstEncodingWork/AdvanceWork/TranslatorCandidate'
SOURCE=HERE/'Source/aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 archive=LEGACY/'aeneas-5b9dcf33.tar.gz';assert sha(archive)=='ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453'
 charon=ROOT/'.deps/charon-4ad295c.tar.gz';assert sha(charon)=='6201c2f41fee4e20e2d565db6790aeb14d4f356bfe7632ca3ea8f18f2da2532b'
 original={}
 with tarfile.open(archive) as tar:
  for member in tar.getmembers():
   if member.isfile():original[member.name.split('/',1)[1]]=hashlib.sha256(tar.extractfile(member).read()).hexdigest()
  if not SOURCE.exists():
   (HERE/'Source').mkdir(exist_ok=True);tar.extractall(HERE/'Source',filter='data')
 if not (SOURCE/'charon').exists():
  with tarfile.open(charon) as tar:tar.extractall(HERE/'Source',filter='data')
  (SOURCE/'charon').symlink_to('../charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8')
 changed={};diff=''
 for name in ['src/symbolic/SymbolicToPureTypes.ml','src/symbolic/SymbolicToPureExpressions.ml','src/pure/PureMicroPassesGeneral.ml']:
  path=SOURCE/name
  with tarfile.open(archive) as tar:before=tar.extractfile('aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3/'+name).read().decode()
  assert sha(path)==original[name] or (HERE/'patch.diff').exists()
  if name.endswith('Types.ml'):
   old='''          [%cassert_opt_span] span sg.fwd_info.effect_info.can_fail
            "Unimplemented";'''
   new='''          (* Candidate: a total, zero-input literal function item can be
             represented by its pure result lifted into Result.ok. Reject all
             other previously unsupported pure function-item shapes. *)
          [%cassert_opt_span] span
            (sg.fwd_info.effect_info.can_fail ||
             (sg.inputs = [] && not sg.fwd_info.effect_info.can_diverge &&
              RegionGroupId.Map.is_empty sg.back_effect_info &&
              (match sg.output with TLiteral _ -> true | _ -> false)))
            "Unsupported pure function item: requires total zero-input literal";'''
   assert before.count(old)==1;after=before.replace(old,new)
   old='''          ty_substitute subst sigs.ty
      | T.TraitMethod _'''
   new='''          let ty = ty_substitute subst sigs.ty in
          if sg.fwd_info.effect_info.can_fail then ty else mk_result_ty ty
      | T.TraitMethod _'''
   assert after.count(old)==1;after=after.replace(old,new)
  elif name.endswith('Expressions.ml'):
   old='''        let ty =
          match kind with
          | T.FunId (FBuiltin _) -> [%craise] ctx.span "Unimplemented"'''
   new='''        let ty, needs_lift =
          match kind with
          | T.FunId (FBuiltin _) -> [%craise] ctx.span "Unimplemented"'''
   assert before.count(old)==1;after=before.replace(old,new)
   old='''              [%cassert] ctx.span sg.sg.fwd_info.effect_info.can_fail
                "Unimplemented";'''
   new='''              [%cassert] ctx.span
                (sg.sg.fwd_info.effect_info.can_fail ||
                 (sg.sg.inputs = [] && not sg.sg.fwd_info.effect_info.can_diverge &&
                  RegionGroupId.Map.is_empty sg.sg.back_effect_info &&
                  (match sg.sg.output with TLiteral _ -> true | _ -> false)))
                "Unsupported pure function item: requires total zero-input literal";'''
   assert after.count(old)==1;after=after.replace(old,new)
   old='''              ty_substitute subst sg.ty
          | T.TraitMethod _ -> [%craise] ctx.span "Unimplemented"
        in
        ({ e = qualif; ty }, false)'''
   new='''              (ty_substitute subst sg.ty, not sg.sg.fwd_info.effect_info.can_fail)
          | T.TraitMethod _ -> [%craise] ctx.span "Unimplemented"
        in
        let value = { e = qualif; ty } in
        ((if needs_lift then mk_result_ok_texpr ctx.span value else value), false)'''
   assert after.count(old)==1;after=after.replace(old,new)
  else:
   old='''            x ) ->
          [%ldebug "Case: result"];'''
   new='''            x ) when monadic ->
          [%ldebug "Case: result"];'''
   assert before.count(old)==1;after=before.replace(old,new)
  if name.endswith('Types.ml'):
   old='    | TFnDef _ | TFnPtr _ ->\n        [%craise_opt_span] span "Arrow types are not supported yet"'
   replacements=['    | TFnDef _ ->\n        (* Lifetime-free function items are zero-sized and carry no borrowed\n           environment. Reuse the existing analysis, which rejects regions. *)\n        ignore (TypesAnalysis.analyze_ty span type_infos ty);\n        save_count outer_regions\n    | TFnPtr _ ->\n        [%craise_opt_span] span "Arrow types are not supported yet"','    | TFnDef _ ->\n        ignore (TypesAnalysis.analyze_ty span type_infos ty);\n        stop outer_regions ty\n    | TFnPtr _ ->\n        [%craise_opt_span] span "Arrow types are not supported yet"']
   assert after.count(old)==2
   for replacement in replacements:after=after.replace(old,replacement,1)
  path.write_text(after);changed[name]=sha(path)
  diff+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='upstream/'+name,tofile='candidate/'+name))
 for name,h in original.items():assert sha(SOURCE/name)==changed.get(name,h),name
 (HERE/'patch.diff').write_text(diff)
 prefix=LEGACY/'Opam/aeneas-never'
 env=os.environ.copy();env.update({'PATH':str(prefix/'bin')+':/Users/izzy/.opam/default/bin:/opt/homebrew/bin:/usr/bin:/bin','OCAMLPATH':str(prefix/'lib'),'CAML_LD_LIBRARY_PATH':str(prefix/'lib/stublibs')+':/Users/izzy/.opam/default/lib/stublibs','OCAML_TOPLEVEL_PATH':str(prefix/'lib/toplevel'),'OPAM_SWITCH_PREFIX':str(prefix),'AENEAS_VERSION':'5b9dcf33-pure-zero-literal-fnitem-candidate'})
 command=[str(prefix/'bin/dune'),'build','--profile','release','main.exe','-j','4']
 with (HERE/'build.log').open('w') as out:r=subprocess.run(command,cwd=SOURCE/'src',env=env,stdout=out,stderr=subprocess.STDOUT)
 report={'candidate_only':True,'accepted_toolchain_modified':False,'source_archive_sha256':sha(archive),'charon_archive_sha256':sha(charon),'original_source_sha256':original,'changed_source_sha256':changed,'patch_sha256':sha(HERE/'patch.diff'),'script_sha256':sha(Path(__file__)),'exit_code':r.returncode,'build_log_sha256':sha(HERE/'build.log'),'command':command,'read_only_ocaml_prefix':str(prefix),'never_patch_or_binary_used':False,'scope':'Result lift for total zero-input literal pure function items only; existing function-item behavior otherwise unchanged; not accepted.'}
 if r.returncode==0:
  built=SOURCE/'src/_build/default/main.exe';binary=HERE/('candidate-'+sha(built)[:16])
  if not binary.exists():shutil.copy2(built,binary)
  assert sha(binary)==sha(built)
  report['binary_path']=str(binary.relative_to(ROOT));report['binary_sha256']=sha(binary);report['version']=subprocess.check_output([str(binary),'-version'],text=True).strip()
 (HERE/'build-report.json').write_text(json.dumps(report,indent=2)+'\n');print('Build exit',r.returncode,flush=True)
 raise SystemExit(r.returncode)
if __name__=='__main__':main()
