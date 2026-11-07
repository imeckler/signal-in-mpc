#!/usr/bin/env python3
"""Quarantined pinned-source baseline / one-pass-order extension builds.
The legacy-named dependency prefix supplies OCaml libraries only: no Never
translator binary or source patch is reused.
"""
import difflib,hashlib,json,os,shutil,subprocess,sys,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];REFERENCE=ROOT/'SignalReference'
LEGACY=REFERENCE/'ProstEncodingWork/AdvanceWork/TranslatorCandidate'
SOURCE=HERE/'Source/aeneas-5b9dcf33dccdb1560ea7203ac57ea202476b6ed3'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 phase=sys.argv[1];assert phase in ('baseline','candidate')
 archive=LEGACY/'aeneas-5b9dcf33.tar.gz';assert digest(archive)=='ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453'
 charon_archive=ROOT/'.deps/charon-4ad295c.tar.gz';assert digest(charon_archive)=='6201c2f41fee4e20e2d565db6790aeb14d4f356bfe7632ca3ea8f18f2da2532b'
 if not SOURCE.exists():
  (HERE/'Upstream').rename(HERE/'Source')
  with tarfile.open(charon_archive) as t:t.extractall(HERE/'Source',filter='data')
  (SOURCE/'charon').symlink_to('../charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8')
 source_hashes={}
 with tarfile.open(archive) as t:
  for m in t.getmembers():
   if m.isfile():
    name=m.name.split('/',1)[1];source_hashes[name]=hashlib.sha256(t.extractfile(m).read()).hexdigest()
 patchfile='src/PrePasses.ml';path=SOURCE/patchfile
 old='''      ("remove_unreachable", remove_unreachable);
      ("update_loop", update_loops);'''
 new='''      ("remove_unreachable", remove_unreachable);
      (* Candidate: expose existing branch continuations before normalizing
         early returns in loops. Reuse the existing semantics-preserving pass. *)
      ("expose_loop_continuations", remove_useless_joins);
      ("update_loop", update_loops);'''
 if phase=='candidate':
  before=path.read_text();assert digest(path)==source_hashes[patchfile] and before.count(old)==1
  after=before.replace(old,new);path.write_text(after)
  (HERE/'continuation-pass.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='upstream/src/PrePasses.ml',tofile='candidate/src/PrePasses.ml')))
 for name,sha in source_hashes.items():
  if name==patchfile and phase=='candidate':continue
  assert digest(SOURCE/name)==sha,name
 prefix=LEGACY/'Opam/aeneas-never'
 env=os.environ.copy();env.update({'PATH':str(prefix/'bin')+':/Users/izzy/.opam/default/bin:/opt/homebrew/bin:/usr/bin:/bin',
  'OCAMLPATH':str(prefix/'lib'),'CAML_LD_LIBRARY_PATH':str(prefix/'lib/stublibs')+':/Users/izzy/.opam/default/lib/stublibs',
  'OCAML_TOPLEVEL_PATH':str(prefix/'lib/toplevel'),'OPAM_SWITCH_PREFIX':str(prefix),
  'AENEAS_VERSION':'5b9dcf33dccdb1560ea7203ac57ea202476b6ed3-loop-'+phase})
 command=[str(prefix/'bin/dune'),'build','--profile','release','main.exe','-j','4']
 log=HERE/(phase+'-build.log')
 with log.open('w') as out:r=subprocess.run(command,cwd=SOURCE/'src',env=env,stdout=out,stderr=subprocess.STDOUT)
 report={'candidate_only':True,'accepted_toolchain_modified':False,'phase':phase,'source_archive_sha256':digest(archive),'charon_archive_sha256':digest(charon_archive),
  'original_source_sha256':source_hashes,'source_delta':[patchfile] if phase=='candidate' else [],'never_candidate_source_or_binary_used':False,
  'read_only_ocaml_dependency_prefix':str(prefix),'dependency_version_inventory_sha256':digest(LEGACY/'installed-packages.txt'),
  'command':command,'environment_overrides':{k:env[k] for k in ['PATH','OCAMLPATH','CAML_LD_LIBRARY_PATH','OCAML_TOPLEVEL_PATH','OPAM_SWITCH_PREFIX','AENEAS_VERSION']},
  'script_sha256':digest(Path(__file__)),'exit_code':r.returncode,'log_sha256':digest(log)}
 if r.returncode==0:
  (HERE/'Bin').mkdir(exist_ok=True);binary=HERE/'Bin'/phase;shutil.copy2(SOURCE/'src/_build/default/main.exe',binary)
  report['binary_sha256']=digest(binary);report['version']=subprocess.check_output([str(binary),'-version'],text=True).strip()
 if phase=='candidate':report.update({'diff_sha256':digest(HERE/'continuation-pass.diff'),'changed_source_sha256':digest(path)})
 (HERE/(phase+'-build-report.json')).write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items() if k in ['phase','exit_code','binary_sha256','version']}),flush=True)
 sys.exit(r.returncode)
if __name__=='__main__':main()
