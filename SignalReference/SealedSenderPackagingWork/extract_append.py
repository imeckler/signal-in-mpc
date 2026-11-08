#!/usr/bin/env python3
"""Actual pinned Prost Vec byte-adapter append wrapper, with standard containers external.
This does not accept a full sealed-sender/primitive refinement by extraction.
"""
import hashlib,importlib.util,json,os,subprocess,tarfile,tomllib
from pathlib import Path
HERE=Path(__file__).resolve().parent;REFERENCE=HERE.parent;ROOT=REFERENCE.parent
spec=importlib.util.spec_from_file_location('reference_extract',REFERENCE/'extract.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 pins=json.loads((REFERENCE/'pins.json').read_text());source=ROOT/'.deps/libsignal-v0.106.1';archive=ROOT/'.deps/libsignal-v0.106.1.tar.gz'
 assert sha(archive)==pins['libsignal']['archive_sha256']
 names=['rust/protocol/src/crypto.rs','rust/protocol/src/sealed_sender.rs','Cargo.lock']
 with tarfile.open(archive) as tar:
  archive_files={}
  for name in names:
   matches=[m for m in tar.getmembers() if m.name.endswith('/'+name)];assert len(matches)==1
   content=tar.extractfile(matches[0]).read();assert (source/name).read_bytes()==content
   archive_files[str((source/name).relative_to(ROOT))]=sha(source/name)
 lock=tomllib.loads((source/'Cargo.lock').read_text());dependencies={}
 for name,version in [('prost','0.14.4'),('bytes','1.12.0')]:
  directory=ROOT/'.deps/libsignal-vendor'/(name+'-'+version)
  package=next(p for p in lock['package'] if p['name']==name and p['version']==version)
  checksums=json.loads((directory/'.cargo-checksum.json').read_text());assert checksums['package']==package['checksum']
  for filename,expected in checksums['files'].items():assert sha(directory/filename)==expected
  dependencies[name]={'version':version,'package_sha256':package['checksum'],'files_checked':len(checksums['files'])}
  for filename in (['src/encoding.rs'] if name=='prost' else ['src/buf/buf_mut.rs','src/buf/buf_impl.rs']):archive_files[str((directory/filename).relative_to(ROOT))]=sha(directory/filename)
 rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REFERENCE/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve()
 versions={'charon':subprocess.check_output([str(charon),'version'],text=True).strip(),'aeneas':subprocess.check_output([str(aeneas),'-version'],text=True).strip(),'rustc':subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()}
 assert pins['charon']['commit'] in versions['charon'] and pins['aeneas']['release'] in versions['aeneas'] and versions['rustc']==pins['charon']['rustc_version']
 destination=HERE/'Artifacts/PayloadAppend';destination.mkdir(parents=True,exist_ok=True);llbc=destination/'ss_append.llbc';llbc.unlink(missing_ok=True)
 env=dict(os.environ);env.update(PATH=str(rust/'bin')+os.pathsep+env.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/ss-wrapper-charon-target'),RUSTFLAGS='')
 command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from={crate::encoding::sealed::BytesAdapter for alloc::vec::Vec<u8>}::append_to','--start-from-if-exists=crate::encoding::*::append_to','--include=bytes::buf::buf_impl::*::remaining','--include=bytes::buf::buf_impl::*::chunk','--dest-file='+str(llbc),'--','--package','prost@0.14.4','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 subprocess.run([str(rust/'bin/cargo'),'clean','--package','prost@0.14.4','--target','aarch64-apple-darwin'],cwd=source,env=env,check=True,stdout=subprocess.DEVNULL)
 with (destination/'charon.log').open('w') as out:r=subprocess.run(command,cwd=source,env=env,stdout=out,stderr=subprocess.STDOUT)
 report={'verified_dependencies':dependencies,'candidate_only':True,'accepted_reference':False,'source_patches':[],'archive_sha256':sha(archive),'source_sha256':archive_files,'versions':versions,'opaque_primitives':[],'primitive_implementation_refinement_established':False,'charon_command':[s.replace(str(ROOT),'$WORKSPACE') for s in command],'charon_exit_code':r.returncode,'script_sha256':sha(Path(__file__))}
 if llbc.exists():report.update(base.inventory(llbc))
 target=destination/'inventory.json';target.write_text(json.dumps(report,indent=2)+'\n')
 if r.returncode or not llbc.exists() or report['has_errors'] or report['counts']['ordered_decls']==0:
  print('Actual append extraction blocked',flush=True);return 1
 generated=HERE/'Generated/PayloadAppend';generated.mkdir(parents=True,exist_ok=True)
 command=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REFERENCE),'-subdir','/SealedSenderPackagingWork/Generated/PayloadAppend','-split-files','-namespace','SealedSenderAppend','-warnings-as-errors','-no-progress-bar']
 with (destination/'aeneas.log').open('w') as out:r=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 report.update(aeneas_exit_code=r.returncode,aeneas_command=[s.replace(str(ROOT),'$WORKSPACE') for s in command],generated_files={str(p.relative_to(REFERENCE)):sha(p) for p in generated.glob('*.lean')})
 target.write_text(json.dumps(report,indent=2)+'\n');print('Actual pinned SS wrapper Aeneas exit',r.returncode,flush=True)
 return r.returncode
if __name__=='__main__':raise SystemExit(main())
