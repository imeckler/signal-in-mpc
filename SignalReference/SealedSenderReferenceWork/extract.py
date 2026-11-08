#!/usr/bin/env python3
"""Actual unchanged pinned SSv1 symmetric wrapper; explicitly opaque primitives.
This does not accept a full sealed-sender/primitive refinement by extraction.
"""
import hashlib,importlib.util,json,os,subprocess,tarfile
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
 rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REFERENCE/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve()
 versions={'charon':subprocess.check_output([str(charon),'version'],text=True).strip(),'aeneas':subprocess.check_output([str(aeneas),'-version'],text=True).strip(),'rustc':subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()}
 assert pins['charon']['commit'] in versions['charon'] and pins['aeneas']['release'] in versions['aeneas'] and versions['rustc']==pins['charon']['rustc_version']
 destination=HERE/'Artifacts/EncryptWrapper';destination.mkdir(parents=True,exist_ok=True);llbc=destination/'ss_wrapper.llbc'
 env=dict(os.environ);env.update(PATH=str(rust/'bin')+os.pathsep+env.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/ss-wrapper-charon-target'),RUSTFLAGS='')
 command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate::crypto::aes256_ctr_hmacsha256_encrypt','--opaque=crate::crypto::aes_256_ctr_encrypt','--opaque=crate::crypto::hmac_sha256','--dest-file='+str(llbc),'--','--package','libsignal-protocol','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 with (destination/'charon.log').open('w') as out:r=subprocess.run(command,cwd=source,env=env,stdout=out,stderr=subprocess.STDOUT)
 report={'candidate_only':True,'accepted_reference':False,'source_patches':[],'archive_sha256':sha(archive),'source_sha256':archive_files,'versions':versions,'opaque_primitives':['actual crypto::aes_256_ctr_encrypt','actual crypto::hmac_sha256'],'primitive_implementation_refinement_established':False,'charon_command':[s.replace(str(ROOT),'$WORKSPACE') for s in command],'charon_exit_code':r.returncode,'script_sha256':sha(Path(__file__))}
 if llbc.exists():report.update(base.inventory(llbc))
 target=destination/'inventory.json';target.write_text(json.dumps(report,indent=2)+'\n')
 if r.returncode or not llbc.exists() or report['has_errors']:raise RuntimeError('Actual wrapper extraction failed; inspect charon.log')
 generated=HERE/'Generated/EncryptWrapper';generated.mkdir(parents=True,exist_ok=True)
 command=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REFERENCE),'-subdir','/SealedSenderReferenceWork/Generated/EncryptWrapper','-split-files','-namespace','SealedSenderReference','-warnings-as-errors','-no-progress-bar']
 with (destination/'aeneas.log').open('w') as out:r=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 report.update(aeneas_exit_code=r.returncode,aeneas_command=[s.replace(str(ROOT),'$WORKSPACE') for s in command],generated_files={str(p.relative_to(REFERENCE)):sha(p) for p in generated.glob('*.lean')})
 target.write_text(json.dumps(report,indent=2)+'\n');print('Actual pinned SS wrapper Aeneas exit',r.returncode,flush=True)
 return r.returncode
if __name__=='__main__':raise SystemExit(main())
