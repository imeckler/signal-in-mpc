#!/usr/bin/env python3
"""Actual unchanged pinned SSv1 symmetric wrapper; explicitly opaque primitives.
This does not accept a full sealed-sender/primitive refinement by extraction.
"""
import argparse,hashlib,importlib.util,json,os,subprocess,tarfile,tomllib
from pathlib import Path
HERE=Path(__file__).resolve().parent;REFERENCE=HERE.parent;ROOT=REFERENCE.parent
spec=importlib.util.spec_from_file_location('reference_extract',REFERENCE/'extract.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 parser=argparse.ArgumentParser();parser.add_argument("profile",choices=["ctr","ctr_scoped","hmac","hmac_scoped","ctr_mono","hmac_mono","hmac_mono_barrier","hmac_specialized","ctr_specialized"]);args=parser.parse_args()
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
 destination=HERE/'Artifacts'/args.profile;destination.mkdir(parents=True,exist_ok=True);llbc=destination/'ss_wrapper.llbc';llbc.unlink(missing_ok=True)
 env=dict(os.environ);env.update(PATH=str(rust/'bin')+os.pathsep+env.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/ss-primitive-charon-target'),RUSTFLAGS='--cfg aes_backend="soft" --cfg sha2_256_backend="soft" --cfg sha2_backend_soft="compact"')
 command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate::crypto::'+('aes_256_ctr_encrypt' if args.profile.startswith('ctr') else 'hmac_sha256'),*[f'--include={name}' for name in (['ctr','cipher','aes','hybrid_array','inout','crypto_common'] if args.profile.startswith('ctr') else ['hmac','digest','sha2','block_buffer','hybrid_array','crypto_common'])],*(['--exclude=hybrid_array::traits::ArraySize'] if args.profile.endswith('_scoped') else []),*(['--monomorphize','--extract-opaque-bodies'] if '_mono' in args.profile else []),*(['--monomorphize'] if args.profile.endswith('_specialized') else []),*(['--opaque=zeroize::barrier::optimization_barrier'] if args.profile.endswith('_barrier') else []),'--dest-file='+str(llbc),'--','--package','libsignal-protocol','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 with (destination/'charon.log').open('w') as out:r=subprocess.run(command,cwd=source,env=env,stdout=out,stderr=subprocess.STDOUT)
 lock=tomllib.loads((source/'Cargo.lock').read_text());dependencies={}
 for name in (['ctr','cipher','aes','hybrid-array','inout','crypto-common'] if args.profile.startswith('ctr') else ['hmac','digest','sha2','block-buffer','hybrid-array','crypto-common']):
  version={'ctr':'0.10.1','cipher':'0.5.2','aes':'0.9.1','hybrid-array':'0.4.13','inout':'0.2.2','crypto-common':'0.2.2','hmac':'0.13.0','digest':'0.11.3','sha2':'0.11.0','block-buffer':'0.12.1'}[name]
  directory=ROOT/'.deps/libsignal-vendor'/(name+'-'+version)
  package=next(p for p in lock['package'] if p['name']==name and p['version']==version)
  checksums=json.loads((directory/'.cargo-checksum.json').read_text());assert checksums['package']==package['checksum']
  for filename,expected in checksums['files'].items():assert sha(directory/filename)==expected
  dependencies[name]={'version':version,'package_sha256':package['checksum'],'files_checked':len(checksums['files'])}
 report={'dependencies':dependencies,'candidate_only' :True,'accepted_reference':False,'source_patches':[],'archive_sha256':sha(archive),'source_sha256':archive_files,'versions':versions,'opaque_primitives':(['zeroize::barrier::optimization_barrier (read-only inline-assembly compiler barrier; NOT a crypto primitive agreement)'] if args.profile.endswith('_barrier') else []),'profile':args.profile,'rustflags':env['RUSTFLAGS'],'primitive_implementation_refinement_established':False,'charon_command':[s.replace(str(ROOT),'$WORKSPACE') for s in command],'charon_exit_code':r.returncode,'script_sha256':sha(Path(__file__))}
 if llbc.exists():report.update(base.inventory(llbc))
 target=destination/'inventory.json';target.write_text(json.dumps(report,indent=2)+'\n')
 if r.returncode or not llbc.exists() or report['has_errors']:
  print('Actual primitive extraction blocked; see',target,flush=True);return 1
 generated=HERE/'Generated'/args.profile;generated.mkdir(parents=True,exist_ok=True)
 command=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REFERENCE),'-subdir','/SealedSenderPrimitiveWork/Generated/'+args.profile,'-split-files','-namespace','SealedSenderPrimitive','-warnings-as-errors','-no-progress-bar']
 with (destination/'aeneas.log').open('w') as out:r=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 report.update(aeneas_exit_code=r.returncode,aeneas_command=[s.replace(str(ROOT),'$WORKSPACE') for s in command],generated_files={str(p.relative_to(REFERENCE)):sha(p) for p in generated.glob('*.lean')})
 target.write_text(json.dumps(report,indent=2)+'\n');print('Actual pinned SS wrapper Aeneas exit',r.returncode,flush=True)
 return r.returncode
if __name__=='__main__':raise SystemExit(main())
