#!/usr/bin/env python3
"""Actual unchanged pinned SSv1 USMC constructor/packaging extraction.
This does not accept a full sealed-sender/primitive refinement by extraction.
"""
import argparse,hashlib,importlib.util,json,os,subprocess,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;REFERENCE=HERE.parent;ROOT=REFERENCE.parent
spec=importlib.util.spec_from_file_location('reference_extract',REFERENCE/'extract.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 parser=argparse.ArgumentParser();parser.add_argument("profile",choices=["ContentConstructor","WireFields","WireFieldsFull","ContentConstructorMono"],nargs="?",default="ContentConstructor");args=parser.parse_args()
 pins=json.loads((REFERENCE/'pins.json').read_text());source=ROOT/'.deps/libsignal-v0.106.1';archive=ROOT/'.deps/libsignal-v0.106.1.tar.gz'
 assert sha(archive)==pins['libsignal']['archive_sha256']
 names=['rust/protocol/src/crypto.rs','rust/protocol/src/sealed_sender.rs','rust/protocol/src/proto/sealed_sender.proto','Cargo.lock']
 with tarfile.open(archive) as tar:
  archive_files={}
  for name in names:
   matches=[m for m in tar.getmembers() if m.name.endswith('/'+name)];assert len(matches)==1
   content=tar.extractfile(matches[0]).read();assert (source/name).read_bytes()==content
   archive_files[str((source/name).relative_to(ROOT))]=sha(source/name)
 rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REFERENCE/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve()
 versions={'charon':subprocess.check_output([str(charon),'version'],text=True).strip(),'aeneas':subprocess.check_output([str(aeneas),'-version'],text=True).strip(),'rustc':subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()}
 assert pins['charon']['commit'] in versions['charon'] and pins['aeneas']['release'] in versions['aeneas'] and versions['rustc']==pins['charon']['rustc_version']
 destination=HERE/'Artifacts'/args.profile;destination.mkdir(parents=True,exist_ok=True);llbc=destination/'ss_content.llbc';llbc.unlink(missing_ok=True)
 env=dict(os.environ);env.update(PATH=str(rust/'bin')+os.pathsep+env.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/ss-wrapper-charon-target'),RUSTFLAGS='')
 command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings',*(['--start-from=crate::sealed_sender::UnidentifiedSenderMessageContent::new','--start-from-if-exists=crate::sealed_sender::*::new','--include=prost','--include=bytes'] if args.profile.startswith('ContentConstructor') else ['--start-from={prost::message::Message for crate::proto::sealed_sender::unidentified_sender_message::Message}::encode_raw','--include=prost::encoding::int32::encode','--include=prost::encoding::bytes::encode','--include=prost::encoding::varint::encode_varint','--include=prost::encoding::encode_key','--include=prost::encoding::*::len','--include=prost::encoding::*::append_to','--include=bytes::buf::buf_mut::BufMut::put_u8']),*(['--include=alloc::vec::*::default','--include=alloc::vec::*::as_slice','--include=bytes::buf::buf_impl::*::remaining','--include=bytes::buf::buf_impl::*::chunk','--include=bytes::buf::buf_impl::*::advance','--include=bytes::buf::buf_mut::BufMut::put','--include=bytes::buf::buf_mut::BufMut::put_slice','--include=core::ops::range::*::contains','--include=core::ops::range::*::new','--include=core::ops::range::RangeInclusive','--include=core::ops::range::Bound','--include=core::ops::range::*::start_bound','--include=core::ops::range::*::end_bound','--include=prost::encoding::MIN_TAG','--include=prost::encoding::MAX_TAG'] if args.profile=='WireFieldsFull' else []),*(['--monomorphize'] if args.profile=='ContentConstructorMono' else []),'--dest-file='+str(llbc),'--','--package','libsignal-protocol','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 with (destination/'charon.log').open('w') as out:r=subprocess.run(command,cwd=source,env=env,stdout=out,stderr=subprocess.STDOUT)
 report={'candidate_only':True,'accepted_reference':False,'source_patches':[],'archive_sha256':sha(archive),'source_sha256':archive_files,'versions':versions,'opaque_primitives':[],'primitive_implementation_refinement_established':False,'charon_command':[s.replace(str(ROOT),'$WORKSPACE') for s in command],'charon_exit_code':r.returncode,'script_sha256':sha(Path(__file__))}
 if llbc.exists():report.update(base.inventory(llbc))
 target=destination/'inventory.json';target.write_text(json.dumps(report,indent=2)+'\n')
 if r.returncode or not llbc.exists() or report['has_errors'] or report['counts']['ordered_decls']==0:
  print('Actual packaging extraction blocked; see',target,flush=True);return 1
 generated=HERE/'Generated'/args.profile;generated.mkdir(parents=True,exist_ok=True)
 command=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REFERENCE),'-subdir','/SealedSenderPackagingWork/Generated/'+args.profile,'-split-files','-namespace','SealedSenderPackaging','-warnings-as-errors','-no-progress-bar']
 with (destination/'aeneas.log').open('w') as out:r=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
 report.update(aeneas_exit_code=r.returncode,aeneas_command=[s.replace(str(ROOT),'$WORKSPACE') for s in command],generated_files={str(p.relative_to(REFERENCE)):sha(p) for p in generated.glob('*.lean')})
 target.write_text(json.dumps(report,indent=2)+'\n');print('Actual pinned SS wrapper Aeneas exit',r.returncode,flush=True)
 return r.returncode
if __name__=='__main__':raise SystemExit(main())
