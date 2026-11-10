#!/usr/bin/env python3
"""Pinned actual ctr0.10.1 flavor functions; no Rust/model/body replacements."""
import argparse,hashlib,importlib.util,json,os,pathlib,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent;REFERENCE=HERE.parent;ROOT=REFERENCE.parent
spec=importlib.util.spec_from_file_location('reference_extract',REFERENCE/'extract.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()

def main():
 parser=argparse.ArgumentParser();parser.add_argument('profile',choices=['remaining','current_block','next_block','from_nonce']);parser.add_argument('--candidate');parser.add_argument('--opaque-array',action='store_true');args=parser.parse_args();pins=json.loads((REFERENCE/'pins.json').read_text());source=ROOT/'.deps/libsignal-v0.106.1';vendor=ROOT/'.deps/libsignal-vendor/ctr-0.10.1'
 lock=tomllib.loads((source/'Cargo.lock').read_text());package=next(p for p in lock['package']if p['name']=='ctr'and p['version']=='0.10.1');checks=json.loads((vendor/'.cargo-checksum.json').read_text());assert package['checksum']==checks['package']
 files={str((source/'Cargo.lock').relative_to(ROOT)):sha(source/'Cargo.lock')}
 for name,want in checks['files'].items():assert sha(vendor/name)==want;files[str((vendor/name).relative_to(ROOT))]=want
 for path in ['Cargo.toml','rust/protocol/Cargo.toml','rust/protocol/src/crypto.rs']:files[str((source/path).relative_to(ROOT))]=sha(source/path)
 caller=(source/'rust/protocol/src/crypto.rs').read_text();assert 'ctr::Ctr32BE::<Aes256>::new(&key.into(), &zero_nonce.into())'in caller and 'let zero_nonce = [0u8; 16];'in caller
 assert 'ctr = "0.10.1"'in(source/'Cargo.toml').read_text()and 'ctr = { workspace = true, features = ["zeroize"] }'in(source/'rust/protocol/Cargo.toml').read_text()
 rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REFERENCE/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve();versions=dict(charon=subprocess.check_output([str(charon),'version'],text=True).strip(),aeneas=subprocess.check_output([str(aeneas),'-version'],text=True).strip(),rustc=subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip());assert pins['charon']['commit']in versions['charon']and pins['aeneas']['release']in versions['aeneas']and versions['rustc']==pins['charon']['rustc_version']
 candidate=args.candidate or args.profile;assert candidate.replace('-','').replace('_','').isalnum();destination=HERE/'Artifacts'/candidate;assert not destination.exists(),'preserve prior extraction';destination.mkdir(parents=True);llbc=destination/'ctr.llbc';environment=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/ctr-reference-charon-target'),RUSTFLAGS='')
 root='{impl crate::flavors::CtrFlavor for crate::flavors::ctr32::Ctr32BE}::'+args.profile
 command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from='+root,'--start-from-if-exists=crate::flavors::ctr32::*::'+args.profile,'--exclude=hybrid_array::traits::ArraySize','--dest-file='+str(llbc),'--','--package','ctr@0.10.1','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 if args.opaque_array:command.insert(command.index('--'), '--opaque=hybrid_array::Array')
 with(destination/'charon.log').open('w')as out:result=subprocess.run(command,cwd=source,env=environment,stdout=out,stderr=subprocess.STDOUT,timeout=120)
 report=dict(actual_zeroize_feature_enabled="feature=\"zeroize\""in(destination/'charon.log').read_text(),candidate_only=True,accepted_reference=False,profile=args.profile,source_patches=[],manual_generated_body_edits=False,custom_models=[],opaque_unread_nonce_array_type=args.opaque_array,ctr_version='0.10.1',selected_shared_borrow_flavor_function_has_no_feature_conditionals=True,zeroize_Drop_or_stream_wrapper_refinement=False,ctr_package_sha256=package['checksum'],protocol_caller_zero_nonce16_ctr32be_aes256=True,source_sha256=files,script_sha256=sha(pathlib.Path(__file__)),versions=versions,charon_command=[s.replace(str(ROOT),'$WORKSPACE')for s in command],charon_exit_code=result.returncode,full_CTR_AES_HMAC_wrapper_agreement=False)
 if llbc.exists():report.update(base.inventory(llbc))
 import shutil;shutil.copy2(pathlib.Path(__file__),destination/'extract-script.py')
 receipt=destination/'inventory.json';receipt.write_text(json.dumps(report,indent=2)+'\n')
 if result.returncode or not llbc.exists()or report['has_errors']or not report['counts']['ordered_decls']:print('BLOCKED actual extraction; '+str(receipt.relative_to(ROOT)));return 1
 generated=HERE/'Generated'/candidate;generated.mkdir(parents=True);command=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REFERENCE),'-subdir','/CtrReferenceV1Work/Generated/'+candidate,'-split-files','-namespace','CtrReferenceV1','-warnings-as-errors','-no-progress-bar']
 with(destination/'aeneas.log').open('w')as out:result=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit_code=result.returncode,aeneas_command=[s.replace(str(ROOT),'$WORKSPACE')for s in command],generated_files={str(p.relative_to(REFERENCE)):sha(p)for p in generated.glob('*.lean')});receipt.write_text(json.dumps(report,indent=2)+'\n');print('Actual CTR flavor Aeneas exit '+str(result.returncode));return result.returncode
if __name__=='__main__':raise SystemExit(main())
