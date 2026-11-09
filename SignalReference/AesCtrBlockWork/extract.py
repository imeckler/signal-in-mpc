#!/usr/bin/env python3
"""Unchanged pinned portable AES256 encrypt entrypoint; no assumed cipher model."""
import argparse,hashlib,importlib.util,json,os,pathlib,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parent;ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'extract.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--candidate',default='EncryptV1');parser.add_argument('--monomorphize',action='store_true');parser.add_argument('--opaque-leaves',action='store_true');parser.add_argument('--operation',choices=['aes256_encrypt','inv_bitslice'],default='aes256_encrypt');parser.add_argument('--content-views',action='store_true');options=parser.parse_args();assert options.candidate.isalnum()
 pins=json.loads((REF/'pins.json').read_text());source=ROOT/'.deps/libsignal-v0.106.1';vendor=ROOT/'.deps/libsignal-vendor/aes-0.9.1'
 lock=tomllib.loads((source/'Cargo.lock').read_text());package=next(p for p in lock['package']if p['name']=='aes'and p['version']=='0.9.1');checks=json.loads((vendor/'.cargo-checksum.json').read_text());assert checks['package']==package['checksum']
 for name,want in checks['files'].items():assert sha(vendor/name)==want
 rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();versions=dict(charon=subprocess.check_output([str(charon),'version'],text=True).strip(),aeneas=subprocess.check_output([str(aeneas),'-version'],text=True).strip(),rustc=subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip());assert pins['charon']['commit']in versions['charon']and pins['aeneas']['release']in versions['aeneas']and versions['rustc']==pins['charon']['rustc_version']
 art=HERE/'Artifacts'/options.candidate;assert not art.exists();art.mkdir(parents=True);llbc=art/'aes.llbc'
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/aes-encrypt-reference-target'),RUSTFLAGS='--cfg aes_backend="soft"')
 subprocess.run([str(rust/'bin/cargo'),'clean','--package','aes@0.9.1','--target','aarch64-apple-darwin'],cwd=source,env=env,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True,timeout=30)
 args=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate::soft::fixslice::'+options.operation,'--dest-file='+str(llbc),'--','--verbose','--package','aes@0.9.1','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 if options.content_views:
  for name in ['hybrid_array']:args.insert(args.index('--'),'--include='+name)
  for name in ['default','as_slice','as_mut_slice']:args.insert(args.index('--'),'--opaque=hybrid_array::*::'+name)
 leaves=['bitslice','inv_bitslice','sub_bytes','mix_columns_0','mix_columns_1','mix_columns_2','mix_columns_3','shift_rows_2','add_round_key']if options.opaque_leaves else[]
 for leaf in leaves:args.insert(args.index('--'),'--opaque=crate::soft::fixslice::'+leaf)
 if options.monomorphize:args.insert(args.index('--'),'--monomorphize')
 with(art/'charon.log').open('w')as log:r=subprocess.run(args,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=120)
 report=dict(candidate_only=True,accepted=False,operation=options.operation,reused_leaf_boundaries=leaves,leaf_implementations_bound=False,versions=versions,charon_exit_code=r.returncode,source_patches=[],manual_generated_body_edits=False,rustflags=env['RUSTFLAGS'],package_checksum=package['checksum'],charon_command=[a.replace(str(ROOT),'$WORKSPACE')for a in args],source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source/'Cargo.lock',source/'rust/protocol/src/crypto.rs',vendor/'src/soft/fixslice64.rs']},actual_AES_or_CTR_refinement=False)
 if llbc.exists():report.update(base.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (art/'report.json').write_text(json.dumps(report,indent=2)+'\n');assert r.returncode==0 and llbc.exists() and not report['has_errors'] and report['counts']['ordered_decls']
 dest=HERE/'Generated'/options.candidate;dest.mkdir(parents=True)
 args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/AesCtrBlockWork/Generated/'+options.candidate,'-split-files','-namespace','RustCryptoAesCtrBlock','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as log:r=subprocess.run(args,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit_code=r.returncode,aeneas_command=[a.replace(str(ROOT),'$WORKSPACE')for a in args]);(art/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Actual portable AES256 encrypt extraction:',r.returncode)
if __name__=='__main__':main()
