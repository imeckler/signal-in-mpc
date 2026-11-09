#!/usr/bin/env python3
"""Concrete public type-selection harness; all ctr computational bodies upstream."""
import argparse,hashlib,json,os,pathlib,shutil,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parent;ROOT=REF.parent
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--candidate',default='ConcreteV1');parser.add_argument('--root',choices=['both','current','remaining'],default='both');parser.add_argument('--include-helpers',action='store_true');parser.add_argument('--opaque-default',action='store_true');parser.add_argument('--opaque-views',action='store_true');args=parser.parse_args();assert args.candidate.replace('_','').isalnum();
 stage=ROOT/('.deps/ctr-mono-reference-source-'+args.candidate);assert not stage.exists();stage.mkdir();
 for name in ['Cargo.toml','lib.rs']:shutil.copy2(HERE/'Source'/name,stage/name)
 (stage/'.cargo').mkdir();(stage/'.cargo/config.toml').write_text('[source.crates-io]\nreplace-with="vendored-sources"\n[source.vendored-sources]\ndirectory="'+str(ROOT/'.deps/libsignal-vendor')+'"\n')
 pins=json.loads((REF/'pins.json').read_text());rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();environment=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/ctr-reference-charon-target'),RUSTFLAGS='')
 subprocess.run([str(rust/'bin/cargo'),'generate-lockfile','--offline'],cwd=stage,env=environment,check=True,capture_output=True,timeout=30)
 actual=tomllib.loads((ROOT/'.deps/libsignal-v0.106.1/Cargo.lock').read_text());lookup={(p['name'],p['version']):p.get('checksum')for p in actual['package']};resolved=tomllib.loads((stage/'Cargo.lock').read_text());dependencies={}
 for package in resolved['package']:
  if package['name']=='signal-ctr-reference':continue
  key=(package['name'],package['version']);assert lookup[key]==package['checksum'];dependencies['@'.join(key)]=package['checksum']
 destination=HERE/'Artifacts'/args.candidate;assert not destination.exists();destination.mkdir(parents=True);llbc=destination/'ctr.llbc'
 command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--monomorphize','--start-from=crate::current','--start-from=crate::remaining','--include=ctr','--include=core::convert','--include=core::result','--dest-file='+str(llbc),'--','--verbose','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 if args.opaque_views:
  for name in ['as_slice','as_mut_slice']:command.insert(command.index('--'),'--opaque=hybrid_array::*::'+name)
 if args.opaque_default:command.insert(command.index('--'),'--opaque=hybrid_array::*::default')
 if args.include_helpers:
  for name in ['hybrid_array','typenum']:command.insert(command.index('--'),'--include='+name)
 if args.root!='both':command.remove('--start-from=crate::'+('remaining'if args.root=='current'else'current'))
 with(destination/'charon.log').open('w')as out:result=subprocess.run(command,cwd=stage,env=environment,stdout=out,stderr=subprocess.STDOUT,timeout=120)
 report=dict(candidate_only=True,accepted_reference=False,source_wrapper_only_calls_unchanged_upstream=True,upstream_computational_body_edits=False,charon_exit_code=result.returncode,charon_command=[s.replace(str(ROOT),'$WORKSPACE')for s in command],dependency_checksums_match_pinned_Signal_lock=dependencies,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),HERE/'Source/Cargo.toml',HERE/'Source/lib.rs']},lock_sha256=sha(stage/'Cargo.lock'),llbc_sha256=sha(llbc)if llbc.exists()else None,full_ctr_refinement=False)
 (destination/'inventory.json').write_text(json.dumps(report,indent=2)+'\n');print('Concrete CTR Charon exit',result.returncode)
 return result.returncode
if __name__=='__main__':raise SystemExit(main())
