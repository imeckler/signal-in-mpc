#!/usr/bin/env python3
"""Concrete call roots retain actual generic backend methods during monomorphization."""
import hashlib,importlib.util,json,os,pathlib,shutil,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 stage=ROOT/'.deps/reference-aes-backend-harness-v1';assert not stage.exists();(stage/'src').mkdir(parents=True)
 shutil.copy2(HERE/'Harness/Cargo.toml',stage/'Cargo.toml');shutil.copy2(HERE/'Harness/lib.rs',stage/'src/lib.rs')
 (stage/'.cargo').mkdir();(stage/'.cargo/config.toml').write_text('[source.crates-io]\nreplace-with="vendor"\n[source.vendor]\ndirectory="'+str(ROOT/'.deps/libsignal-vendor')+'"\n')
 pins=json.loads((REF/'pins.json').read_text());rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve()
 assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-aes-backend-harness-target'),RUSTFLAGS='--cfg aes_backend="soft"')
 subprocess.run([str(rust/'bin/cargo'),'generate-lockfile','--offline'],cwd=stage,env=env,check=True,capture_output=True)
 lookup={(p['name'],p['version']):p.get('checksum')for p in tomllib.loads((ROOT/'.deps/libsignal-v0.106.1/Cargo.lock').read_text())['package']}
 for p in tomllib.loads((stage/'Cargo.lock').read_text())['package']:
  if p['name']!='reference-aes-backend-harness':assert lookup[(p['name'],p['version'])]==p['checksum']
 art=HERE/'ArtifactsConcreteHarness';art.mkdir(exist_ok=False);llbc=art/'harness.llbc'
 args=[str(charon),'cargo','--preset=aeneas','--monomorphize','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate::encrypt_one','--start-from=crate::encrypt_four','--include=aes::soft','--include=cipher::block','--opaque=aes::soft::fixslice::*','--exclude=hybrid_array::traits::ArraySize','--dest-file='+str(llbc),'--','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as f:r=subprocess.run(args,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=120)
 report=dict(candidate_only=True,accepted=False,charon_exit=r.returncode,command=args,actual_dependencies_unmodified=True,opaque_fixslice_for_linking_not_assumed_correct=True,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),HERE/'Harness/Cargo.toml',HERE/'Harness/lib.rs',stage/'Cargo.lock']})
 if llbc.exists():
  spec=importlib.util.spec_from_file_location('x',REF/'extract.py');x=importlib.util.module_from_spec(spec);spec.loader.exec_module(x);report.update(x.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (art/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 if r.returncode or not llbc.exists()or report['has_errors']or not report['counts']['ordered_decls']:print('BLOCKED concrete harness',report.get('counts'));return
 dest=HERE/'GeneratedConcreteHarness';dest.mkdir();args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/AesCtrBlockWork/BackendWrapperV1Work/GeneratedConcreteHarness','-split-files','-namespace','ActualAesBackendHarness','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=args);(art/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Aeneas concrete harness',r.returncode)
if __name__=='__main__':main()
