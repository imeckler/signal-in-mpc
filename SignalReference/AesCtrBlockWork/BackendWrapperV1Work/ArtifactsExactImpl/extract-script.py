#!/usr/bin/env python3
"""Unchanged pinned soft AES backend packaging, with actual fixslice entry opaque for linking."""
import hashlib,importlib.util,json,os,pathlib,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 pins=json.loads((REF/'pins.json').read_text());source=ROOT/'.deps/libsignal-v0.106.1';vendor=ROOT/'.deps/libsignal-vendor/aes-0.9.1';checks=json.loads((vendor/'.cargo-checksum.json').read_text());lock=tomllib.loads((source/'Cargo.lock').read_text());assert checks['package']==next(p['checksum']for p in lock['package']if p['name']=='aes'and p['version']=='0.9.1')
 for name,want in checks['files'].items():assert sha(vendor/name)==want
 rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve()
 assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 art=HERE/'ArtifactsExactImpl';art.mkdir(exist_ok=False);(art/'extract-script.py').write_text(pathlib.Path(__file__).read_text());llbc=art/'backend.llbc'
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/aes-backend-reference-target'),RUSTFLAGS='--cfg aes_backend="soft"')
 command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from={impl cipher::block::backends::BlockCipherEncBackend for crate::soft::Aes256BackEnc}::encrypt_block','--start-from-if-exists={impl cipher::block::backends::BlockCipherEncBackend for crate::soft::Aes256BackEnc}::encrypt_par_blocks','--opaque=crate::soft::fixslice::*','--exclude=hybrid_array::traits::ArraySize','--dest-file='+str(llbc),'--','--verbose','--package','aes@0.9.1','--lib','--locked','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as log:r=subprocess.run(command,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=120)
 report=dict(candidate_only=True,accepted=False,source_patches=[],generated_body_edits=False,charon_exit=r.returncode,command=command,actual_fixslice_link_not_yet_proved=True,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),vendor/'src/soft.rs',source/'Cargo.lock']})
 if llbc.exists():
  spec=importlib.util.spec_from_file_location('extract',REF/'extract.py');b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b);report.update(b.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (art/'report.json').write_text(json.dumps(report,indent=2)+'\n')
 if r.returncode or not llbc.exists()or report['has_errors']or not report['counts']['ordered_decls']:print('BLOCKED',report.get('counts'));return
 dest=HERE/'Generated';dest.mkdir();command=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/AesCtrBlockWork/BackendWrapperV1Work/Generated','-split-files','-namespace','ActualAesBackendWrapper','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as log:r=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=command);(art/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Aeneas',r.returncode)
if __name__=='__main__':main()
