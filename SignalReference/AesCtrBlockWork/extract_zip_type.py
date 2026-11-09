#!/usr/bin/env python3
"""One scoped partial-monomorph Zip-type extraction after name-only replay."""
import argparse,hashlib,importlib.util,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parent;ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'extract.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--candidate',default='AddRoundKeyMutTypeV1');parser.add_argument('--mir',choices=['promoted','optimized'],default='promoted');options=parser.parse_args();assert options.candidate.isalnum()
 pins=json.loads((REF/'pins.json').read_text());rust=ROOT/'.deps/rust-nightly-2026-08-18';source=ROOT/'.deps/libsignal-v0.106.1';art=HERE/'Artifacts'/options.candidate;assert not art.exists();art.mkdir(parents=True);llbc=art/'zip.llbc'
 command=[s.replace('$WORKSPACE',str(ROOT))for s in json.loads((REF/'AesZipInvestigation/Artifacts/MutAll/inventory.json').read_text())['charon_command']];command=[('--dest-file='+str(llbc))if s.startswith('--dest-file=')else s for s in command];command.insert(command.index('--'),'--include=core::iter::adapters::zip::Zip');command.insert(command.index('--'),'--mir='+options.mir)
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/aes-zip-type-reference-target'),CHARON_MIRI_SYSROOTS=str(REF/'PaddingWork/Unpad/Sysroot'),RUSTFLAGS='--cfg aes_backend="soft"')
 subprocess.run([str(rust/'bin/cargo'),'clean','--package','aes@0.9.1','--target','aarch64-apple-darwin'],cwd=source,env=env,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True,timeout=30)
 with(art/'charon.log').open('w')as log:r=subprocess.run(command,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=120)
 report=dict(candidate_only=True,accepted=False,source_patches=[],computational_body_edits=False,charon_exit_code=r.returncode,command=[s.replace(str(ROOT),'$WORKSPACE')for s in command])
 if llbc.exists():report.update(base.inventory(llbc));report['llbc_sha256']=hashlib.sha256(llbc.read_bytes()).hexdigest()
 (art/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Type-scope Charon',r.returncode)
 if r.returncode or not llbc.exists()or report['has_errors']:return
 subprocess.run(['python3',str(REF/'CtrReferenceV1Work/replay_mono_names.py'),str(llbc),str(art/'named.llbc')],check=True)
 aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();subdir='/AesCtrBlockWork/Generated/'+options.candidate;(REF/subdir.lstrip('/')).mkdir(parents=True)
 args=[str(aeneas),'-backend','lean',str(art/'named.llbc'),'-dest',str(REF),'-subdir',subdir,'-split-files','-namespace','RustCryptoAesCtrZip','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as log:r=subprocess.run(args,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=60)
 report['aeneas_exit_code']=r.returncode;(art/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('Type-scope Aeneas',r.returncode)
if __name__=='__main__':main()
