#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path(__file__).resolve().parent;ROOT=H.parents[2]
root=sys.argv[1] if len(sys.argv)>1 else 'guarded';assert root in ('guarded','always_error')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
PINS=json.loads((ROOT/'SignalReference/pins.json').read_text());charon=(ROOT/'SignalReference'/PINS['charon']['directory']/'target/release/charon').resolve();rust=ROOT/'.deps/rust-nightly-2026-08-18'
receipt=json.loads((H/'build-report.json').read_text());binary=H/'Bin/candidate';assert sha(binary)==receipt['binary_sha256']
env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(H/'Artifacts/target'),RUSTFLAGS='')
A=H/'Artifacts';A.mkdir(exist_ok=True);llbc=A/'guard.llbc'
subprocess.run([str(rust/'bin/cargo'),'clean','--package','drop-regression','--target','aarch64-apple-darwin'],cwd=H/'Rust',env=env,check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=30)
llbc.unlink(missing_ok=True)
extract=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--precise-drops','--desugar-drops','--start-from=crate::'+root,'--dest-file='+str(llbc),'--','--lib','--offline']
with (H/'extract.log').open('w') as f:r=subprocess.run(extract,cwd=H/'Rust',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=120)
assert r.returncode==0
command=[str(binary),'-backend','lean',str(llbc),'-dest',str(ROOT/'SignalReference'),'-subdir','/ChatResponseReferenceWork/DropCandidate/Generated','-namespace','DropRegression','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
for p in (H/'Generated').glob('*.lean'):p.unlink()
with (H/'translate.log').open('w') as f:r=subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,timeout=60)
(H/(root+'-test-report.json')).write_text(json.dumps({'candidate_only':True,'exit_code':r.returncode,'binary_sha256':sha(binary),'llbc_sha256':sha(llbc),'source_sha256':sha(H/'Rust/src/lib.rs'),'script_sha256':sha(Path(__file__)),'extract':extract,'translate':command,'generated_sha256':{p.name:sha(p) for p in (H/'Generated').glob('*.lean')}},indent=2)+'\n');print('translation exit',r.returncode);raise SystemExit(r.returncode)
