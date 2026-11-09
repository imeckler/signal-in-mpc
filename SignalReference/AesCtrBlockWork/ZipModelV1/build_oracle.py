#!/usr/bin/env python3
"""Build PUBLIC-only oracle: exact vendor module prefix + forwarding append."""
import hashlib,json,os,pathlib,shutil,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 stage=ROOT/'.deps/aes-std-borrow-oracle-source-v1';assert not stage.exists();(stage/'src').mkdir(parents=True)
 vendor=ROOT/'.deps/libsignal-vendor/aes-0.9.1';source=vendor/'src/soft/fixslice64.rs';checks=json.loads((vendor/'.cargo-checksum.json').read_text());assert sha(source)==checks['files']['src/soft/fixslice64.rs']
 shutil.copy2(HERE/'Oracle/Cargo.toml',stage/'Cargo.toml');shutil.copy2(HERE/'Oracle/main.rs',stage/'src/main.rs');body=source.read_bytes();suffix=(HERE/'Oracle/wrappers.rs').read_bytes();(stage/'src/fixslice.rs').write_bytes(body+b'\n'+suffix);assert(stage/'src/fixslice.rs').read_bytes()[:len(body)]==body
 (stage/'.cargo').mkdir();(stage/'.cargo/config.toml').write_text('[source.crates-io]\nreplace-with="vendor"\n[source.vendor]\ndirectory="'+str(ROOT/'.deps/libsignal-vendor')+'"\n')
 rust=ROOT/'.deps/rust-nightly-2026-08-18';pins=json.loads((REF/'pins.json').read_text());version=subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip();assert version==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),DYLD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/aes-std-borrow-oracle-target'),RUSTFLAGS='')
 subprocess.run([str(rust/'bin/cargo'),'generate-lockfile','--offline'],cwd=stage,env=env,check=True,capture_output=True)
 locked=tomllib.loads((ROOT/'.deps/libsignal-v0.106.1/Cargo.lock').read_text());lookup={(p['name'],p['version']):p.get('checksum')for p in locked['package']}
 for p in tomllib.loads((stage/'Cargo.lock').read_text())['package']:
  if p['name']=='aes-std-borrow-oracle':continue
  assert lookup[(p['name'],p['version'])]==p['checksum']
 with(stage/'build.log').open('w')as log:r=subprocess.run([str(rust/'bin/cargo'),'build','--offline','--locked'],cwd=stage,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=120)
 assert r.returncode==0,(stage/'build.log').read_text()[-4000:]
 binary=ROOT/'.deps/aes-std-borrow-oracle-target/debug/aes-std-borrow-oracle';profile=json.loads(subprocess.check_output([str(binary)],input='{"mode":"profile"}\n',text=True));assert profile['debug_assertions']and profile['pointer_bits']==64
 (HERE/'oracle-build-report.json').write_text(json.dumps(dict(passed=True,public_fixture_only=True,rustc=version,unchanged_actual_vendor_prefix=True,appended_forwarding_only=True,profile=profile,binary_sha256=sha(binary),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),HERE/'Oracle/Cargo.toml',HERE/'Oracle/main.rs',HERE/'Oracle/wrappers.rs',source]},stage=str(stage.relative_to(ROOT)),runtime_bitness=64),indent=2)+'\n');print('PASS pinned Rust public StdZip +actual AES forwarding oracle build')
if __name__=='__main__':main()
