#!/usr/bin/env python3
"""Observe actual pinned InOut/hybrid-array alias/disjoint/default/index/writeback behavior."""
import hashlib,json,os,pathlib,shutil,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 stage=ROOT/'.deps/reference-write-buffer-library-v1';assert not stage.exists();(stage/'src').mkdir(parents=True)
 shutil.copy2(HERE/'LibraryOracle/Cargo.toml',stage/'Cargo.toml');shutil.copy2(HERE/'LibraryOracle/main.rs',stage/'src/main.rs');(stage/'.cargo').mkdir();(stage/'.cargo/config.toml').write_text('[source.crates-io]\nreplace-with="vendor"\n[source.vendor]\ndirectory="'+str(ROOT/'.deps/libsignal-vendor')+'"\n')
 rust=ROOT/'.deps/rust-nightly-2026-08-18';pins=json.loads((REF/'pins.json').read_text());version=subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip();assert version==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),DYLD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-write-buffer-library-target'))
 subprocess.run([str(rust/'bin/cargo'),'generate-lockfile','--offline'],cwd=stage,env=env,capture_output=True,check=True)
 lookup={(p['name'],p['version']):p.get('checksum')for p in tomllib.loads((ROOT/'.deps/libsignal-v0.106.1/Cargo.lock').read_text())['package']}
 for p in tomllib.loads((stage/'Cargo.lock').read_text())['package']:
  if p['name']!='read-buffer-write-content-oracle':assert lookup[(p['name'],p['version'])]==p['checksum']
 files=[pathlib.Path(__file__),HERE/'LibraryOracle/Cargo.toml',HERE/'LibraryOracle/main.rs']
 for name in ['block-buffer-0.12.1','hybrid-array-0.4.13']:
  d=ROOT/'.deps/libsignal-vendor'/name
  for rel,want in json.loads((d/'.cargo-checksum.json').read_text())['files'].items():assert sha(d/rel)==want;files.append(d/rel)
 with(stage/'build.log').open('w')as f:r=subprocess.run([str(rust/'bin/cargo'),'build','--offline','--locked'],cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
 assert r.returncode==0,(stage/'build.log').read_text()
 binary=ROOT/'.deps/reference-write-buffer-library-target/debug/read-buffer-write-content-oracle';result=json.loads(subprocess.check_output([str(binary)],text=True));assert result==dict(passed=True,public_seeds=64,observations=11328)
 (HERE/'library-report.json').write_text(json.dumps(dict(**result,public_only=True,trusted_content_model_not_mechanized_library_proof=True,scope='actual pinned ReadBuffer write_block success/zero/oversize and generator/read panic ResetGuard behavior',rustc=version,binary_sha256=sha(binary),lock_sha256=sha(stage/'Cargo.lock'),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS actual pinned library',result)
if __name__=='__main__':main()
