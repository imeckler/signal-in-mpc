#!/usr/bin/env python3
"""Build an isolated public oracle against unchanged pinned portable AES/CTR."""
import hashlib,json,os,pathlib,shutil,subprocess,tomllib
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 stage=ROOT/'.deps/reference-fixslice-oracle-source-v1';assert not stage.exists();(stage/'src').mkdir(parents=True)
 for source,target in [('Oracle/Cargo.toml','Cargo.toml'),('Oracle/main.rs','src/main.rs')]:shutil.copy2(HERE/source,stage/target)
 (stage/'.cargo').mkdir();(stage/'.cargo/config.toml').write_text('[source.crates-io]\nreplace-with="vendor"\n[source.vendor]\ndirectory="'+str(ROOT/'.deps/libsignal-vendor')+'"\n')
 rust=ROOT/'.deps/rust-nightly-2026-08-18';pins=json.loads((REF/'pins.json').read_text());version=subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip();assert version==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),DYLD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-fixslice-oracle-target'),RUSTFLAGS='--cfg aes_backend="soft"')
 subprocess.run([str(rust/'bin/cargo'),'generate-lockfile','--offline'],cwd=stage,env=env,check=True,capture_output=True)
 locked=tomllib.loads((ROOT/'.deps/libsignal-v0.106.1/Cargo.lock').read_text());lookup={(p['name'],p['version']):p.get('checksum')for p in locked['package']}
 for p in tomllib.loads((stage/'Cargo.lock').read_text())['package']:
  if p['name']=='reference-fixslice-oracle':continue
  assert lookup[(p['name'],p['version'])]==p['checksum'],p
 files=[pathlib.Path(__file__),HERE/'Oracle/Cargo.toml',HERE/'Oracle/main.rs']
 for name in ['aes-0.9.1','ctr-0.10.1','cipher-0.5.2']:
  folder=ROOT/'.deps/libsignal-vendor'/name;checks=json.loads((folder/'.cargo-checksum.json').read_text())
  for rel,want in checks['files'].items():
   if rel.startswith('src/')or rel=='Cargo.toml':assert sha(folder/rel)==want;files.append(folder/rel)
 with(stage/'build.log').open('w')as log:r=subprocess.run([str(rust/'bin/cargo'),'build','--offline','--locked'],cwd=stage,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=120)
 assert r.returncode==0,(stage/'build.log').read_text()[-4000:]
 binary=ROOT/'.deps/reference-fixslice-oracle-target/debug/reference-fixslice-oracle';profile=json.loads(subprocess.check_output([str(binary)],input='{"mode":"profile"}\n',text=True));assert profile['forced_soft']and profile['pointer_bits']==64 and profile['debug_assertions']
 (HERE/'oracle-build-report.json').write_text(json.dumps(dict(passed=True,public_fixture_only=True,actual_public_cipher_and_Ctr32BE_traits=True,forced_portable_noncompact=True,source_patches=False,rustc=version,profile=profile,binary_sha256=sha(binary),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},stage=str(stage.relative_to(ROOT)),lock_sha256=sha(stage/'Cargo.lock')),indent=2)+'\n');print('PASS pinned public portable AES/CTR oracle build')
if __name__=='__main__':main()
