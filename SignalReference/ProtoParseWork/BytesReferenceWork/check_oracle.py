#!/usr/bin/env python3
"""Public native pinned-source differential checks for the bounded content model."""
import hashlib,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];ORACLE=HERE/'Oracle'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 files=[]
 for package in ['prost-0.14.4','bytes-1.12.0']:
  root=ROOT/'.deps/libsignal-vendor'/package;checks=json.loads((root/'.cargo-checksum.json').read_text())
  for name,sha in checks['files'].items():assert digest(root/name)==sha,(package,name)
  files += [root/'.cargo-checksum.json']+[root/name for name in checks['files']]
 rust=ROOT/'.deps/rust-nightly-2026-08-18';env=os.environ.copy();env.update({'PATH':str(rust/'bin')+os.pathsep+env.get('PATH',''),'CARGO_HOME':str(ROOT/'.deps/libsignal-cargo-home'),'CARGO_TARGET_DIR':str(ORACLE/'target'),'DYLD_LIBRARY_PATH':str(rust/'lib'),'RUSTFLAGS':''})
 with (HERE/'oracle-build.log').open('w')as log:subprocess.run([str(rust/'bin/cargo'),'build','--offline','--manifest-path',str(ORACLE/'Cargo.toml')],cwd=ORACLE,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
 binary=ORACLE/'target/debug/prost-bounded-bytes-oracle'
 with (HERE/'oracle-output.txt').open('w')as out:subprocess.run([str(binary)],stdout=out,check=True)
 counts={}
 for line in (HERE/'oracle-output.txt').read_text().splitlines():
  row=line.split(' ');kind=row[0]
  if kind=='COPY':
   _,flavor,n,count,ok,got,rest=row;n=int(n);count=int(count);data=bytes((i*37+n*11)%256 for i in range(n));valid=count<=n
   assert (ok=='true')==valid and got==(data[:count].hex()if valid else '-') and rest==(data[count:]if valid else data).hex(),row
   label='copy_'+flavor
  elif kind=='MERGE':
   _,n,count,ok,value,rest=row;n=int(n);count=int(count);data=bytes((i*37+n*11)%256 for i in range(n));valid=count<=n
   assert (ok=='true')==valid and value==(data[:count].hex()if valid else 'aabb') and rest==(data[count:]if valid else data).hex(),row
   label='merge'
  elif kind=='DUP':
   _,n,count,value,rest=row;n=int(n);count=int(count);data=bytes((i*37+n*11)%256 for i in range(n));assert value==data[:count].hex()and rest=='',row;label='duplicate'
  else:raise AssertionError(row)
  counts[label]=counts.get(label,0)+1
 files += [ORACLE/'Cargo.toml',ORACLE/'Cargo.lock',ORACLE/'src/main.rs',Path(__file__)]
 (HERE/'oracle-report.json').write_text(json.dumps({'candidate_only':True,'accepted_model':False,'cases':counts,'all_cases_passed':True,'source_sha256':{str(p.relative_to(ROOT)):digest(p)for p in files},'binary_sha256':digest(binary),'output_sha256':digest(HERE/'oracle-output.txt'),'rustc_version':subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip(),'rust_source_changes':[],'scope':'Native pinned slice/Bytes copy prefix/suffix/overflow, actual prost bytes merge underflow/overwrite and repeated fields including empty replacement. Public fixtures support source review; they are not a universal translation/model proof.'},indent=2)+'\n')
 print(counts)
if __name__=='__main__':main()
