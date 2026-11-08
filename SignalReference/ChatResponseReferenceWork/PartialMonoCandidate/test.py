#!/usr/bin/env python3
"""Original failure, scoped positive/negative regressions, unchanged Prost."""
from pathlib import Path
import os,subprocess,json,hashlib
H=Path(__file__).resolve().parent;ROOT=H.parents[2];rust=ROOT/'.deps/rust-nightly-2026-08-18';original=ROOT/'.deps/charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8/charon/target/release/charon';candidate=H/'Build/tool/release/charon'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
build=json.loads((H/'build-report.json').read_text());assert sha(candidate)==build['binaries'][str(candidate.relative_to(ROOT))]
env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env['PATH'],CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'))
base=['--preset=aeneas','--sysroot=default','--error-on-warnings','--no-dedup-serialized-ast','--monomorphize-mut=all'];results=[]
for tool,binary in [('original',original),('candidate',candidate)]:
 for case,root in [('static','entry'),('free','free_entry'),('abstract','merge'),('mixed','mixed')]:
  env['CARGO_TARGET_DIR']=str(H/'Build'/('regression-'+tool));out=H/'Artifacts'/(tool+'-'+case+'.llbc');out.unlink(missing_ok=True)
  command=[str(binary),'cargo',*base,'--start-from=crate::'+root,'--dest-file='+str(out),'--','--lib','--offline','--locked']
  with (H/(tool+'-'+case+'.log')).open('w') as f:p=subprocess.run(command,cwd=H/'Regression',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=120)
  llbc=json.loads(out.read_text()) if out.exists() else None;log=(H/(tool+'-'+case+'.log')).read_text();passed=p.returncode==0 and llbc is not None and not llbc['has_errors'];expect=case=='free' or (tool=='candidate' and case=='static');assert passed==expect,(tool,case,p.returncode,log[:2000])
  if tool=='candidate' and case in ('abstract','mixed'):assert 'unsupported; method and implementation specialization is required' in log or 'leaves an abstract caller' in log
  results.append({'tool':tool,'case':case,'exit_code':p.returncode,'has_errors':None if llbc is None else llbc['has_errors'],'command':command,'log_sha256':sha(H/(tool+'-'+case+'.log')),'llbc_sha256':sha(out) if out.exists() else None})
# Native typed counterpart tests the same actual impl and exact borrowed input.
env['CARGO_TARGET_DIR']=str(H/'Build/native')
with (H/'native.log').open('w') as f:subprocess.run([str(rust/'bin/cargo'),'run','--offline','--locked','--bin','check'],cwd=H/'Regression',env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=120)
assert 'Compared 4097 actual generic/closed-impl results and exact borrowed inputs' in (H/'native.log').read_text()
# Unchanged pinned Prost body; explicit std UTF8 and varint boundaries remain.
env['CARGO_TARGET_DIR']=str(H/'Build/prost-candidate')
args=['--start-from=crate::encoding::string::merge','--include=core::mem::forget','--include=core::mem::manually_drop::*::new','--include=bytes::buf::take::Take','--include=bytes::buf::buf_impl::Buf::take','--include=bytes::buf::take::new','--opaque=core::str::converts::from_utf8','--opaque=crate::encoding::varint::decode_varint']
subprocess.run([str(rust/'bin/cargo'),'clean','--package','prost@0.14.4','--target','aarch64-apple-darwin'],cwd=H.parent/'Rust',env=env,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=True,timeout=60)
prost=H/'Artifacts/prost.llbc';prost.unlink(missing_ok=True);command=[str(candidate),'cargo',*base,*args,'--dest-file='+str(prost),'--','--package','prost@0.14.4','--lib','--offline','--locked']
with (H/'prost.log').open('w') as f:p=subprocess.run(command,cwd=H.parent/'Rust',env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180)
llbc=json.loads(prost.read_text()) if prost.exists() else None
report={'candidate_only':True,'build_report_sha256':sha(H/'build-report.json'),'regression_source_sha256':sha(H/'Regression/src/lib.rs'),'native_source_sha256':sha(H/'Regression/src/bin/check.rs'),'script_sha256':sha(Path(__file__)),'regressions':results,'native_log':(H/'native.log').read_text(),'prost':{'exit_code':p.returncode,'has_errors':None if llbc is None else llbc['has_errors'],'command':command,'llbc_sha256':sha(prost) if prost.exists() else None,'log_sha256':sha(H/'prost.log')},'does_not_claim_full_string_or_response_refinement':True}
(H/'test-report.json').write_text(json.dumps(report,indent=2)+'\n');print('regressions/native pass; Prost exit',p.returncode);raise SystemExit(p.returncode if p.returncode else int(llbc is None or llbc['has_errors']))
