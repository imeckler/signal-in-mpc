#!/usr/bin/env python3
"""Actual pinned mutable Buf forwarding bridge, preserving error and suffix."""
from pathlib import Path
import copy,json,subprocess,os,hashlib
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();run=lambda a,**kw:subprocess.run(a,check=True,timeout=180,**kw)
rust=ROOT/'.deps/rust-nightly-2026-08-18';binary=ROOT/'.deps/charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8/charon/target/release/charon';translator=H.parent/'TranslatorCandidate/Bin/candidate'
assert sha(translator)==json.loads((H.parent/'TranslatorCandidate/build-report.json').read_text())['binary_sha256']
vendor=ROOT/'.deps/libsignal-vendor/bytes-1.12.0';checks=json.loads((vendor/'.cargo-checksum.json').read_text())['files']
for name,digest in checks.items():assert sha(vendor/name)==digest,name
rev=H/'Build/forward-audit';rev.mkdir(parents=True,exist_ok=True);env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env['PATH'],CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),CARGO_TARGET_DIR=str(H/'Build/forward-actual'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'))
run([str(rust/'bin/cargo'),'clean','--package','actual-buf-forward-reference','--target','aarch64-apple-darwin'],cwd=H/'ForwardActual',env=env,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
raw=H/'Artifacts/forward-actual.llbc';raw.unlink(missing_ok=True)
command=[str(binary),'cargo','--preset=aeneas','--sysroot=default','--error-on-warnings','--no-dedup-serialized-ast','--monomorphize-mut=all','--start-from=crate::forward_actual','--include=bytes::buf::buf_impl::*::advance','--dest-file='+str(raw),'--','--lib','--offline','--locked']
with (H/'forward-actual.log').open('w') as f:run(command,cwd=H/'ForwardActual',env=env,stdout=f,stderr=subprocess.STDOUT)
original=json.loads(raw.read_text());assert not original['has_errors']
# Preserve the unmodified failure as a separate executable regression.
unfixed=H/'Artifacts/forward-actual-unfixed-named.llbc';run(['python3',str(H/'name_specializations.py'),str(raw),str(unfixed)])
unfixed_command=[str(translator),'-backend','lean',str(unfixed),'-dest',str(ROOT/'SignalReference'),'-subdir','/ChatResponseReferenceWork/PartialMonoCandidate/Build/Unfixed','-namespace','UnfixedBufForward','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'forward-unfixed.log').open('w') as f:unfixed_result=subprocess.run(unfixed_command,stdout=f,stderr=subprocess.STDOUT,timeout=180)
assert unfixed_result.returncode!=0 and "Can't copy a mutable borrow" in (H/'forward-unfixed.log').read_text()

# Strict negative transformations, checked before any generated proof is used.
negatives=[]
for case in ['other_value_use','raw_pointer','shared_reborrow']:
 d=copy.deepcopy(original);f=next(f for f in d['translated']['fun_decls'] if f and any(p.get('Ident',[''])[0]=='advance' for p in f['item_meta']['name']) and isinstance(f['body'],dict));body=f['body']['Structured'];assigns=[]
 def walk(v):
  if isinstance(v,dict):
   if isinstance(v.get('kind'),dict) and 'Assign' in v['kind']:assigns.append(v)
   for z in v.values():walk(z)
  elif isinstance(v,list):
   for z in v:walk(z)
 walk(body['body']);copy_stmt=next(s for s in assigns if 'Use' in s['kind']['Assign'][1] and 'Copy' in s['kind']['Assign'][1]['Use'][0] and 'Ref' in s['kind']['Assign'][0]['ty'].get('Untagged',{}));temp=copy_stmt['kind']['Assign'][0]
 if case=='other_value_use':body['body']['statements'].append(copy.deepcopy(copy_stmt))
 elif case=='raw_pointer':temp['ty']={'Untagged':{'RawPtr':[temp['ty']['Untagged']['Ref'][1],'Mut']}}
 else:next(s for s in assigns if 'Ref' in s['kind']['Assign'][1])['kind']['Assign'][1]['Ref']['kind']='Shared'
 path=rev/(case+'.llbc');path.write_text(json.dumps(d));p=subprocess.run(['python3',str(H/'canonicalize_forward_reborrow.py'),'--input',str(path),'--output',str(rev/'rejected.llbc')],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=30);assert p.returncode!=0,case;negatives.append(case)
run(['python3',str(H/'canonicalize_forward_reborrow.py')]);lowered=H/'Artifacts/forward-actual-reborrow.llbc';named=H/'Artifacts/forward-actual-reborrow-named.llbc';run(['python3',str(H/'name_specializations.py'),str(lowered),str(named)])
translation=[str(translator),'-backend','lean',str(named),'-dest',str(ROOT/'SignalReference'),'-subdir','/ChatResponseReferenceWork/PartialMonoCandidate/GeneratedForwardActual','-namespace','ActualBufForward','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'forward-actual-translate.log').open('w') as f:run(translation,stdout=f,stderr=subprocess.STDOUT)
env['CARGO_TARGET_DIR']=str(H/'Build/forward-native')
with (H/'forward-native.log').open('w') as f:run([str(rust/'bin/cargo'),'run','--offline','--locked','--bin','check'],cwd=H/'ForwardActual',env=env,stdout=f,stderr=subprocess.STDOUT)
native=(H/'forward-native.log').read_text();assert 'Compared 1188 actual/direct forwarding outcomes and exact suffixes, including 66 exact panic payloads' in native
output=H/'Build/forward-final-lean';env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output);modules=['PartialMonoCandidate.GeneratedForwardActual.Types','PartialMonoCandidate.GeneratedForwardActual.Funs','PartialMonoCandidate.ActualForwardReference']
with (H/'actual-forward-kernel.log').open('w') as f:run(['python3',str(H.parent/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT)
log=(H/'actual-forward-kernel.log').read_text();assert 'sorryAx' not in log
for theorem in ['forward_all_outcomes','raw_forward_success']:assert theorem+"' does not depend on any axioms" in log
for name,digest in checks.items():assert sha(vendor/name)==digest,name
paths=[H/p for p in ['check_forward.py','canonicalize_forward_reborrow.py','ActualForwardReference.lean','ForwardActual/Cargo.toml','ForwardActual/Cargo.lock','ForwardActual/.cargo/config.toml','ForwardActual/src/lib.rs','ForwardActual/src/bin/check.rs']]+sorted((H/'GeneratedForwardActual').glob('*.lean'))
(H/'forward-audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Actual native mutable Buf forwarding and exact observed receiver projection; all outcomes relative to delegated trait operation. No assumed adapter behavior or full String claim.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in paths},'charon_binary_sha256':sha(binary),'aeneas_binary_sha256':sha(translator),'extraction_command':command,'translation_command':translation,'rewrite':json.loads(lowered.with_suffix('.rewrite.json').read_text()),'name_receipt_sha256':sha(named.with_suffix('.names.json')),'negative_cases':negatives,'unmodified_translation':{'exit_code':unfixed_result.returncode,'command':unfixed_command,'log_sha256':sha(H/'forward-unfixed.log')},'native_log':native,'kernel_log':log,'verified_bytes_files':len(checks),'native_applicability':'Safe Sized contiguous &[u8]/Bytes buffers; selected actual source helper. Raw-pointer/unsized memory behavior is not claimed.','object_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules}},indent=2)+'\n');print('actual forwarding projection/native/rejection regressions PASS')
