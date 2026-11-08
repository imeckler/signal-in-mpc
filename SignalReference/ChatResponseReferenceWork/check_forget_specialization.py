#!/usr/bin/env python3
"""Strict typed LLBC specialization regression; no generated Lean body edits."""
from pathlib import Path
import copy,json,subprocess,hashlib,os
H=Path(__file__).resolve().parent;ROOT=H.parents[1];rev=H/'Revisions/forget-specialization';rev.mkdir(parents=True,exist_ok=True)
run=lambda args,**kw:subprocess.run(args,check=True,timeout=180,**kw)
run(['python3',str(H/'extract.py'),'string_forget']);run(['python3',str(H/'specialize_forget_guard.py')])
original=json.loads((H/'Artifacts/string_forget/chat.llbc').read_text());tests=[]
for variant in ['wrong_guard','wrong_callee_body','multiple_calls']:
 d=copy.deepcopy(original);x=d['translated'];f=next(f for f in x['fun_decls'] if f and f['def_id']==8)
 if variant=='wrong_guard':x['type_decls'][0]['item_meta']['name'][-1]['Ident'][0]='OtherGuard'
 elif variant=='wrong_callee_body':f['body']['Structured']['body']['statements'].append(copy.deepcopy(f['body']['Structured']['body']['statements'][-1]))
 else:x['fun_decls'].append(copy.deepcopy(x['fun_decls'][0]))
 source=rev/(variant+'.llbc');source.write_text(json.dumps(d))
 p=subprocess.run(['python3',str(H/'specialize_forget_guard.py'),'--input',str(source),'--output',str(rev/'rejected.llbc'),'--receipt',str(rev/'rejected.json')],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=30)
 assert p.returncode!=0;tests.append(variant)
binary=ROOT/'.deps/aeneas-2026-08-27/aeneas';command=[str(binary),'-backend','lean',str(H/'Artifacts/string_forget/specialized.llbc'),'-dest',str(ROOT/'SignalReference'),'-subdir','/ChatResponseReferenceWork/GeneratedStringForgetSpecialized','-namespace','ActualChatResponseStringForgetSpecialized','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'forget-specialized-translate.log').open('w') as f:run(command,stdout=f,stderr=subprocess.STDOUT)
s=(H/'GeneratedStringForgetSpecialized/Funs.lean').read_text();start=s.index('def prost.reference_forget_drop_guard\n');end=s.index('\n/--',start);decl=s[start:end]
assert ':= do\n  ok t' in decl
core='''-- Mechanical exact declaration replay; see forget-specialization-audit.json.
import Aeneas
open Aeneas Aeneas.Std Result
namespace ActualChatResponseStringForgetSpecialized
def encoding.string.merge.DropGuard := alloc.vec.Vec U8
'''+decl+'''\ntheorem forget_preserves_borrow (v : encoding.string.merge.DropGuard) :
  prost.reference_forget_drop_guard v = .ok v := rfl
#print axioms forget_preserves_borrow
end ActualChatResponseStringForgetSpecialized
'''
(H/'ForgetSpecializationReference.lean').write_text(core)
output=rev/'Build';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
with (H/'forget-specialization-audit.log').open('w') as f:run(['python3',str(H/'check.py'),'ForgetSpecializationReference'],env=env,stdout=f,stderr=subprocess.STDOUT)
log=(H/'forget-specialization-audit.log').read_text();assert "forget_preserves_borrow' depends on axioms: [propext]" in log
rust=ROOT/'.deps/rust-nightly-2026-08-18';env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env['PATH'],CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/chat-response-owned-diff-target'))
stdsource=rust/'lib/rustlib/src/rust/library/core/src/mem/mod.rs'
assert 'pub const fn forget<T>(t: T) {\n    let _ = ManuallyDrop::new(t);\n}' in stdsource.read_text()
with (H/'forget-specialization-native.log').open('w') as f:run([str(rust/'bin/cargo'),'run','--offline','--locked','--bin','forget-guard-check'],cwd=H/'Rust',env=env,stdout=f,stderr=subprocess.STDOUT)
nativelog=(H/'forget-specialization-native.log').read_text();assert 'Compared 513 actual generic/specialized forget outcomes and actual cleanup effects' in nativelog
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=[H/'specialize_forget_guard.py',H/'check_forget_specialization.py',H/'ForgetSpecializationReference.lean',H/'GeneratedStringForgetSpecialized/Funs.lean',H/'Rust/src/bin/forget-guard-check.rs',stdsource]
(H/'forget-specialization-audit.json').write_text(json.dumps({'candidate_only':True,'body_unchanged':True,'generated_body_hand_edits':False,'strict_negative_tests':tests,'specialization':json.loads((H/'forget-guard-specialization.json').read_text()),'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in paths},'translator_sha256':sha(binary),'command':command,'lean_log':log,'native_log':nativelog,'scope':'Exact specialized forget declaration, not full generated string merge kernel check. Precise error cleanup/full String content composition remain separately open.'},indent=2)+'\n');print('typed forget specialization fragment PASS; 3 strict negative regressions')
