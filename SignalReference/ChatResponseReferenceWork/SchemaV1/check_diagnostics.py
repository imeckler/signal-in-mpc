#!/usr/bin/env python3
"""Bounded diagnostic model + native literal replay; actual static bridge OPEN."""
from pathlib import Path
import copy,hashlib,importlib.util,json,os,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def module(name):
 spec=importlib.util.spec_from_file_location(name,H/(name+'.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
special=module('specialize_push');box=module('box_reborrow');raw=H/'Artifacts/stamp/stamp.llbc';schema=H/'Artifacts/schema.llbc';minimal=json.loads(raw.read_text());full=json.loads(schema.read_text());
for label,data in [('stamp',minimal),('schema',full)]:
 entry=next(f for f in data['translated']['files'] if f['name']=={'Local':'src/lib.rs'});assert (H/'SourceSnapshots'/f'{label}-lib.rs').read_text()==entry['contents']
lowered,receipt=special.specialize(minimal);normalized,br=box.normalize(lowered);all_lowered,all_receipt=special.specialize(full);all_normalized,all_br=box.normalize(all_lowered);assert len(all_receipt['specialized_functions'])==13 and len(all_br)==13
calls=[]
def find(v):
 if isinstance(v,dict):
  if 'Call' in v:
   c=v['Call']['call']
   if c['func'].get('Regular',{}).get('kind')=={'Fun':{'Regular':1}}:calls.append(c)
  for a in v.values():find(a)
 elif isinstance(v,list):
  for a in v:find(a)
find(minimal);assert len(calls)==1
negative=[]
for name in ['dynamic-local','mutable-string','nonliteral-payload']:
 mutant=copy.deepcopy(minimal);calls=[];find(mutant);arg=calls[0]['args'][2];payload,ty=arg['Const']['Untagged']
 if name=='dynamic-local':calls[0]['args'][2]={'Copy':{'kind':{'Local':22},'ty':ty}}
 elif name=='mutable-string':ty['Untagged']['Ref'][2]='Mut'
 else:payload['Literal']={'ByteStr':[1,2]}
 try:special.specialize(mutant)
 except (AssertionError,KeyError,ValueError):negative.append(name)
 else:raise AssertionError('accepted '+name)
for name in ['box-extra-use','box-shared-reborrow','box-raw-receiver']:
 mutant=copy.deepcopy(lowered);f=mutant['translated']['fun_decls'][receipt['specialized_functions'][0]];statements=f['body']['Structured']['body']['statements']
 alias=next(s for s in statements if isinstance(s['kind'],dict) and 'Assign' in s['kind'] and s['kind']['Assign'][0]['kind']=={'Local':9});consumer=next(s for s in statements if isinstance(s['kind'],dict) and 'Assign' in s['kind'] and 'Ref' in s['kind']['Assign'][1])
 if name=='box-extra-use':statements.append(copy.deepcopy(alias))
 elif name=='box-shared-reborrow':consumer['kind']['Assign'][1]['Ref']['kind']='Shared'
 else:
  receiver=alias['kind']['Assign'][1]['Use'][0]['Copy']['kind']['Projection'][0]['kind']['Projection'][0]
  _,inner,kind=receiver['ty']['Untagged']['Ref'];receiver['ty']={'Untagged':{'RawPtr':[inner,kind]}}
 try:box.normalize(mutant)
 except (AssertionError,KeyError,ValueError):negative.append(name)
 else:raise AssertionError('accepted '+name)
rust=ROOT/'.deps/rust-nightly-2026-08-18';r=subprocess.run([str(rust/'bin/rustc'),'--crate-type','lib',str(H/'BorrowedRejected.rs'),'-o',str(H/'Build/borrowed-negative.rlib')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);assert r.returncode!=0 and 'escapes' in r.stdout;negative.append('native-dynamic-lifetime')
subprocess.run(['python3',str(H/'replay_native_push.py')],check=True,timeout=30)
env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env['PATH'],CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(H/'Build/native-push'))
with (H/'native-push.log').open('w') as f:subprocess.run([str(rust/'bin/cargo'),'run','--offline','--locked'],cwd=H/'Native',env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=120)
native=(H/'native-push.log').read_text();assert 'Compared 4368 exact native error/stack/order outcomes' in native
output=H/'Build/diagnostic-final';env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output);modules=['BytesContentV1.Replayed.TypesExternal','BytesContentV1.Replayed.Types','SchemaV1.DiagnosticModel']
with (H/'diagnostic-audit.log').open('w') as f:subprocess.run(['python3',str(H.parent/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=120)
log=(H/'diagnostic-audit.log').read_text();assert 'sorryAx' not in log
for theorem in ['push_kind_all_outcomes','push_bounded','push_two_order','observe_error_push','caller_diagnostics_unobservable']:assert theorem+"' depends on axioms:" in log
caller=ROOT/'.deps/libsignal-v0.106.1/rust/net/src/chat/ws.rs';text=caller.read_text();assert 'MessageProto::decode(data).map_err(ChatProtoDataError::InvalidProtobuf)?' in text;assert 'log::warn!("[{log_tag}] received invalid message: {e}");' in text
files=[H/p for p in ['SourceSnapshots/schema-lib.rs','SourceSnapshots/stamp-lib.rs','DiagnosticModel.lean','check_diagnostics.py','DIAGNOSTICS.md','specialize_push.py','box_reborrow.py','replay_native_push.py','native-push-replay.json','BorrowedRejected.rs','Native/Cargo.toml','Native/Cargo.lock','Native/.cargo/config.toml','Native/src/main.rs','Rust/Cargo.toml','Rust/Cargo.lock','Rust/build.rs','Rust/src/lib.rs','extract.py','extract_stamp.py','extraction.json','stamp-extraction.json']]
failures={}
for name in ['stamp-original.log','stamp-static.log','stamp-candidate.log','stamp-specialized.log','stamp-reborrow.log','stamp-storage.log']:
 lines=(H/name).read_text().splitlines();failures[name]=next((line for line in lines if '[Error' in line or 'Error' in line and 'Info' not in line),'see log')
(H/'diagnostic-audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Executable diagnostic stack model and owned/request-state observation; exact modeled failure/divergence/capacity effects and cursor retained before quotient. Native literal body replay confirms stack mutation/order. Actual static-reference push extraction remains OPEN; no complete actual-source schema/refinement claim.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'original_llbc_sha256':{'minimal':sha(raw),'schema':sha(schema)},'native_caller_sha256':sha(caller),'caller_lines':[1268,1339,1389],'log_contents_excluded_from_observation':True,'negative_guards':negative,'native_comparisons':4368,'kernel_log':log,'objects_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules},'failed_candidate_steps':failures,'unaccepted_transformations':['static_literals.py operand retag alone erased again by Aeneas prepass','StaticLiteralCandidate argument-type restoration exposes static input/local mismatch','Literal push specialization + Box-place normalization advances to static reference Vec storage mismatch','StorageTypeCandidate one-line computed-v_ty fix advances to static receiver/generic Vec.push type mismatch'],'remaining':['Actual static-reference push bridge is trusted/open.','Schema/default/submessage/repeated headers and streaming/compiler composition.']},indent=2)+'\n');print('diagnostic model/native4368/seven negative guards PASS; actual static push bridge OPEN')
