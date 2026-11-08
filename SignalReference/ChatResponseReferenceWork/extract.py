#!/usr/bin/env python3
"""Pinned source extraction; explicit primitive and precise-drop boundaries."""
from pathlib import Path
import hashlib,importlib.util,json,os,subprocess,sys
H=Path(__file__).resolve().parent;REF=H.parent;ROOT=REF.parent
spec=importlib.util.spec_from_file_location('canonical_extract',REF/'extract.py');canonical=importlib.util.module_from_spec(spec);spec.loader.exec_module(canonical)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=canonical.check_sources();pins=canonical.PINS;rust=ROOT/'.deps/rust-nightly-2026-08-18'
charon=(REF/pins['charon']['directory']/'target/release/charon').resolve()
profile=sys.argv[1] if len(sys.argv)>1 else 'dispatch'
profiles=['dispatch','string','uint64','status','status_mono','string_precise','utf8','metadata_positive','metadata_negative','string_drop','validation']
assert profile in profiles
versions={'charon':subprocess.check_output([str(charon),'version'],text=True).strip(),'rustc':subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()}
assert pins['charon']['commit'] in versions['charon'] and pins['charon']['rustc_version']==versions['rustc']
verified=0
for package in ['prost-0.14.4','bytes-1.12.0','http-1.4.2']:
 vendor=ROOT/'.deps/libsignal-vendor'/package
 for name,digest in json.loads((vendor/'.cargo-checksum.json').read_text())['files'].items():assert sha(vendor/name)==digest;verified+=1
primitive=profile in ('uint64','string','string_precise','string_drop')
env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/chat-response-charon-target'/profile),RUSTFLAGS='')
dest=H/'Artifacts'/profile;dest.mkdir(parents=True,exist_ok=True);llbc=dest/'chat.llbc';(dest/'inventory.json').unlink(missing_ok=True)
if profile=='validation':
 selected=['--start-from=crate::validation_replay::validate_decoded','--include=crate::chat_websocket::web_socket_message::Type','--include=crate::chat_websocket::web_socket_message::*::try_from']
elif profile=='dispatch':
 selected=['--start-from=crate::merge_envelope','--start-from=crate::merge_response','--include=crate::chat_websocket::*::merge_field','--include=prost::error::DecodeError','--include=prost::error::Inner','--include=prost::error::*::from','--include=prost::error::*::push','--opaque=crate::chat_websocket::*::merge_field::*::call_once']
elif profile=='string_drop':
 selected=['--start-from={core::ops::drop::Drop for crate::encoding::string::merge::DropGuard}::drop']
elif profile in ('status','status_mono'):
 selected=['--start-from=crate::checked_status','--include=http::status::*::from_u16','--include=http::status::*::as_u16','--include=http::status::*::is_success','--include=http::status::*::new','--include=http::status::StatusCode','--include=http::status::InvalidStatusCode']
elif profile=='utf8':
 selected=['--start-from=core::str::validations::run_utf8_validation','--opaque=core::str::converts::from_utf8','--include=core::str::validations','--include=core::str::error::Utf8Error']
elif profile.startswith('metadata_'):
 roots=['slice_metadata_positive'] if profile=='metadata_positive' else ['slice_metadata_negative_u16','slice_metadata_negative_raw']
 selected=['--start-from=crate::'+n for n in roots]
 if profile=='metadata_negative':selected+=['--include=core::ptr::const_ptr::*::len']
else:
 target='uint64' if profile=='uint64' else 'string'
 selected=['--start-from=crate::encoding::'+target+'::merge','--opaque=crate::encoding::varint::decode_varint']
if profile in ('utf8','metadata_positive','metadata_negative'):
 selected+=['--start-from=crate::reference_length_seed','--opaque=crate::slice_metadata_len']
if profile=='status_mono':selected+=['--monomorphize']
if profile=='string_precise':selected+=['--precise-drops','--desugar-drops']
subprocess.run([str(rust/'bin/cargo'),'clean','--package',('prost@0.14.4' if primitive else 'chat-response-reference'),'--target','aarch64-apple-darwin'],cwd=H/'Rust',env=env,check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=60)
command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings',*selected,'--dest-file='+str(llbc),'--',*(['--package','prost@0.14.4'] if primitive else []),'--lib','--locked','--offline']
llbc.unlink(missing_ok=True)
with (dest/'charon.log').open('w') as log:r=subprocess.run(command,cwd=H/'Rust',env=env,stdout=log,stderr=subprocess.STDOUT,timeout=240)
files=[H/'extract.py',H/'Rust/Cargo.toml',H/'Rust/Cargo.lock',H/'Rust/build.rs',H/'Rust/src/lib.rs',H/'Rust/src/validation_replay.rs',H/'replay_validation.py',source/'rust/net/build.rs',source/'rust/net/src/proto/chat_websocket.proto',source/'rust/net/src/chat.rs',source/'rust/net/src/chat/ws.rs']
generated=list(Path(env['CARGO_TARGET_DIR']).rglob('signal.proto.chat_websocket.rs'))
if generated:assert len({sha(p) for p in generated})==1
report={'tool_versions':versions,'verified_vendor_files':verified,'generated_rust_sha256':{str(p.relative_to(ROOT)):sha(p) for p in generated},'candidate_only':True,'profile':profile,'charon_exit_code':r.returncode,'source_patches':[],'llbc_preprocessing':False,'actual_net_bytes_generator_options':True,'private_validator_api_called':False,'command':command,'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files if p.exists()}}
if llbc.exists():report.update(canonical.inventory(llbc))
else:report['missing_llbc']=True
(dest/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k in ('profile','charon_exit_code','counts','has_errors','missing_llbc')}));sys.exit(r.returncode if r.returncode else int(not llbc.exists()))
