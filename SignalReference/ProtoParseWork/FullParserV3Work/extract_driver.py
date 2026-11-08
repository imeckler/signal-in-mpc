#!/usr/bin/env python3
"""Extract unchanged pinned Prost parsing primitives using accepted tools.
This records exact boundaries; it never patches source, LLBC or generated Lean.
"""
import argparse,importlib.util,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;REFERENCE=HERE.parent.parent;ROOT=REFERENCE.parent
spec=importlib.util.spec_from_file_location('canonical_extract',REFERENCE/'extract.py');canonical=importlib.util.module_from_spec(spec);spec.loader.exec_module(canonical)
digest=canonical.digest
PROFILES={'driver':'prost::message::Message::merge'}
def main():
    cli=argparse.ArgumentParser(description=__doc__);cli.add_argument('profile',choices=PROFILES);args=cli.parse_args()
    source=canonical.check_sources();pins=canonical.PINS;rust=ROOT/'.deps/rust-nightly-2026-08-18'
    charon=(REFERENCE/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REFERENCE/pins['aeneas']['directory']/'aeneas').resolve()
    versions={'charon':subprocess.check_output([str(charon),'version'],text=True).strip(),'aeneas':subprocess.check_output([str(aeneas),'-version'],text=True).strip(),'rustc':subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()}
    assert pins['charon']['commit'] in versions['charon'] and pins['aeneas']['release'] in versions['aeneas'] and pins['charon']['rustc_version']==versions['rustc']
    vendor=ROOT/'.deps/libsignal-vendor/prost-0.14.4';checksum=vendor/'.cargo-checksum.json';checks=json.loads(checksum.read_text())
    for n,h in checks['files'].items():assert digest(vendor/n)==h,n
    env=os.environ.copy();env.update({'PATH':str(rust/'bin')+os.pathsep+env.get('PATH',''),'CHARON_TOOLCHAIN_IS_IN_PATH':'1','DYLD_LIBRARY_PATH':str(rust/'lib'),'LD_LIBRARY_PATH':str(rust/'lib'),'CARGO_HOME':str(ROOT/'.deps/libsignal-cargo-home'),'CARGO_TARGET_DIR':str(ROOT/'.deps/libsignal-charon-target'),'RUSTFLAGS':''})
    dest=HERE/'Artifacts'/args.profile;dest.mkdir(parents=True,exist_ok=True);llbc=dest/'prost.llbc';llbc.unlink(missing_ok=True)
    command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from='+PROFILES[args.profile],'--include=prost::message::Message::merge','--include=prost::RECURSION_LIMIT','--include=prost::encoding::DecodeContext','--include=prost::encoding::*::clone','--include=prost::encoding::*::default','--opaque=prost::encoding::decode_key','--dest-file='+str(llbc),'--','--package','libsignal-protocol','--lib','--locked','--offline']
    with(dest/'charon.log').open('w') as log:r=subprocess.run(command,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT)
    report={'candidate_only':True,'accepted_reference':False,'source_patches':[],'llbc_preprocessing':False,'profile':args.profile,'versions':versions,'script_sha256':digest(Path(__file__)),'vendor_files_verified':len(checks['files']),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in [source/'Cargo.lock',source/'rust/protocol/src/proto/wire.proto',source/'rust/protocol/src/proto/wire.rs',source/'rust/protocol/build.rs',checksum,*[vendor/n for n in checks['files']]]},'charon_exit_code':r.returncode,'charon_command':[v.replace(str(ROOT),'$WORKSPACE') for v in command]}
    if llbc.exists():report.update(canonical.inventory(llbc))
    (dest/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k in ('profile','charon_exit_code','aeneas_exit_code','counts','has_errors','remaining_external_templates')}))
if __name__=='__main__':main()
