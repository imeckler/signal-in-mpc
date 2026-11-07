#!/usr/bin/env python3
"""Extract unchanged pinned Prost parsing primitives using accepted tools.
This records exact boundaries; it never patches source, LLBC or generated Lean.
"""
import argparse,importlib.util,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;REFERENCE=HERE.parent.parent;ROOT=REFERENCE.parent
spec=importlib.util.spec_from_file_location('canonical_extract',REFERENCE/'extract.py');canonical=importlib.util.module_from_spec(spec);spec.loader.exec_module(canonical)
digest=canonical.digest
PROFILES={'slice':'crate::encoding::varint::decode_varint_slice','varint':'crate::encoding::varint::decode_varint','key':'crate::encoding::decode_key','skip':'crate::encoding::skip_field'}
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
    subprocess.run([str(rust/'bin/cargo'),'clean','--package','prost@0.14.4','--target','aarch64-apple-darwin'],cwd=source,env=env,check=True,stdout=subprocess.DEVNULL)
    command=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from='+PROFILES[args.profile],'--dest-file='+str(llbc),'--','--package','prost@0.14.4','--lib','--locked','--offline']
    with(dest/'charon.log').open('w') as log:r=subprocess.run(command,cwd=source,env=env,stdout=log,stderr=subprocess.STDOUT)
    report={'candidate_only':True,'accepted_reference':False,'source_patches':[],'llbc_preprocessing':False,'profile':args.profile,'versions':versions,'script_sha256':digest(Path(__file__)),'vendor_files_verified':len(checks['files']),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in [source/'Cargo.lock',checksum,*[vendor/n for n in checks['files']]]},'charon_exit_code':r.returncode,'charon_command':[v.replace(str(ROOT),'$WORKSPACE') for v in command]}
    if llbc.exists():report.update(canonical.inventory(llbc))
    if r.returncode==0 and llbc.exists() and not report['has_errors'] and report['counts']['ordered_decls']:
        generated=HERE/'Generated'/args.profile;generated.mkdir(parents=True,exist_ok=True)
        for p in generated.glob('*.lean'):p.unlink()
        command=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REFERENCE),'-subdir','/ProtoParseWork/KeyReferenceWork/Generated/'+args.profile,'-split-files','-namespace','ProstKeyCandidate','-warnings-as-errors','-no-progress-bar']
        with(dest/'aeneas.log').open('w') as log:a=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        report.update({'aeneas_exit_code':a.returncode,'aeneas_command':[v.replace(str(ROOT),'$WORKSPACE') for v in command],'generated_files':{str(p.relative_to(REFERENCE)):digest(p) for p in generated.glob('*.lean')},'remaining_external_templates':[p.name for p in generated.glob('*_Template.lean')]})
    (dest/'inventory.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k in ('profile','charon_exit_code','aeneas_exit_code','counts','has_errors','remaining_external_templates')}))
if __name__=='__main__':main()
