#!/usr/bin/env python3
"""Source-body-preserving fixed dispatch; explicit trusted library models, no crypto assumption."""
import hashlib,importlib.util,json,os,pathlib,shutil,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 pins=json.loads((REF/'pins.json').read_text());vendor=ROOT/'.deps/libsignal-vendor/aes-0.9.1';checks=json.loads((vendor/'.cargo-checksum.json').read_text());source=vendor/'src/soft.rs';assert sha(source)==checks['files']['src/soft.rs'];original=source.read_text()
 start=original.index('            fn encrypt_block(&self, mut block:');end=original.index('\n        }',start)
 methods=original[start:end];single=methods[:methods.index('\n\n            #[inline(always)]')];parallel=methods[methods.index('            fn encrypt_par_blocks'):]
 assert methods.count('$fixslice_encrypt')==2
 # Only the macro-selected symbol and method visibility are instantiated. All statements remain literal.
 def instantiate(method):return method.replace('$fixslice_encrypt','aes256_encrypt').replace('            fn ','            pub fn ',1)
 body='impl Backend<\'_> {\n'+instantiate(single)+'\n'+instantiate(parallel)+'\n}\n'
 stage=ROOT/'.deps/reference-aes-fixed-dispatch-complete-v1';assert not stage.exists();(stage/'src').mkdir(parents=True)
 shutil.copy2(HERE/'Model/Cargo.toml',stage/'Cargo.toml');(stage/'src/lib.rs').write_text((HERE/'Model/prefix.rs').read_text()+body)
 art=HERE/'ArtifactsComplete';art.mkdir(exist_ok=False);(art/'selected-methods.rs').write_text(methods);(art/'instantiated-methods.rs').write_text(body)
 rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-aes-fixed-dispatch-target'))
 llbc=art/'dispatch.llbc';args=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate','--opaque=crate::aes256_encrypt','--dest-file='+str(llbc),'--','--lib','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as f:r=subprocess.run(args,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
 report=dict(candidate_only=True,accepted=False,charon_exit=r.returncode,actual_wrapper_statement_text_preserved=True,macro_symbol_and_visibility_only_instantiated=True,trusted_model_boundary='fixed hybrid-array content and InOut entry-read/complete-output-owner, explicit AES256 dispatch; no address/Drop/allocator semantics',whole_AES_result_assumed=False,actual_AES_slot_not_bound_yet=True,command=args,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source,HERE/'Model/prefix.rs',HERE/'Model/Cargo.toml',stage/'src/lib.rs',art/'selected-methods.rs',art/'instantiated-methods.rs']})
 if llbc.exists():
  s=importlib.util.spec_from_file_location('b',REF/'extract.py');b=importlib.util.module_from_spec(s);s.loader.exec_module(b);report.update(b.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (HERE/'complete-extraction-report.json').write_text(json.dumps(report,indent=2)+'\n')
 assert r.returncode==0 and llbc.exists()and not report['has_errors']and report['counts']['ordered_decls']
 (HERE/'GeneratedComplete').mkdir();args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/AesCtrBlockWork/FixedDispatchV1Work/GeneratedComplete','-split-files','-namespace','FixedAesDispatch','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=args);(HERE/'complete-extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');print('fixed dispatch translation',r.returncode)
if __name__=='__main__':main()
