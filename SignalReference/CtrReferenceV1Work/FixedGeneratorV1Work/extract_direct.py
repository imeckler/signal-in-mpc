#!/usr/bin/env python3
"""Literal CTR generator body under selected flavor/AES and fixed InOut library dispatch."""
import hashlib,importlib.util,json,os,pathlib,shutil,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 pins=json.loads((REF/'pins.json').read_text());aes=REF/'AesCtrBlockWork/FixedDispatchV1Work';receipt=json.loads((aes/'proof-report.json').read_text());assert receipt['passed']
 for n,v in receipt['source_sha256'].items():assert sha(ROOT/n)==v
 source=ROOT/'.deps/libsignal-vendor/ctr-0.10.1/src/ctr_core.rs';checks=json.loads((source.parents[1]/'.cargo-checksum.json').read_text());assert sha(source)==checks['files']['src/ctr_core.rs'];text=source.read_text();start=text.index('    fn gen_ks_block(');end=text.index('\n    }',start)+6;selected=text[start:end]
 actual=selected.replace('fn gen_ks_block','pub fn gen_ks_block',1).replace('Block<Self>','Block').replace('F::next_block','next_block').replace('((&tmp, block).into())','(make_inout((&tmp, block)))')
 prefix=(aes/'Model/prefix.rs').read_text()+(aes/'ArtifactsComplete/instantiated-methods.rs').read_text()+'''\npub fn make_inout<'i,'o,T>(pair: (&'i T,&'o mut T)) -> InOut<'i,'o,T> {
 InOut { input:pair.0, output:pair.1 }
}
pub struct Nonce { pub ctr:u32, pub nonce:[u32;4] }
// Opaque selected flavor slot, bound to unchanged translated Ctr32BE<U16>::next_block.
pub fn next_block(_state:&mut Nonce)->Block { panic!("reference linkage slot") }
pub struct CtrBackend<'a,'b> { pub ctr_nonce:&'a mut Nonce, pub backend:&'b Backend<'b> }
'''
 model=prefix+"impl CtrBackend<'_,'_> {\n"+actual+'\n}\n';stage=ROOT/'.deps/reference-ctr-fixed-generator-direct-v1';assert not stage.exists();(stage/'src').mkdir(parents=True);(stage/'Cargo.toml').write_text('[package]\nname="ctr-fixed-generator-content-model"\nversion="0.1.0"\nedition="2024"\npublish=false\n');(stage/'src/lib.rs').write_text(model)
 art=HERE/'ArtifactsDirect';art.mkdir(exist_ok=False);(art/'model.rs').write_text(model);(art/'selected-method.rs').write_text(selected)
 rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-ctr-fixed-generator-target'))
 llbc=art/'generator.llbc';args=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate','--opaque=crate::aes256_encrypt','--opaque=crate::next_block','--dest-file='+str(llbc),'--','--lib','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as f:r=subprocess.run(args,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
 report=dict(candidate_only=True,accepted=False,charon_exit=r.returncode,actual_counter_and_AES_calls_preserved=True,Into_conversion_explicitly_instantiated_as_content_constructor=True,selected_F_next_block_and_Block16_types_explicitly_instantiated=True,dispatch_content_model_trusted=True,crypto_and_counter_slots_not_bound_yet=True,command=args,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source,aes/'proof-report.json',art/'model.rs',art/'selected-method.rs']})
 if llbc.exists():
  s=importlib.util.spec_from_file_location('b',REF/'extract.py');b=importlib.util.module_from_spec(s);s.loader.exec_module(b);report.update(b.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (HERE/'direct-extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');assert r.returncode==0 and llbc.exists()and not report['has_errors']and report['counts']['ordered_decls']
 (HERE/'GeneratedDirect').mkdir();args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/CtrReferenceV1Work/FixedGeneratorV1Work/GeneratedDirect','-split-files','-namespace','FixedCtrGenerator','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=args);(HERE/'direct-extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');print('fixed generator translation',r.returncode)
if __name__=='__main__':main()
