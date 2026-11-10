#!/usr/bin/env python3
"""Literal ApplyBlockCtx callback, dispatch slots linked to previously proved actual primitives."""
import hashlib,importlib.util,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 source=ROOT/'.deps/libsignal-vendor/cipher-0.5.2/src/stream/core_api.rs';checks=json.loads((source.parents[2]/'.cargo-checksum.json').read_text());assert sha(source)==checks['files']['src/stream/core_api.rs'];text=source.read_text();region=text.index('StreamCipherClosure for ApplyBlockCtx');start=text.index('    fn call<',region);brace=text.index('{',start);depth=1;end=brace+1
 while depth:depth+=(text[end]=='{')-(text[end]=='}');end+=1
 selected=text[start:end];body=selected[selected.index('{'):];method='    pub fn call(mut self, backend: &mut Backend) '+body
 model='''#![register_tool(charon)]
#![feature(register_tool)]
pub type Block=[u8;16];
pub struct Backend { pub counter:u32, pub nonce:[u32;4], pub keys:[u64;120] }
pub struct InOut<'i,'o> { pub input:&'i Block, pub output:&'o mut Block }
impl Backend {
 #[charon::opaque]
 pub fn gen_ks_block(&mut self,_block:&mut Block) { panic!("actual-source linkage") }
}
impl InOut<'_,'_> {
 #[charon::opaque]
 pub fn xor_in2out(&mut self,_data:&Block) { panic!("actual-source linkage") }
}
pub struct ApplyBlockCtx<'i,'o> { pub block:InOut<'i,'o> }
impl ApplyBlockCtx<'_,'_> {
'''+method+'\n}\n'
 stage=ROOT/'.deps/reference-ctr-apply-block-v1';assert not stage.exists();(stage/'src').mkdir(parents=True);(stage/'Cargo.toml').write_text('[package]\nname="fixed-ctr-apply-block-reference"\nversion="0.1.0"\nedition="2024"\npublish=false\n');(stage/'src/lib.rs').write_text(model)
 art=HERE/'Artifacts';art.mkdir(exist_ok=False);(art/'model.rs').write_text(model);(art/'selected-method.rs').write_text(selected)
 pins=json.loads((REF/'pins.json').read_text());rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-ctr-apply-block-target'))
 llbc=art/'apply.llbc';args=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate','--dest-file='+str(llbc),'--','--lib','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as f:r=subprocess.run(args,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
 report=dict(candidate_only=True,accepted=False,charon_exit=r.returncode,actual_callback_body_text_unchanged=True,selected_fixed_dispatch_content_layout_trusted=True,gen_and_XOR_slots_require_actual_source_DEF_links=True,whole_crypto_result_assumed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source,art/'model.rs',art/'selected-method.rs']},command=args)
 if llbc.exists():
  s=importlib.util.spec_from_file_location('b',REF/'extract.py');b=importlib.util.module_from_spec(s);s.loader.exec_module(b);report.update(b.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (HERE/'extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');assert r.returncode==0 and llbc.exists()and not report['has_errors']and report['counts']['ordered_decls']
 (HERE/'Generated').mkdir();args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/CtrReferenceV1Work/ApplyBlockV1Work/Generated','-split-files','-namespace','ActualApplyBlock16','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=args);(HERE/'extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');print('source ApplyBlockCtx callback',r.returncode)
if __name__=='__main__':main()
