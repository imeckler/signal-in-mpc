#!/usr/bin/env python3
"""Literal ApplyBlockCtx callback, dispatch slots linked to previously proved actual primitives."""
import hashlib,importlib.util,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 source=ROOT/'.deps/libsignal-vendor/cipher-0.5.2/src/stream/core_api.rs';checks=json.loads((source.parents[2]/'.cargo-checksum.json').read_text());assert sha(source)==checks['files']['src/stream/core_api.rs'];text=source.read_text();region=text.index('StreamCipherClosure for ApplyBlocksCtx');start=text.index('    fn call<',region);brace=text.index('{',start);depth=1;end=brace+1
 while depth:depth+=(text[end]=='{')-(text[end]=='}');end+=1
 selected=text[start:end];body=selected[selected.index('{'):]
 body=body.replace('B::ParBlocksSize::USIZE','4').replace('self.blocks.into_chunks::<B::ParBlocksSize>()','self.blocks.into_chunks()').replace('Array::<_, B::ParBlocksSize>::default()','Batch::default()')
 model="""#![register_tool(charon)]
#![feature(register_tool)]
pub type Block=[u8;16];pub type Batch=[Block;4];
pub struct InOut<T> {pub input:T,pub output:T}
impl InOut<Block> {#[charon::opaque] pub fn xor_in2out(&mut self,_data:&Block){panic!("actual source linkage")}}
impl InOut<Batch> {#[charon::opaque] pub fn xor_in2out(&mut self,_data:&Batch){panic!("actual source linkage")}}
pub struct Backend {pub counter:u32,pub nonce:[u32;4],pub keys:[u64;120]}
impl Backend {
 #[charon::opaque] pub fn gen_ks_block(&mut self,_out:&mut Block){panic!("actual source linkage")}
 #[charon::opaque] pub fn gen_par_ks_blocks(&mut self,_out:&mut Batch){panic!("actual source linkage")}
 #[charon::opaque] pub fn gen_tail_blocks(&mut self,_out:&mut[Block]){panic!("actual source linkage")}
}
// TRUSTED coherent prechunked content view; no crypto computation here.
pub struct InOutBuf<'a> {pub chunks:&'a mut[InOut<Batch>],pub tail:&'a mut[InOut<Block>]}
pub struct Tail<'a> {pub elements:&'a mut[InOut<Block>]}
impl<'a> InOutBuf<'a> {
 pub fn into_chunks(self)->(&'a mut[InOut<Batch>],Tail<'a>){(self.chunks,Tail{elements:self.tail})}
}
impl Tail<'_> {
 pub fn len(&self)->usize{self.elements.len()}
 #[charon::opaque]
 pub fn get(&mut self,i:usize)->&mut InOut<Block>{&mut self.elements[i]}
}
// Fixed parallel-size4 eliminates this source branch. Fail closed if reached.
impl<'a> IntoIterator for InOutBuf<'a> {
 type Item=&'a mut InOut<Block>;type IntoIter=core::slice::IterMut<'a,InOut<Block>>;
 fn into_iter(self)->Self::IntoIter{panic!("unreachable fixed-parallel4 branch")}
}
pub struct ApplyBlocksCtx<'a> {pub blocks:InOutBuf<'a>}
impl ApplyBlocksCtx<'_> {
 #[allow(unused_mut)]
 pub fn call(self,backend:&mut Backend) """+body+'\n}\n'
 stage=ROOT/'.deps/reference-ctr-blocks-callback-get-v1';assert not stage.exists();(stage/'src').mkdir(parents=True);(stage/'Cargo.toml').write_text('[package]\nname="fixed-ctr-blocks-callback-reference"\nversion="0.1.0"\nedition="2024"\npublish=false\n');(stage/'src/lib.rs').write_text(model)
 art=HERE/'ArtifactsGet';art.mkdir(exist_ok=False);(art/'model.rs').write_text(model);(art/'selected-method.rs').write_text(selected)
 pins=json.loads((REF/'pins.json').read_text());rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-ctr-blocks-callback-target'))
 llbc=art/'apply.llbc';args=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate','--dest-file='+str(llbc),'--','--lib','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as f:r=subprocess.run(args,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
 report=dict(candidate_only=True,accepted=False,charon_exit=r.returncode,actual_callback_control_and_crypto_statement_bodies_retained=True,prechunked_content_view_and_reborrow_layout_trusted=True,gen_and_XOR_slots_require_actual_source_DEF_links=True,whole_crypto_result_assumed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source,art/'model.rs',art/'selected-method.rs']},command=args)
 if llbc.exists():
  s=importlib.util.spec_from_file_location('b',REF/'extract.py');b=importlib.util.module_from_spec(s);s.loader.exec_module(b);report.update(b.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (HERE/'get-extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');assert r.returncode==0 and llbc.exists()and not report['has_errors']and report['counts']['ordered_decls']
 (HERE/'GeneratedGet').mkdir();args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/CtrReferenceV1Work/BlocksCallbackV1Work/GeneratedGet','-split-files','-namespace','ActualBlocksCallbackGet4','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=args);(HERE/'get-extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');print('source ApplyBlockCtx callback',r.returncode)
if __name__=='__main__':main()
