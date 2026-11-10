#!/usr/bin/env python3
"""Source parallel4 CTR generator, with actual counter/AES links and fixed library content."""
import hashlib,importlib.util,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 old=REF/'CtrReferenceV1Work/FixedGeneratorV1Work';receipt=json.loads((old/'proof-report.json').read_text());assert receipt['passed']
 for n,w in receipt['source_sha256'].items():assert sha(ROOT/n)==w,n
 source=ROOT/'.deps/libsignal-vendor/ctr-0.10.1/src/ctr_core.rs';checks=json.loads((source.parents[1]/'.cargo-checksum.json').read_text());assert sha(source)==checks['files']['src/ctr_core.rs'];text=source.read_text();start=text.index('    fn gen_par_ks_blocks(');brace=text.index('{',start);depth=1;end=brace+1
 while depth:depth+=(text[end]=='{')-(text[end]=='}');end+=1
 selected=text[start:end];method=selected.replace('fn gen_par_ks_blocks','pub fn gen_par_ks_blocks',1).replace('ParBlocks<Self>','BatchBlocks').replace('ParBlocks::<Self>','BatchBlocks').replace('F::next_block','next_block').replace('((&tmp, blocks).into())','(make_inout((&tmp, blocks)))')
 prefix=(old/'ArtifactsDirect/model.rs').read_text();model=prefix+"\nimpl CtrBackend<'_,'_> {\n"+method+'\n}\n';stage=ROOT/'.deps/reference-ctr-parallel-generator-v1';assert not stage.exists();(stage/'src').mkdir(parents=True);(stage/'Cargo.toml').write_text('[package]\nname="fixed-ctr-parallel-generator-reference"\nversion="0.1.0"\nedition="2024"\npublish=false\n');(stage/'src/lib.rs').write_text(model)
 art=HERE/'Artifacts';art.mkdir(exist_ok=False);(art/'model.rs').write_text(model);(art/'selected-method.rs').write_text(selected)
 pins=json.loads((REF/'pins.json').read_text());rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-ctr-parallel-generator-target'))
 llbc=art/'parallel.llbc';args=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate','--opaque=crate::aes256_encrypt','--opaque=crate::next_block','--dest-file='+str(llbc),'--','--lib','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as f:r=subprocess.run(args,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
 report=dict(candidate_only=True,accepted=False,charon_exit=r.returncode,actual_parallel_loop_and_counter_AES_calls_retained=True,fixed_array_iterator_InOut_content_dispatch_trusted=True,whole_crypto_result_assumed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source,old/'proof-report.json',old/'ArtifactsDirect/model.rs',art/'model.rs',art/'selected-method.rs']},command=args)
 if llbc.exists():
  s=importlib.util.spec_from_file_location('b',REF/'extract.py');b=importlib.util.module_from_spec(s);s.loader.exec_module(b);report.update(b.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (HERE/'extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');assert r.returncode==0 and llbc.exists()and not report['has_errors']and report['counts']['ordered_decls']
 (HERE/'Generated').mkdir();args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/CtrReferenceV1Work/ParallelGeneratorV1Work/Generated','-split-files','-namespace','ActualParallelCtr4','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=args);(HERE/'extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');print('source parallel4 CTR generator',r.returncode)
if __name__=='__main__':main()
