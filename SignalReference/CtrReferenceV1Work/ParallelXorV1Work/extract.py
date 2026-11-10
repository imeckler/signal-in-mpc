#!/usr/bin/env python3
"""Actual fixed-block XOR loop, scoped pointer-read/write content dispatch only."""
import hashlib,importlib.util,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 source=ROOT/'.deps/libsignal-vendor/inout-0.2.2/src/inout.rs';checks=json.loads((source.parents[1]/'.cargo-checksum.json').read_text());assert sha(source)==checks['files']['src/inout.rs'];text=source.read_text();start=text.index('    pub fn xor_in2out(&mut self, data: &Array<Array<u8, N>, M>)');brace=text.index('{',start);depth=1;end=brace+1
 while depth:depth+=(text[end]=='{')-(text[end]=='}');end+=1
 selected=text[start:end]
 method=selected.replace('&Array<Array<u8, N>, M>','&Batch').replace('ptr::read(self.in_ptr)','*self.input').replace('Array::<Array<u8, N>, M>::default()','Batch::default()').replace('N::USIZE','16').replace('M::USIZE','4').replace('ptr::write(self.out_ptr, temp);','*self.output = temp;')
 assert 'temp[i][j] = input[i][j] ^ data[i][j];' in selected and 'temp[i][j] = input[i][j] ^ data[i][j];' in method
 model="pub type Batch=[[u8;16];4];\npub struct InOut<'i,'o> { pub input:&'i Batch, pub output:&'o mut Batch }\nimpl InOut<'_,'_> {\n"+method+'\n}\n'
 stage=ROOT/'.deps/reference-parallel-xor-content-v1';assert not stage.exists();(stage/'src').mkdir(parents=True);(stage/'Cargo.toml').write_text('[package]\nname="fixed-parallel-xor-content-reference"\nversion="0.1.0"\nedition="2024"\npublish=false\n');(stage/'src/lib.rs').write_text(model)
 art=HERE/'Artifacts';art.mkdir(exist_ok=False);(art/'model.rs').write_text(model);(art/'selected-method.rs').write_text(selected)
 pins=json.loads((REF/'pins.json').read_text());rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-parallel-xor-content-target'))
 llbc=art/'xor.llbc';args=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate','--dest-file='+str(llbc),'--','--lib','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as f:r=subprocess.run(args,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
 report=dict(candidate_only=True,accepted=False,charon_exit=r.returncode,fixed_pointer_input_read_output_write_content_boundary_trusted=True,actual_range_loop_and_XOR_statement_preserved=True,whole_xor_or_cipher_result_assumed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source,art/'model.rs',art/'selected-method.rs']},command=args)
 if llbc.exists():
  s=importlib.util.spec_from_file_location('b',REF/'extract.py');b=importlib.util.module_from_spec(s);s.loader.exec_module(b);report.update(b.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (HERE/'extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');assert r.returncode==0 and llbc.exists()and not report['has_errors']and report['counts']['ordered_decls']
 (HERE/'Generated').mkdir();args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/CtrReferenceV1Work/ParallelXorV1Work/Generated','-split-files','-namespace','ActualParallelXor4','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=args);(HERE/'extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');print('source fixed XOR loop',r.returncode)
if __name__=='__main__':main()
