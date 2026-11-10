#!/usr/bin/env python3
"""Actual fixed16 ReadBuffer cursor/cache method bodies, no memory/crypto assumptions."""
import hashlib,importlib.util,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 source=ROOT/'.deps/libsignal-vendor/block-buffer-0.12.1/src/read.rs';checks=json.loads((source.parents[1]/'.cargo-checksum.json').read_text());assert sha(source)==checks['files']['src/read.rs'];text=source.read_text();selected={}
 for name in ['write_block','set_pos_unchecked','reset']:
  start=text.index(('    unsafe fn 'if name=='set_pos_unchecked'else'    pub fn 'if name=='reset'else'    pub fn ')+name+'(')if name in ['reset','set_pos_unchecked']else text.index('    pub fn '+name+'(')
  brace=text.index('{',start);depth=1;end=brace+1
  while depth:
   depth+=(text[end]=='{')-(text[end]=='}');end+=1
  selected[name]=text[start:end]
 methods='\n'.join(('    #[charon::opaque]\n'+body if name=='get_pos' else body)for name,body in selected.items()).replace('BS::USIZE','16').replace('BS::U8','16').replace('Array<u8, BS>','[u8;16]')
 model='#![register_tool(charon)]\n#![feature(register_tool)]\npub struct ReadBuffer { pub buffer:[u8;16] }\nimpl ReadBuffer {\n'+methods+'\n}\nstruct ResetGuard<\'a>(&\'a mut ReadBuffer);\nimpl Drop for ResetGuard<\'_> { fn drop(&mut self) { self.0.reset(); } }\n'
 stage=ROOT/'.deps/reference-write-buffer-v1-v1';assert not stage.exists();(stage/'src').mkdir(parents=True);(stage/'Cargo.toml').write_text('[package]\nname="fixed-write-buffer-reference"\nversion="0.1.0"\nedition="2024"\npublish=false\n');(stage/'src/lib.rs').write_text(model)
 art=HERE/'Artifacts';art.mkdir(exist_ok=False);(art/'model.rs').write_text(model);(art/'selected.json').write_text(json.dumps(selected,indent=2)+'\n')
 pins=json.loads((REF/'pins.json').read_text());rust=ROOT/'.deps/rust-nightly-2026-08-18';charon=(REF/pins['charon']['directory']/'target/release/charon').resolve();aeneas=(REF/pins['aeneas']['directory']/'aeneas').resolve();assert subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip()==pins['charon']['rustc_version']
 env=dict(os.environ,PATH=str(rust/'bin')+os.pathsep+os.environ.get('PATH',''),CHARON_TOOLCHAIN_IS_IN_PATH='1',DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'),CARGO_TARGET_DIR=str(ROOT/'.deps/reference-write-buffer-target'))
 llbc=art/'buffer.llbc';args=[str(charon),'cargo','--preset=aeneas','--no-dedup-serialized-ast','--sysroot=default','--error-on-warnings','--start-from=crate','--dest-file='+str(llbc),'--','--lib','--offline','--target','aarch64-apple-darwin']
 with(art/'charon.log').open('w')as f:r=subprocess.run(args,cwd=stage,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=90)
 report=dict(candidate_only=True,accepted=False,charon_exit=r.returncode,statement_bodies_unchanged_except_BS16_constants=True,fixed_hybrid_array_content_binding_trusted=True,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),source,art/'model.rs',art/'selected.json']},command=args)
 if llbc.exists():
  s=importlib.util.spec_from_file_location('b',REF/'extract.py');b=importlib.util.module_from_spec(s);s.loader.exec_module(b);report.update(b.inventory(llbc));report['llbc_sha256']=sha(llbc)
 (HERE/'extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');assert r.returncode==0 and llbc.exists()and not report['has_errors']and report['counts']['ordered_decls']
 (HERE/'Generated').mkdir();args=[str(aeneas),'-backend','lean',str(llbc),'-dest',str(REF),'-subdir','/CtrReferenceV1Work/WriteBufferV1Work/Generated','-split-files','-namespace','ActualWriteBuffer16','-warnings-as-errors','-no-progress-bar']
 with(art/'aeneas.log').open('w')as f:r=subprocess.run(args,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=60)
 report.update(aeneas_exit=r.returncode,aeneas_command=args);(HERE/'extraction-report.json').write_text(json.dumps(report,indent=2)+'\n');print('actual fixed ReadBuffer methods',r.returncode)
if __name__=='__main__':main()
