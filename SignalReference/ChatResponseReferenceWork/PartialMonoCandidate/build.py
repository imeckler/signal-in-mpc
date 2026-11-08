#!/usr/bin/env python3
"""Build a fail-closed candidate for unsupported borrowed generic trait methods.
No canonical source or type checker is changed. Actual specialization support
would require coordinated trait-method + implementation cloning.
"""
from pathlib import Path
import shutil,hashlib,subprocess,os,json,difflib
H=Path(__file__).resolve().parent;ROOT=H.parents[2]
base=ROOT/'.deps/charon-4ad295c1bf982b5533ce7d85f4ddc889ff3127f8/charon';src=H/'Source/charon';src.parent.mkdir(exist_ok=True)
if not src.exists():shutil.copytree(base,src,ignore=shutil.ignore_patterns('target','.git'))
relative=Path('src/transform/normalize/partial_monomorphization.rs');old=(base/relative).read_text()
needle='''    fn exit_fn_ptr(&mut self, x: &mut FnPtr) {'''
assert old.count(needle)==1
insert='''    fn enter_fn_ptr(&mut self, x: &mut FnPtr) {
        // Generic trait methods cannot be specialized by this pass yet (see
        // exit_fn_ptr). Specializing their supplied nested trait dictionaries
        // without also cloning the method/implementations produces mismatched
        // clauses. Reject the unsupported case before claiming usable LLBC.
        if matches!(*x.kind, FnPtrKind::Trait(..))
            && x.generics.types.iter().any(|ty| self.is_infected(ty))
        {
            register_error!(
                self.ctx,
                self.span,
                "partial monomorphization of generic trait methods with mutable-borrow arguments is unsupported; method and implementation specialization is required"
            );
        }
    }
'''
new=old.replace(needle,insert+needle);(src/relative).write_text(new)
shutil.copy2(base/'src/transform/normalize/normalize_trait_refs.rs',src/'src/transform/normalize/normalize_trait_refs.rs')
shutil.copy2(base/'src/transform/normalize/skip_trait_refs_when_known.rs',src/'src/transform/normalize/skip_trait_refs_when_known.rs')
subprocess.run(['python3',str(H/'closed_adapter_patch.py'),str(src)],check=True)
new=(src/relative).read_text()
(H/'fail-closed.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='pinned/'+str(relative),tofile='candidate/'+str(relative))))
rust=ROOT/'.deps/rust-nightly-2026-08-18';env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env['PATH'],RUSTC=str(rust/'bin/rustc'),CARGO_TARGET_DIR=str(H/'Build/tool'),DYLD_LIBRARY_PATH=str(rust/'lib'),LD_LIBRARY_PATH=str(rust/'lib'))
cmd=[str(rust/'bin/cargo'),'build','--release','--offline','--locked','--bin','charon','--bin','charon-driver']
with (H/'build.log').open('w') as f:p=subprocess.run(cmd,cwd=src,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=900)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'candidate_only':True,'full_specialization_fix':False,'scope':'Selected closed Self/adapter dictionary specialization with binder-aware actual impl resolution; abstract/mixed callers fail closed. Canonical tool, all type checkers and borrow regions preserved.','exit_code':p.returncode,'source_path':str(base.relative_to(ROOT)),'pinned_source_sha256':sha(base/relative),'candidate_source_sha256':sha(src/relative),'script_sha256':sha(Path(__file__)),'patch_script_sha256':sha(H/'closed_adapter_patch.py'),'modified_sources':{str(q):{'pinned':sha(base/q),'candidate':sha(src/q)} for q in [relative,Path('src/transform/normalize/skip_trait_refs_when_known.rs'),Path('src/transform/normalize/normalize_trait_refs.rs')]},'command':cmd}
if p.returncode==0:report['binaries']={str((H/'Build/tool/release'/name).relative_to(ROOT)):sha(H/'Build/tool/release'/name) for name in ['charon','charon-driver']}
(H/'build-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report));raise SystemExit(p.returncode)
