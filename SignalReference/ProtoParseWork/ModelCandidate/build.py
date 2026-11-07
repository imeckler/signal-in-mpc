#!/usr/bin/env python3
"""Isolated candidate model extension; never modifies accepted Aeneas sources.
The only semantic change maps valid usize slice get_unchecked to checked index.
No decoder Rust/LLBC/generated Lean rewrite is performed.
"""
import difflib,hashlib,json,os,re,shutil,subprocess,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2]
MODEL=ROOT/'.deps/aeneas-2026-08-27/backends/lean';ARCHIVE=ROOT/'SignalReference/ProstEncodingWork/AdvanceWork/TranslatorCandidate/aeneas-5b9dcf33.tar.gz'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert digest(ARCHIVE)=='ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453'
    source=MODEL/'Aeneas/Std/Slice.lean';original=source.read_text()
    with tarfile.open(ARCHIVE) as archive:
        member=next(m for m in archive.getmembers() if m.name.endswith('/backends/lean/Aeneas/Std/Slice.lean'))
        assert archive.extractfile(member).read()==source.read_bytes()
    old='''  -- TODO: we should actually use the `SliceIndexInst.get_unchecked` method
  sorry'''
    new='''  -- Candidate extension: checked indexing agrees with unsafe indexing on
  -- valid indices. No semantics is claimed for Rust's out-of-bounds UB case.
  SliceIndexInst.index i s'''
    assert original.count(old)==1;patched=original.replace(old,new)
    old='''  core.slice.Slice.get_unchecked  (core.slice.index.SliceIndexUsizeSlice T) s i
  ⦃ x => x = s[i] ⦄ := by
  sorry'''
    new='''  core.slice.Slice.get_unchecked  (core.slice.index.SliceIndexUsizeSlice T) s i
  ⦃ x => x = s[i] ⦄ := by
  simpa only [core.slice.Slice.get_unchecked, core.slice.index.SliceIndexUsizeSlice,
    core.slice.index.Usize.index, Slice.getElem_Usize_eq] using (Slice.index_usize_spec s i h)'''
    assert patched.count(old)==1;patched=patched.replace(old,new)
    candidate=HERE/'Aeneas/Std/Slice.lean';candidate.parent.mkdir(parents=True,exist_ok=True);candidate.write_text(patched)
    (HERE/'slice-model.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),patched.splitlines(True),fromfile='official/Aeneas/Std/Slice.lean',tofile='candidate/Aeneas/Std/Slice.lean')))
    modules={str(p.relative_to(MODEL).with_suffix('')).replace('/','.'):p for p in MODEL.rglob('*.lean') if '.lake' not in p.parts}
    deps={m:[v for line in p.read_text().splitlines() if line.startswith('import ') for v in line[7:].split() if v in modules] for m,p in modules.items()}
    affected={'Aeneas.Std.Slice'}
    while True:
        more=affected|{m for m,ds in deps.items() if any(d in affected for d in ds)}
        if more==affected:break
        affected=more
    order=[];seen=set()
    def visit(m):
        if m in seen:return
        seen.add(m)
        for d in deps[m]:visit(d)
        if m in affected:order.append(m)
    for m in sorted(affected):visit(m)
    build=HERE/'Build';shutil.copytree(MODEL/'.lake/build/lib/lean',build,dirs_exist_ok=True);cache=Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
    paths=[build,MODEL/'.lake/build/lib/lean',*[p/'.lake/build/lib/lean' for p in sorted(cache.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]]
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,paths))
    sources={str(p.relative_to(ROOT)):digest(p) for m,p in modules.items() if m in affected}
    for m in order:
        p=candidate if m=='Aeneas.Std.Slice' else modules[m];target=build/(m.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        print('Checking '+m,flush=True)
        subprocess.run(['lean','-o',str(target),str(p)],cwd=HERE if m=='Aeneas.Std.Slice' else MODEL,env=env,check=True)
    report={'candidate_only':True,'accepted_reference':False,'original_source_sha256':digest(source),'candidate_source_sha256':digest(candidate),'diff_sha256':digest(HERE/'slice-model.diff'),'upstream_archive_sha256':digest(ARCHIVE),'script_sha256':digest(Path(__file__)),'rebuilt_modules':order,'source_sha256':sources,'trust_boundary':'For valid usize indices, Rust get_unchecked returns the same slice element as checked index. All actual decoder accesses require a separate bounds proof. Outside that precondition this candidate chooses checked-index failure; no claim about Rust UB.','original_models_modified':False,'translator_or_llbc_modified':False}
    (HERE/'build-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
