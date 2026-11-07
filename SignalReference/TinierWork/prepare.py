#!/usr/bin/env python3
"""Prepare isolated Tinier128 benchmark source; no build, network, or production change."""
import hashlib,json,shutil
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
SOURCE=ROOT/'.deps/MP-SPDZ';DEST=ROOT/'.deps/signal-tinier128/MP-SPDZ'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    if DEST.exists():raise SystemExit(f'Refusing to overwrite existing candidate: {DEST}')
    def ignore(directory,names):
        relative=Path(directory).relative_to(SOURCE)
        omitted={n for n in names if n in {'.git','__pycache__','Player-Data','Persistence','Memory','Logs'}}
        if not relative.parts:omitted.update({'Programs','libSPDZ.so','libSPDZ.a','libFHE.so','librelease.a','static'})
        # Retain external OT libraries, but never reuse MP-SPDZ objects compiled
        # with the short MAC-key type. All MP-SPDZ sources rebuild consistently.
        if not relative.parts or relative.parts[0] not in {'local','deps'}:
            omitted.update(n for n in names if n.endswith(('.o','.d','.x')))
        return omitted
    shutil.copytree(SOURCE,DEST,ignore=ignore)
    config=DEST/'CONFIG.mine';base=config.read_text() if config.exists() else ''
    config.write_text(base+'\n# Isolated benchmark: 128-bit binary MACs, consistent in every translation unit.\nMY_CFLAGS += -DLONG_BIT_MAC_KEY -DDEFAULT_SECURITY=128\n')
    for name in ['Source','Bytecode','Schedules','Public-Input']:(DEST/'Programs'/name).mkdir(parents=True,exist_ok=True)
    (DEST/'Player-Data').mkdir(exist_ok=True)
    suffixes={'.cpp','.h','.hpp','.py'}
    sources={str(p.relative_to(SOURCE)):digest(p) for p in sorted(SOURCE.rglob('*')) if p.is_file() and p.suffix in suffixes and p.relative_to(SOURCE).parts[0] not in {'deps','local','Programs'} and (DEST/p.relative_to(SOURCE)).exists()}
    assert all(digest(DEST/n)==sha for n,sha in sources.items())
    report={'candidate_only':True,'built':False,'production_backend_changed':False,'source_root':str(SOURCE.relative_to(ROOT)),'destination':str(DEST.relative_to(ROOT)),'source_sha256':sources,'config_original_sha256':digest(SOURCE/'CONFIG.mine'),'config_candidate_sha256':digest(config),'prepare_script_sha256':digest(Path(__file__)),'build_command':'make -j2 tinier-party.x','runtime_requirements':['-N 5','-S 128','live preprocessing','same frozen bytecode and public fixtures as CCD baseline'],'security_boundary':'Tinier malicious dishonest-majority candidate, no mobile refresh or mixed StrongShamir conversion claim. LONG_BIT_MAC_KEY chooses gf2n_long for binary MACs. Runtime -S128 is mandatory. No speedup or correctness execution claim before native validation.'}
    (HERE/'preparation.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
