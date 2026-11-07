#!/usr/bin/env python3
"""Kernel-check the quarantined actual skip translation; no self-acceptance."""
import importlib.util,json,os,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;PARENT=HERE.parent;ROOT=PARENT.parent.parent;BUILD=HERE/'Build'
sys.path.insert(0,str(PARENT/'KeyReferenceWork'))
spec=importlib.util.spec_from_file_location('key_check',PARENT/'KeyReferenceWork/check.py');key=importlib.util.module_from_spec(spec);spec.loader.exec_module(key)
def env():
    e=key.env();e['LEAN_PATH']=str(BUILD)+os.pathsep+e['LEAN_PATH'];return e

def main():
    e=env()
    modules=[('SkipTranslatorWork.LoopMonotone',HERE/'Modules/SkipTranslatorWork/LoopMonotone.lean',HERE/'Modules')]
    for kind in ('skip','regressions'):
        tree=HERE/'Trees/candidate'
        modules.append((f'SkipTranslatorWork.Generated.{kind}.Types',tree/f'SkipTranslatorWork/Generated/{kind}/Types.lean',tree))
        if kind=='skip':modules.append((f'SkipTranslatorWork.Generated.{kind}.FunsExternal',HERE/f'Modules/SkipTranslatorWork/Generated/{kind}/FunsExternal.lean',HERE/'Modules'))
        modules.append((f'SkipTranslatorWork.Generated.{kind}.Funs',tree/f'SkipTranslatorWork/Generated/{kind}/Funs.lean',tree))
    modules += [(f'SkipTranslatorWork.Replayed.{name}',HERE/f'Modules/SkipTranslatorWork/Replayed/{name}.lean',HERE/'Modules') for name in ['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']]
    modules += [(f'SkipTranslatorWork.{name}',HERE/f'Modules/SkipTranslatorWork/{name}.lean',HERE/'Modules') for name in ['SkipLeaf']]
    for module,source,cwd in modules:
        target=BUILD/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        print('Checking',module,flush=True);subprocess.run(['lean','-o',str(target),str(source)],cwd=cwd,env=e,check=True)
if __name__=='__main__':main()
