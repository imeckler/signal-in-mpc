#!/usr/bin/env python3
import sys,subprocess,importlib.util,os
from pathlib import Path
HERE=Path(__file__).resolve().parent;KEY=HERE.parent/'KeyReferenceWork';REFERENCE=HERE.parent.parent
sys.path.insert(0,str(KEY));spec=importlib.util.spec_from_file_location('accepted_key_check',KEY/'check.py');key=importlib.util.module_from_spec(spec);spec.loader.exec_module(key)
def env():
 e=key.env();e['LEAN_PATH']=str(HERE/'Build')+os.pathsep+e['LEAN_PATH'];return e
if __name__=='__main__':
 modules=[('ProtoParseWork.FieldReferenceWork.Generated.uint32_step.Types',HERE/'Generated/uint32_step/Types.lean',REFERENCE),('ProtoParseWork.FieldReferenceWork.Generated.uint32_step.FunsExternal',HERE/'Modules/ProtoParseWork/FieldReferenceWork/Generated/uint32_step/FunsExternal.lean',HERE/'Modules'),('ProtoParseWork.FieldReferenceWork.Generated.uint32_step.Funs',HERE/'Generated/uint32_step/Funs.lean',REFERENCE)]
 for name in ['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']:
  modules.append(('FieldReferenceWork.Replayed.'+name,HERE/'Modules/FieldReferenceWork/Replayed'/(name+'.lean'),HERE/'Modules'))
 modules.append(('FieldReferenceWork.Uint32Reference',HERE/'Modules/FieldReferenceWork/Uint32Reference.lean',HERE/'Modules'))
 for module,source,cwd in modules:
  target=HERE/'Build'/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  print('Checking',module,flush=True);subprocess.run(['lean','-o',str(target),str(source)],cwd=cwd,env=env(),check=True)
