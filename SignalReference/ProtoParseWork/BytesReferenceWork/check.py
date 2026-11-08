#!/usr/bin/env python3
import sys,subprocess,importlib.util,os
from pathlib import Path
HERE=Path(__file__).resolve().parent;KEY=HERE.parent/'KeyReferenceWork';REFERENCE=HERE.parent.parent;FIELD=HERE.parent/'FieldReferenceWork'
sys.path.insert(0,str(KEY));spec=importlib.util.spec_from_file_location('accepted_key_check',KEY/'check.py');key=importlib.util.module_from_spec(spec);spec.loader.exec_module(key)
def env():
 e=key.env();e['LEAN_PATH']=str(HERE/'Build')+os.pathsep+e['LEAN_PATH'];return e
if __name__=='__main__':
 modules=[]
 for name in ['TypesExternal','Types','FunsExternal','Funs']:
  source=HERE/'Modules/ProtoParseWork/FieldReferenceWork/Generated/bytes_step'/(name+'.lean') if name.endswith('External') else FIELD/'Generated/bytes_step'/(name+'.lean')
  modules.append(('ProtoParseWork.FieldReferenceWork.Generated.bytes_step.'+name,source,HERE/'Modules' if name.endswith('External') else REFERENCE))
 for name in ['BufModel','SliceReference','SliceBridge','SliceAdapter','SlowReference','StateBridge','WrapperReference','ArtifactBridge','Consumption']:
  modules.append(('BytesReferenceWork.Replayed.'+name,HERE/'Modules/BytesReferenceWork/Replayed'/(name+'.lean'),HERE/'Modules'))
 for name in ['Types','FunsExternal','Funs']:
  source=HERE/'Modules/ProtoParseWork/BytesReferenceWork/Generated/vec_replace_put_body'/(name+'.lean') if name=='FunsExternal' else HERE/'Generated/vec_replace_put_body'/(name+'.lean')
  modules.append(('ProtoParseWork.BytesReferenceWork.Generated.vec_replace_put_body.'+name,source,HERE/'Modules' if name=='FunsExternal' else REFERENCE))
 for name in ['CopyModel','BytesReference','VecReference','VecBridge']:
  modules.append(('BytesReferenceWork.'+name,HERE/'Modules/BytesReferenceWork'/(name+'.lean'),HERE/'Modules'))
 for module,source,cwd in modules:
  target=HERE/'Build'/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  print('Checking',module,flush=True);subprocess.run(['lean','-o',str(target),str(source)],cwd=cwd,env=env(),check=True)
