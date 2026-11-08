import sys,subprocess,importlib.util,os
from pathlib import Path
HERE=Path(__file__).resolve().parent;KEY=HERE.parent/'KeyReferenceWork'
sys.path.insert(0,str(KEY));spec=importlib.util.spec_from_file_location('accepted_key_check',KEY/'check.py');key=importlib.util.module_from_spec(spec);spec.loader.exec_module(key)
def env():
 e=key.env();e['LEAN_PATH']=str(HERE/'Build')+os.pathsep+str(HERE.parent/'SkipTranslatorWork/Build')+os.pathsep+e['LEAN_PATH'];return e
if __name__=='__main__':
 for name in ['KeyCircuit','Fixed','Reference','Group','Stack','GroupReference']:
  target=HERE/'Build/SkipPlanWork'/f'{name}.olean';target.parent.mkdir(parents=True,exist_ok=True)
  subprocess.run(['lean','-o',str(target),str(HERE/'Modules/SkipPlanWork'/f'{name}.lean')],cwd=HERE/'Modules',env=env(),check=True)
