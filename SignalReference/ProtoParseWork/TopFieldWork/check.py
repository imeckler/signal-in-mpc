import sys,subprocess,importlib.util,os
from pathlib import Path
HERE=Path(__file__).resolve().parent;PLAN=HERE.parent/'SkipPlanWork'
sys.path.insert(0,str(PLAN));spec=importlib.util.spec_from_file_location('skip_plan_check',PLAN/'check.py');plan=importlib.util.module_from_spec(spec);spec.loader.exec_module(plan)
def env():
 e=plan.env();e['LEAN_PATH']=str(HERE/'Build')+os.pathsep+e['LEAN_PATH'];return e
if __name__=='__main__':
 for name in ['Fields','TopPlan','Table','Scan','DecoderTable']:
  target=HERE/'Build/TopFieldWork'/f'{name}.olean';target.parent.mkdir(parents=True,exist_ok=True)
  subprocess.run(['lean','-o',str(target),str(HERE/'Modules/TopFieldWork'/f'{name}.lean')],cwd=HERE/'Modules',env=env(),check=True)
