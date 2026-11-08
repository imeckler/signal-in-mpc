from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent;SOURCE=ROOT/'.deps/tls-backend-diagnostic-programs'
def main():
 receipts={}
 for backend in ['ccd','bmr']:
  stage=ROOT/f'.deps/tls-{backend}128-pure-and'
  if stage.exists():raise SystemExit('preserve existing pure-AND closure')
  stage.mkdir()
  shutil.copytree(SOURCE/'Compiler',stage/'Compiler',ignore=shutil.ignore_patterns('__pycache__','*.pyc'));shutil.copy2(SOURCE/'compile.py',stage/'compile.py')
  for name in ['Programs/Source','Programs/Bytecode','Programs/Schedules','Player-Data']:(stage/name).mkdir(parents=True,exist_ok=True)
  shutil.copy2(WORK/'pure_and.mpc',stage/'Programs/Source/pure_and.mpc')
  command=[sys.executable,'-B','compile.py','-M','-B','64']+(['-G']if backend=='bmr'else[])+['pure_and']
  env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0');env.pop('PYTHONPATH',None);env.pop('PYTHONHOME',None)
  subprocess.run(command,cwd=stage,env=env,check=True,timeout=120)
  hashes={str(p.relative_to(stage)):hashlib.sha256(p.read_bytes()).hexdigest() for p in stage.rglob('*')if p.is_file()}
  receipts[backend]={'command':command,'source_product_sha256':hashes,'native_executed':False}
 (WORK/'pure-and-compile.json').write_text(json.dumps(receipts,indent=2)+'\n')
if __name__=='__main__':main()
