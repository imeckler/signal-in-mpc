from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT));from scripts.pin_tls_worker import build
STAGE=ROOT/'.deps/tls-backend-diagnostic-programs';SOURCE=ROOT/'.deps/tls-websocket-upgrade-native'
def prepare():
 if STAGE.exists():raise SystemExit('preserve existing microprogram closure')
 STAGE.mkdir()
 for directory in ['Compiler','backend_adapter','handshake_backend']:
  shutil.copytree(SOURCE/directory,STAGE/directory,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 for name in ['compile.py'] :shutil.copy2(SOURCE/name,STAGE/name)
 for directory in ['Programs/Source','Programs/Functions','Programs/Bytecode','Programs/Schedules','Player-Data']:(STAGE/directory).mkdir(parents=True,exist_ok=True)
 shutil.copy2(WORK/'diagnostic_mix.mpc',STAGE/'Programs/Source/tls_diagnostic_mix.mpc')
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0');env.pop('PYTHONPATH',None);env.pop('PYTHONHOME',None)
 subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'tls_diagnostic_mix'],cwd=STAGE,env=env,check=True,timeout=600)
 descriptor='tls_diagnostic_mix-sbv:[128x1]-sbv:[320x1]';descriptors=[descriptor,'tls_diagnostic_compare-sbv:[640x1]-sbv:[8x1]'];manifest=build(STAGE,descriptors,[]);(STAGE/'programs.manifest').write_text(manifest)
 files={str(p.relative_to(STAGE)):hashlib.sha256(p.read_bytes()).hexdigest() for p in STAGE.rglob('*') if p.is_file() and p.suffix in ['.py','.mpc']}
 (WORK/'microprogram-compile.json').write_text(json.dumps({'scope':'public compilation only, no native parties','compiler_source_sha256':files,'manifest_sha256':hashlib.sha256(manifest.encode()).hexdigest(),'descriptor':descriptor,'statistical_security':128,'checked_dabits':True,'edabits':False},indent=2)+'\n');print(STAGE)
if __name__=='__main__':prepare()
