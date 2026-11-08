"""Pin the tiny upstream+producer computed-validity gate."""
from pathlib import Path
import os,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def prepare():
 stage=ROOT/'.deps/tls-websocket-upgrade-native';artifact=stage/'Worker-Public/tls-provider-validity.json'
 with artifact.open('w') as stream:subprocess.run([str(ROOT/'.lake/build/bin/provider_gate_emitter')],stdout=stream,check=True)
 image=json.loads(artifact.read_text());assert image['input_bits']==16 and len(image['outputs'])==8
 (stage/'Programs/Source/tls_provider_gate.mpc').write_text('program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text())
 env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
 for name in ('PYTHONPATH','PYTHONHOME'):env.pop(name,None)
 subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'tls_provider_gate','binary-packed',str(artifact.relative_to(stage))],cwd=stage,env=env,check=True)
 manifest=stage/'provider-gate.manifest';manifest.write_text(build(stage,['tls_binary_tls_provider_validity-sbv:[16x1]-sbv:[8x1]']));return manifest
if __name__=='__main__':print(prepare())
