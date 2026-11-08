"""Add the public no-pending-response admission profile; controls still admitted."""
import os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def prepare(capacity):
    assert 0<=capacity<=65535
    stage=ROOT/'.deps/tls-websocket-upgrade-native';name='tls-websocket-frame-idle-v2-'+str(capacity)
    artifact=stage/'Worker-Public'/(name+'.json')
    with artifact.open('w') as stream:
        subprocess.run([str(ROOT/'.lake/build/bin/websocket_frame_emitter'),'idle',str(capacity)],stdout=stream,check=True,timeout=900)
    (stage/'Programs/Source/tls_websocket_idle.mpc').write_text('program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text())
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for key in ('PYTHONPATH','PYTHONHOME'):env.pop(key,None)
    subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),
      'tls_websocket_idle','binary-packed',str(artifact.relative_to(stage))],cwd=stage,env=env,check=True,timeout=900)
    manifest=stage/('frame-idle-v2-'+str(capacity)+'.manifest')
    manifest.write_text(build(stage,[f'tls_binary_{name.replace("-","_")}-sbv:[224x1]-sbv:[272x1]']));return manifest
if __name__=='__main__':print(prepare(int(sys.argv[1])))
