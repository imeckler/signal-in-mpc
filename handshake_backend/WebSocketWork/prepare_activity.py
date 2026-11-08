"""Add one exact public-capacity activity circuit to the isolated WS cache."""
import json,os,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def prepare(capacity):
    assert 0<=capacity<=16385
    stage=ROOT/'.deps/tls-websocket-upgrade-native'
    assert (stage/'Compiler').is_dir(),'prepare the byte machine first'
    name='tls-websocket-activity-'+str(capacity)
    artifact=stage/'Worker-Public'/(name+'.json')
    with artifact.open('w') as stream:
        subprocess.run([str(ROOT/'.lake/build/bin/websocket_activity_emitter'),str(capacity)],stdout=stream,check=True,timeout=900)
    image=json.loads(artifact.read_text());assert image['input_bits']==24 and len(image['outputs'])==8*(capacity+1)
    source='program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text()
    (stage/'Programs/Source/tls_websocket_activity.mpc').write_text(source)
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for n in ('PYTHONPATH','PYTHONHOME'):env.pop(n,None)
    subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),
      'tls_websocket_activity','binary-packed',str(artifact.relative_to(stage))],cwd=stage,env=env,check=True,timeout=900)
    descriptor=f'tls_binary_{name.replace("-","_")}-sbv:[24x1]-sbv:[{8*(capacity+1)}x1]'
    manifest=stage/('activity-'+str(capacity)+'.manifest');manifest.write_text(build(stage,[descriptor]));return manifest
if __name__=='__main__':print(prepare(int(sys.argv[1])))
