"""Compile private control collection and fresh-mask response encoding."""
import json,os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def prepare():
    stage=ROOT/'.deps/tls-websocket-upgrade-native';assert (stage/'Compiler').is_dir()
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for key in ('PYTHONPATH','PYTHONHOME'):env.pop(key,None)
    manifests=[]
    for mode in ('collect','encode'):
        name='tls-websocket-control-'+mode+('-125' if mode=='encode' else '')
        artifact=stage/'Worker-Public'/(name+'.json')
        with artifact.open('w') as stream:
            subprocess.run([str(ROOT/'.lake/build/bin/websocket_control_emitter'),mode],stdout=stream,check=True,timeout=900)
        image=json.loads(artifact.read_text());initial=stage/'Worker-Public/websocket-control-initial.bin'
        if mode=='collect':
            initial.write_bytes(bytes(image['initial_state']));assert initial.stat().st_size==636
            source='program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text()
            program='tls_control_collect';args=['binary-packed',str(artifact.relative_to(stage))]
            descriptor='tls_binary_tls_websocket_control_collect-sbv:[5120x1]-sbv:[5088x1]'
        else:
            source='program.set_security(128)\n'+(ROOT/'programs/tls_websocket_control.mpc').read_text()
            program='tls_control_encode';args=[str(artifact.relative_to(stage))]
            descriptor='tls_binary_tls_websocket_control_encode_125-sbv:[1032x1]-sbv:[1072x1]'
        (stage/'Programs/Source'/(program+'.mpc')).write_text(source)
        subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),program,*args],cwd=stage,env=env,check=True,timeout=900)
        manifest=stage/('control-'+mode+'.manifest');manifest.write_text(build(stage,[descriptor],['Worker-Public/websocket-control-initial.bin'] if mode=='collect' else []));manifests.append(manifest)
    return manifests
if __name__=='__main__':print(*prepare(),sep='\n')
