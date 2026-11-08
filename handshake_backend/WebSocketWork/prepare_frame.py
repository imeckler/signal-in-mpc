"""Compile one bounded private server-frame profile in the isolated WS cache."""
import json,os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def prepare(capacity):
    assert 0<=capacity<=65535
    stage=ROOT/'.deps/tls-websocket-upgrade-native';assert (stage/'Compiler').is_dir()
    name='tls-websocket-frame-'+str(capacity);artifact=stage/'Worker-Public'/(name+'.json')
    with artifact.open('w') as stream:
        subprocess.run([str(ROOT/'.lake/build/bin/websocket_frame_emitter'),str(capacity)],stdout=stream,check=True,timeout=900)
    image=json.loads(artifact.read_text());assert image['input_bits']==224 and len(image['outputs'])==264
    initial=stage/'Worker-Public'/(name+'-initial.bin');initial.write_bytes(bytes(image['initial_state']));assert initial.stat().st_size==26
    (stage/'Programs/Source/tls_websocket_frame.mpc').write_text('program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text())
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for n in ('PYTHONPATH','PYTHONHOME'):env.pop(n,None)
    subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),
      'tls_websocket_frame','binary-packed',str(artifact.relative_to(stage))],cwd=stage,env=env,check=True,timeout=900)
    descriptor=f'tls_binary_{name.replace("-","_")}-sbv:[224x1]-sbv:[264x1]'
    manifest=stage/('frame-'+str(capacity)+'.manifest');manifest.write_text(build(stage,[descriptor],[str(initial.relative_to(stage))]));return manifest
if __name__=='__main__':print(prepare(int(sys.argv[1])))
