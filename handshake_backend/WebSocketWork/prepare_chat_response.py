"""Compile a private streaming response/correlation profile, never activate it."""
import json,os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def prepare(capacity):
    assert 0<=capacity<=65535
    stage=ROOT/'.deps/tls-websocket-upgrade-native';assert (stage/'Compiler').is_dir()
    name='tls-chat-response-'+str(capacity);artifact=stage/'Worker-Public'/(name+'.json')
    with artifact.open('w') as stream:
        subprocess.run([str(ROOT/'.lake/build/bin/chat_response_emitter'),str(capacity)],stdout=stream,check=True,timeout=900)
    image=json.loads(artifact.read_text());n=image['state_bytes'];offset=image['expected_offset']
    assert n==932 and offset==891 and image['input_bits']==8*(n+4) and len(image['outputs'])==8*(n+6)
    initial=stage/'Worker-Public'/(name+'-initial.bin')
    initial.write_bytes(n.to_bytes(2,'big')+offset.to_bytes(2,'big')+bytes(image['initial_state']))
    assert initial.stat().st_size==n+4
    (stage/'Programs/Source/tls_chat_response.mpc').write_text('program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text())
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for k in ('PYTHONPATH','PYTHONHOME'):env.pop(k,None)
    subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),
      'tls_chat_response','binary-packed',str(artifact.relative_to(stage))],cwd=stage,env=env,check=True,timeout=900)
    descriptor=f'tls_binary_{name.replace("-","_")}-sbv:[{image["input_bits"]}x1]-sbv:[{8*(n+6)}x1]'
    manifest=stage/('chat-'+str(capacity)+'.manifest');manifest.write_text(build(stage,[descriptor],[str(initial.relative_to(stage))]));return manifest
if __name__=='__main__':print(prepare(int(sys.argv[1])))
