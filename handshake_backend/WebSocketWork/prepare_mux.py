"""Prepare exact candidate mux/admission/private-ID function closures."""
from pathlib import Path
import json,os,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def prepare():
 stage=ROOT/'.deps/tls-websocket-upgrade-native';env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
 for key in ('PYTHONPATH','PYTHONHOME'):env.pop(key,None)
 plans=[('mux-byte','chat_mux_emitter','byte','tls-chat-mux-byte-4096-4',986,985),('mux-admit','chat_mux_emitter','admit','tls-chat-mux-admit-4',992,982),('request-id-seed','request_id_emitter','seed','tls-private-request-id-seed',8,8),('request-id-next','request_id_emitter','next','tls-private-request-id-next',8,9)]
 result=[]
 for label,emitter,mode,name,ins,outs in plans:
  artifact=stage/'Worker-Public'/(name+'.json')
  with artifact.open('w') as stream:subprocess.run([str(ROOT/'.lake/build/bin'/emitter),mode],stdout=stream,check=True,timeout=900)
  image=json.loads(artifact.read_text());assert image['input_bits']==8*ins and len(image['outputs'])==8*outs
  if mode=='seed':
   source='program.set_security(128)\n'+(ROOT/'programs/tls_private_request_id.mpc').read_text()
   program='tls_private_request_id_init';arguments=[str(artifact.relative_to(stage))]
   descriptor='tls_binary_tls_private_request_id_init-sbv:[128x1]-sbv:[64x1]'
  else:
   source='program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text()
   program='tls_'+label.replace('-','_');arguments=['binary-packed',str(artifact.relative_to(stage))]
   descriptor=f'tls_binary_{name.replace("-","_")}-sbv:[{8*ins}x1]-sbv:[{8*outs}x1]'
  (stage/'Programs/Source'/(program+'.mpc')).write_text(source)
  subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),program,*arguments],cwd=stage,env=env,check=True,timeout=900)
  public=[]
  if label=='mux-byte':
   initial=stage/'Worker-Public/chat-mux-initial.bin';initial.write_bytes(bytes(image['initial_state']));assert initial.stat().st_size==982
   public=[str(initial.relative_to(stage))]
  manifest=stage/(label+'.manifest');manifest.write_text(build(stage,[descriptor],public));result.append(manifest)
 return result
if __name__=='__main__':print(*prepare(),sep='\n')
