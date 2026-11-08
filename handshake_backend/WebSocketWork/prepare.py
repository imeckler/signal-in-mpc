"""Compile only the bounded private HTTP101 byte machine in an isolated cache."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def prepare():
    stage=ROOT/'.deps/tls-websocket-upgrade-native';stage.mkdir(exist_ok=True)
    runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    for name,target in [('Compiler',runtime/'Compiler'),('backend_adapter',ROOT/'backend_adapter'),('handshake_backend',ROOT/'handshake_backend')]:
        link=stage/name
        if link.exists():assert link.is_symlink() and link.resolve()==target.resolve()
        else:link.symlink_to(target,target_is_directory=True)
    shutil.copy2(runtime/'compile.py',stage/'compile.py')
    for folder in ('Source','Bytecode','Functions','Schedules'):(stage/'Programs'/folder).mkdir(parents=True,exist_ok=True)
    source='program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text()
    (stage/'Programs/Source/tls_websocket_export.mpc').write_text(source)
    public=stage/'Worker-Public';public.mkdir(exist_ok=True)
    artifact=public/'tls-websocket-upgrade-byte.json'
    with artifact.open('w') as output:
        subprocess.run([str(ROOT/'.lake/build/bin/websocket_upgrade_emitter')],stdout=output,check=True,timeout=900)
    image=json.loads(artifact.read_text());state=image['state_bytes']
    assert image['input_bits']==8*(state+30) and len(image['outputs'])==8*(state+3)
    initial=public/'websocket-initial-state.bin';initial.write_bytes(bytes(image['initial_state']))
    assert initial.stat().st_size==state
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for name in ('PYTHONHOME','PYTHONPATH'):env.pop(name,None)
    subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),
      'tls_websocket_export','binary-packed',str(artifact.relative_to(stage))],cwd=stage,env=env,check=True,timeout=900)
    descriptor=f'tls_binary_tls_websocket_upgrade_byte-sbv:[{image["input_bits"]}x1]-sbv:[{8*(state+3)}x1]'
    manifest=stage/'upgrade.manifest';manifest.write_text(build(stage,[descriptor],['Worker-Public/websocket-initial-state.bin']))
    receipt={'state_bytes':state,'input_bits':image['input_bits'],'output_bits':8*(state+3),'descriptor':descriptor,
      'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),
      'native_mpc_executed':False}
    (stage/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(manifest,flush=True)
    return manifest
if __name__=='__main__':prepare()
