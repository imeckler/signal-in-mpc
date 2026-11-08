"""Isolated mixed-DH/private service compilation; no deployment or activation."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
from signal_backend.SealedSenderWork.shape import ServiceShape

def compile_profile(shape):
    runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    stage=ROOT/'.deps/private-sealed-relay-native'/('-'.join(map(str,shape.values)))
    stage.mkdir(parents=True,exist_ok=True)
    for name,target in [('Compiler',runtime/'Compiler'),('backend_adapter',ROOT/'backend_adapter'),
        ('handshake_backend',ROOT/'handshake_backend'),('signal_backend',ROOT/'signal_backend')]:
        link=stage/name
        if link.exists():assert link.is_symlink() and link.resolve()==target.resolve()
        else:link.symlink_to(target,target_is_directory=True)
    shutil.copy2(runtime/'compile.py',stage/'compile.py')
    source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
    shutil.copy2(ROOT/'programs/signal_sealed_export.mpc',source/'signal_private_sealed.mpc')
    public=stage/'Worker-Public';public.mkdir(exist_ok=True)
    field=ROOT/'.deps/relay-service-artifacts/x25519-field.json'
    boolean=ROOT/'.deps/relay-service-artifacts'/('service-'+'-'.join(map(str,shape.values))+'.json')
    for name,target in [('x25519-field.json',field),('service.json',boolean)]:
        link=public/name
        if link.exists():assert link.is_symlink() and link.resolve()==target.resolve()
        else:link.symlink_to(target,target_is_directory=True)
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for key in ['PYTHONPATH','PYTHONHOME']:env.pop(key,None)
    subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),
        'signal_private_sealed','Worker-Public/x25519-field.json','Worker-Public/service.json',
        *map(str,shape.values)],cwd=stage,env=env,check=True,timeout=1800)
    manifest=stage/'service.manifest';manifest.write_text(build(stage,[shape.descriptor]))
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    receipt={'shape':shape.values,'input_bytes':shape.input_bytes,'output_bytes':shape.output_bytes,
      'boolean_artifact_sha256':sha(boolean),'field_artifact_sha256':sha(field),
      'manifest_sha256':sha(manifest),'native_mpc_executed':False,
      'no_dh_or_ephemeral_scalar_inputs':True,'trust_boundary':'Unverified mixed-domain conversion/runtime; cryptographic and service assembly use Lean artifacts.'}
    (stage/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(manifest,flush=True)
    return manifest
if __name__=='__main__':compile_profile(ServiceShape(*map(int,sys.argv[1:])))
