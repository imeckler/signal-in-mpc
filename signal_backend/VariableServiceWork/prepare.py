"""Isolated mixed-DH/private service compilation; no deployment or activation."""
import argparse,hashlib,json,os,re,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
from signal_backend.VariableServiceWork.shape import VariableShape

SHA_PROFILES=('reference','gate-efficient','latency')

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as source:
        for chunk in iter(lambda:source.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()

def lean_source_identity():
    pending=[ROOT/'SignalReference/PrivateConversationWork/Export.lean'];result={}
    while pending:
        path=pending.pop();name=str(path.relative_to(ROOT))
        if name in result:continue
        data=path.read_bytes();result[name]=hashlib.sha256(data).hexdigest()
        for line in data.decode().splitlines():
            if line.startswith('import '):
                for module in line[7:].split():
                    target=ROOT/(module.replace('.','/')+'.lean')
                    if target.is_file():pending.append(target)
    result['lean-toolchain']=sha(ROOT/'lean-toolchain')
    return result

def artifact_profile(path):
    # Lean's JSON serializer sorts keys: sha_profile follows the large graph.
    # This is an early routing check; the compiler validates the complete JSON.
    with path.open('rb') as source:
        prefix=source.read(65536)
        source.seek(max(0,path.stat().st_size-65536))
        boundary=prefix+b'\n'+source.read()
    found=re.search(rb'"sha_profile"\s*:\s*"([^"\n]+)"',boundary)
    return found.group(1).decode('ascii') if found else None

def emit_profile_artifact(shape,profile):
    if profile not in SHA_PROFILES:raise ValueError('unsupported SHA profile')
    folder=ROOT/'.deps/private-hash-artifacts'/('sha-'+profile);folder.mkdir(parents=True,exist_ok=True)
    stem='private-conversation-'+str(shape.certificate)+'-'+str(shape.plaintext)+'-'+('present'if shape.chunk else'none')+'-'+('present'if shape.addresses else'none')
    target=folder/(stem+'.json');receipt=folder/(stem+'.source.json');identity=lean_source_identity()
    if target.exists():
        if not receipt.exists():raise RuntimeError('existing SHA artifact has no immutable source receipt')
        old=json.loads(receipt.read_text())
        if old.get('sha_profile')!=profile or old.get('source_sha256')!=identity or old.get('artifact_sha256')!=sha(target):raise RuntimeError('preserve existing SHA artifact; source or product identity changed')
        return target
    with tempfile.NamedTemporaryFile(dir=folder,suffix='.partial',delete=False) as stream:
        temporary=Path(stream.name)
        try:
            command=['lake','env','lean','--run','SignalReference/PrivateConversationWork/Export.lean',str(shape.certificate),str(shape.plaintext),'present'if shape.chunk else'none','present'if shape.addresses else'none',profile]
            subprocess.run(command,cwd=ROOT,stdout=stream,check=True,timeout=1800)
            stream.flush()
            if lean_source_identity()!=identity or artifact_profile(temporary)!=profile:raise RuntimeError('SHA source/profile changed during export')
            temporary.replace(target)
            receipt.write_text(json.dumps({'sha_profile':profile,'source_sha256':identity,'artifact_sha256':sha(target),'command':command},indent=2)+'\n')
        finally:
            if temporary.exists():temporary.unlink()
    return target

def compile_profile(shape,sha_profile=None):
    runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    if sha_profile is not None and sha_profile not in SHA_PROFILES:raise ValueError('unsupported SHA profile')
    selected=sha_profile or 'reference'
    stage=ROOT/'.deps/private-variable-conversation-native'/('-'.join(map(str,shape.values)))
    if sha_profile is not None:stage=stage/('sha-'+selected)
    if (stage/'service.manifest').exists():raise RuntimeError('preserve existing compiled closure; select a fresh explicit profile')
    if sha_profile is not None:
        if stage.exists():raise RuntimeError('preserve existing explicit SHA candidate, including failed builds')
        stage.mkdir(parents=True)
        shutil.copytree(runtime/'Compiler',stage/'Compiler',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        shutil.copytree(ROOT/'backend_adapter',stage/'backend_adapter',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        (stage/'handshake_backend').mkdir()
        for name in ['binary_io.py','field_dag.py','mixed.py']:shutil.copy2(ROOT/'handshake_backend'/name,stage/'handshake_backend'/name)
        (stage/'signal_backend/VariableServiceWork').mkdir(parents=True)
        shutil.copy2(ROOT/'signal_backend/VariableServiceWork/shape.py',stage/'signal_backend/VariableServiceWork/shape.py')
    else:
        stage.mkdir(parents=True,exist_ok=True)
        for name,target in [('Compiler',runtime/'Compiler'),('backend_adapter',ROOT/'backend_adapter'),
            ('handshake_backend',ROOT/'handshake_backend'),('signal_backend',ROOT/'signal_backend')]:
            link=stage/name
            if link.exists():assert link.is_symlink() and link.resolve()==target.resolve()
            else:link.symlink_to(target,target_is_directory=True)
    shutil.copy2(runtime/'compile.py',stage/'compile.py')
    source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
    shutil.copy2(ROOT/'programs/signal_variable_service.mpc',source/'signal_private_conversation.mpc')
    public=stage/'Worker-Public';public.mkdir(exist_ok=True)
    field=ROOT/'.deps/relay-service-artifacts/x25519-field.json'
    boolean=ROOT/'.deps/private-hash-artifacts'/('private-conversation-'+str(shape.certificate)+'-'+str(shape.plaintext)+'-'+('present' if shape.chunk else 'none')+'-'+('present' if shape.addresses else 'none')+'.json')
    if sha_profile is not None:boolean=emit_profile_artifact(shape,selected)
    actual=artifact_profile(boolean)
    if actual!=selected and not (sha_profile is None and actual is None and selected=='reference'):raise RuntimeError('SHA artifact/profile mismatch')
    for name,target in [('x25519-field.json',field),('service.json',boolean)]:
        link=public/name
        if sha_profile is not None:shutil.copy2(target,link)
        elif link.exists():assert link.is_symlink() and link.resolve()==target.resolve()
        else:link.symlink_to(target,target_is_directory=True)
    env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for key in ['PYTHONPATH','PYTHONHOME']:env.pop(key,None)
    subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),
        'signal_private_conversation','Worker-Public/x25519-field.json','Worker-Public/service.json',
        *map(str,shape.values),selected],cwd=stage,env=env,check=True,timeout=1800)
    products={'sha_profile':selected,'profile_explicit':sha_profile is not None,
      'boolean_artifact_sha256':sha(boolean),'field_artifact_sha256':sha(field)}
    (public/'profile.json').write_text(json.dumps(products,sort_keys=True,separators=(',',':'))+'\n')
    manifest=stage/'service.manifest';manifest.write_text(build(stage,[shape.descriptor],['Worker-Public/profile.json']))
    receipt={'sha_profile':selected,'profile_explicit':sha_profile is not None,'artifact_profile_metadata':actual,'shape':shape.values,'input_bytes':shape.input_bytes,'output_bytes':shape.output_bytes,
      'boolean_artifact_sha256':sha(boolean),'field_artifact_sha256':sha(field),
      'manifest_sha256':sha(manifest),'native_mpc_executed':False,
      'no_dh_or_ephemeral_scalar_inputs':True,'trust_boundary':'Unverified mixed-domain conversion/runtime; cryptographic and service assembly use Lean artifacts.'}
    (stage/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(manifest,flush=True)
    return manifest
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('dimensions',type=int,nargs=4);parser.add_argument('--sha-profile',choices=SHA_PROFILES)
    args=parser.parse_args();compile_profile(VariableShape(*args.dimensions),args.sha_profile)
