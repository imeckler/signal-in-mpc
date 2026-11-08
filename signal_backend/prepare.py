"""Offline compilation of one public Signal profile into a pinned native function.

Outputs stay in an isolated build tree. Callers collectively agree the resulting
exact closure before registering it in a worker; this helper never activates it.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
from signal_backend.shape import SendShape

P=str(2**255-19)
def compile_profile(artifact:Path,shape:SendShape)->Path:
    backend=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    stage=ROOT/'.deps/signal-established-native'/shape.stem
    stage.mkdir(parents=True,exist_ok=True)
    for name,target in [('Compiler',backend/'Compiler'),('backend_adapter',ROOT/'backend_adapter'),
                        ('handshake_backend',ROOT/'handshake_backend'),('signal_backend',ROOT/'signal_backend')]:
        link=stage/name
        if link.exists():
            if not link.is_symlink() or link.resolve()!=target.resolve():raise ValueError('build path collision')
        else:link.symlink_to(target,target_is_directory=True)
    shutil.copy2(backend/'compile.py',stage/'compile.py')
    source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
    shutil.copy2(ROOT/'programs/signal_export.mpc',source/'signal_send_export.mpc')
    public=stage/'Worker-Public';public.mkdir(exist_ok=True)
    target=public/(shape.stem+'.json')
    if target.exists():
        if not target.is_symlink() or target.resolve()!=artifact.resolve():raise ValueError('artifact path collision')
    else:target.symlink_to(artifact.resolve())
    environment=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
    for key in ['PYTHONPATH','PYTHONHOME']:environment.pop(key,None)
    subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',P,'signal_send_export',
                    'Worker-Public/'+target.name],cwd=stage,env=environment,check=True,timeout=900)
    manifest=stage/'signal-send.manifest'
    manifest.write_text(build(stage,[shape.descriptor]))
    # Result is only a compiler receipt; private execution/erasure are separate.
    return manifest
