"""Public artifact registry; pinned hashes are required before native use."""
from pathlib import Path
import hashlib,json
from functools import lru_cache
from backend_adapter.boolean import load,execute
ROOT=Path(__file__).resolve().parents[2]

def artifact_spec(key):
    kind,*args=key
    if kind=='hash':
        name='signal-keccak-'+'-'.join(map(str,args))
        return ROOT/'.deps/signal-keccak-artifacts'/f'{name}.json',ROOT/'SignalReference/KeccakWork/.lake/build/bin/emit_keccak',['signal-keccak',*map(str,args)]
    if kind=='noise':
        name=f'signal-mlkem-noise-{args[0]}'
        return ROOT/'.deps/signal-mlkem-arithmetic-artifacts'/f'{name}.json',None,None
    if kind in ('ntt','encoding','poly'):
        name=f'signal-mlkem-{kind}-'+'-'.join(map(str,args))
        module={'ntt':'Ntt','encoding':'Encoding','poly':'Poly'}[kind]
        return ROOT/f'.deps/signal-mlkem-{kind}-artifacts'/f'{name}.json',ROOT/f'SignalReference/MlKem{module}Work/.lake/build/bin/emit_mlkem_{kind}',[f'signal-mlkem-{kind}',*map(str,args)]
    if kind=='matrix':
        name='signal-mlkem-matrix-'+'-'.join(map(str,args))
        return ROOT/'.deps/signal-mlkem-sample-artifacts'/f'{name}.json',None,None
    raise ValueError('artifact kind')

class Registry:
    def __init__(self,manifest,zero,one):
        self.manifest=manifest;self.zero=zero;self.one=one
    @lru_cache(maxsize=2)
    def image(self,key):
        path,_,_=artifact_spec(key);entry=self.manifest['artifacts'].get(str(path.relative_to(ROOT)))
        if entry is None or hashlib.sha256(path.read_bytes()).hexdigest()!=entry['sha256']:
            raise ValueError('missing or changed pinned artifact')
        image=load(path)
        if image['input_bits']!=entry['input_bits'] or len(image['outputs'])!=entry['output_bits']:
            raise ValueError('artifact dimensions')
        return image
    def __call__(self,key,bits):return execute(self.image(key),list(bits),self.zero,self.one)
