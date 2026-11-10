"""Produce a Lean circuit in the flat gate format on demand, cached by arguments.

Usage: circuit_cache.py EMITTER_ARG...   (arguments of `hybrid_kdf_emitter`)
Prints one line: PATH SHA256 INPUT_BITS OUTPUT_BITS.

Record and transcript sizes are public but only known at run time, so a worker
asks for the circuit of a given size when it first needs it. The export is
deterministic: both parties run this independently and compare the SHA-256
before use. The lowering is the shared unverified adapter (hybrid_lowering.py).
Concurrent callers are safe: the file is written to a temporary name and
renamed into place.
"""
import fcntl,hashlib,json,os,pathlib,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;CACHE=ROOT/'.deps/emp-hybrid-word-v1/cache'
sys.path.insert(0,str(HERE))
from hybrid_lowering import lower,flat_text
def ensure(args):
    if not args or any(not a or not all(c.isalnum() or c=='-' for c in a) for a in args):raise ValueError('circuit arguments')
    CACHE.mkdir(parents=True,exist_ok=True);path=CACHE/('-'.join(args)+'.flat');meta=path.with_suffix('.json')
    # One producer at a time: the second caller waits and reuses the result.
    lock=open(CACHE/'.lock','w');fcntl.flock(lock,fcntl.LOCK_EX)
    if not (path.exists() and meta.exists()):
        binary=ROOT/'.lake/build/bin/hybrid_kdf_emitter'
        command=[str(binary)] if binary.exists() else ['lake','exe','hybrid_kdf_emitter']
        raw=subprocess.run([*command,*args],cwd=ROOT,check=True,capture_output=True).stdout
        image=json.loads(raw);n,gates,outputs=lower(image);text=flat_text(n,gates,outputs).encode()
        info=dict(arguments=list(args),sha256=hashlib.sha256(text).hexdigest(),input_bits=n,output_bits=len(outputs),and_gates=sum(g[0]=='A' for g in gates),lean_image_sha256=hashlib.sha256(raw).hexdigest())
        writes=[(path,text)]
        if 'input_fields' in image:
            # Worker kernel: the named field layout comes from Lean and is pinned with the circuit.
            fields_out=[(name,rest[0],rest[1]) for name,rest in image['output_fields']]   # Lean encodes the triple as a nested pair
            rows=['EMP_HYBRID_KERNEL_LAYOUT_V1']+['I %s %d'%(name,bits) for name,bits in image['input_fields']]+['O %s %d %d'%(name,bits,int(opened)) for name,bits,opened in fields_out]
            if sum(b for _,b in image['input_fields'])!=n or sum(f[1] for f in fields_out)!=len(outputs) or any(not f[0].isalnum() for f in image['input_fields']+fields_out):raise ValueError('kernel layout')
            layout=('\n'.join(rows)+'\n').encode();info['layout_sha256']=hashlib.sha256(layout).hexdigest();writes.append((path.with_suffix('.layout'),layout))
        for target,data in (*writes,(meta,(json.dumps(info,indent=2)+'\n').encode())):
            fd,temp=tempfile.mkstemp(dir=CACHE,prefix='.tmp-')
            with os.fdopen(fd,'wb') as f:f.write(data)
            os.replace(temp,target)
    info=json.loads(meta.read_text())
    if hashlib.sha256(path.read_bytes()).hexdigest()!=info['sha256']:raise ValueError('cached circuit does not match its record')
    if 'layout_sha256' in info and hashlib.sha256(path.with_suffix('.layout').read_bytes()).hexdigest()!=info['layout_sha256']:raise ValueError('cached layout does not match its record')
    return path,info
if __name__=='__main__':
    path,info=ensure(sys.argv[1:])
    if 'layout_sha256' in info:print(path,info['sha256'],info['input_bits'],info['output_bits'],path.with_suffix('.layout'),info['layout_sha256'])
    else:print(path,info['sha256'],info['input_bits'],info['output_bits'])
