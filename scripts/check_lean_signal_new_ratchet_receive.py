#!/usr/bin/env python3
"""Public first-message DH-ratchet transactions against X25519, Python HKDF and OpenSSL CBC."""
import argparse,json,random,re,subprocess,sys,hmac
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey
from scripts.check_lean_signal_ratchet_step import digest,hkdf,expected as step_expected
from scripts.check_lean_signal_bounded_receive import expected as bounded_expected,material
from scripts.check_lean_signal_proto_parse import field,scalar
from scripts.check_lean_signal_receive import cbc,mac,sample
from scripts.check_lean_crypto import evaluate_lanes,compile_and_check
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def clamp(x):return bytes([x[0]&248])+x[1:31]+bytes([(x[31]&127)|64])
def expected(raw,count=2,jump=2):
    old=raw[1:137];intermediate,receiving=hkdf(old[:32],raw[201:233])
    inner=raw[:1]+raw[265:297]+receiving+bytes(4)+raw[297:429]+bytes(69*count)+raw[429:]
    opened=bounded_expected(inner,count,jump)
    updated=step_expected(opened[:1]+raw[1:265])
    tail=raw[265:297]+opened[1:]
    return updated[:137]+(tail if updated[0]==255 else bytes(len(tail)))
def fixtures(size=96):
    oldPrivate=clamp(sample('ratchet-old-private',32));newPrivate=clamp(sample('ratchet-new-private',32));peerPrivate=clamp(sample('ratchet-peer-private',32))
    oldkey=X25519PrivateKey.from_private_bytes(oldPrivate);newkey=X25519PrivateKey.from_private_bytes(newPrivate);peer=X25519PrivateKey.from_private_bytes(peerPrivate)
    remote=peer.public_key().public_bytes_raw();receive=oldkey.exchange(peer.public_key());send=newkey.exchange(peer.public_key())
    old=sample('ratchet-root',32)+oldPrivate+oldkey.public_key().public_bytes_raw()+sample('ratchet-sender-chain',32)+(12).to_bytes(4,'big')+(45).to_bytes(4,'big')
    pair=newPrivate+newkey.public_key().public_bytes_raw();pq=sample('ratchet-pq',32);sender=sample('ratchet-sender-id',32);receiver=sample('ratchet-receiver-id',32)
    address=b'\0'+sample('sender',16)+b'\1\1'+sample('receiver',16)+b'\x7f';cases=[]
    def add(label,target=0,present=0,recv=receive,snd=send,key=remote,tamper=None,index=12,padding=None,extra=b''):
        prior=old[:128]+index.to_bytes(4,'big')+old[132:];_,receiving=hkdf(prior[:32],recv);chain=receiving
        for _ in range(min(target,3)):chain=hmac.digest(chain,b'\x02','sha256')
        seed=hmac.digest(chain,b'\x01','sha256');ck,mk,iv=material(seed,pq if present==1 else bytes(32))
        ciphertext=cbc(ck,iv,padding if padding is not None else b'hello'+b'\x0b'*11)
        body=field(1,b'\x05'+key)+scalar(2,target)+field(4,ciphertext)+extra;gap=size-9-len(body)
        if gap<2:return
        body+=field(15,bytes(gap-2));assert len(body)+9==size
        content=b'\x44'+body;wire=content+mac(mk,sender,receiver,content)
        raw=bytes([present])+prior+pair+recv+snd+remote+pq+sender+receiver+address+wire
        if tamper is not None:raw=bytearray(raw);raw[tamper]^=1;raw=bytes(raw)
        cases.append((label,raw,expected(raw)))
    for target in(0,1,2,3,2**32-1):add(f'counter-{target}',target=target)
    for target in(0,1,2):add(f'bad-mac-{target}',target=target,tamper=-1)
    for p in(1,2,255):add(f'presence-{p}',target=2,present=p)
    add('zero-receive',recv=bytes(32));add('zero-send',snd=bytes(32));add('both-zero',recv=bytes(32),snd=bytes(32))
    add('different-remote',key=sample('other-ratchet',32));add('bad-padding',padding=bytes(16));add('duplicate-counter-mismatch',extra=scalar(2,2))
    for idx in(0,1,2,255,256,2**32-1):add(f'previous-index-{idx}',index=idx)
    add('sender-identity-tamper',tamper=329);add('receiver-identity-tamper',tamper=361);add('ratchet-body-tamper',tamper=433)
    return cases

def main():
    cli=argparse.ArgumentParser();cli.add_argument('--compile-backend',action='store_true');args=cli.parse_args()
    work=ROOT/'SignalReference/NewRatchetReceiveWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/NewRatchetReceiveExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/NewRatchetReceiveChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    cases=fixtures();inputs=[raw for _,raw,_ in cases];outputs=[out for _,_,out in cases];command=str(work/'.lake/build/bin/emit_new_ratchet_receive')
    result=subprocess.run([command,'evaluate','2','2'],input=''.join(json.dumps(list(w))+'\n' for w in inputs),text=True,capture_output=True,check=True,timeout=600)
    got=[bytes(json.loads(line)) for line in result.stdout.splitlines()]
    assert got==outputs,[(l,g.hex(),e.hex()) for (l,_,e),g in zip(cases,got) if g!=e]
    directory=ROOT/'.deps/signal-new-ratchet-receive-artifacts';directory.mkdir(exist_ok=True);path=directory/'signal-new-ratchet-receive-2-2-96.json'
    with path.open('w') as out:subprocess.run([command,'signal-new-ratchet-receive','2','2','96'],stdout=out,check=True,timeout=600)
    artifact=load(path);assert evaluate_lanes(artifact,inputs)==outputs
    fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'label':l,'input':w.hex(),'output':e.hex()} for l,w,e in cases],indent=2)+'\n')
    row={'fixture_lanes':len(cases),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(artifact),'all_outputs_match':True,'wire_bytes':96,'capacity':2,'max_jump':2}
    if args.compile_backend:row['mpc_compilations']=[compile_and_check(path,inputs,outputs,batch) for batch in(1,16)]
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.NewRatchetReceive')
    files|={Path(__file__),checks,ROOT/'SignalReference/NewRatchetReceiveExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_signal_ratchet_step.py',ROOT/'scripts/check_lean_signal_bounded_receive.py',ROOT/'scripts/check_lean_signal_proto_receive.py',ROOT/'scripts/check_lean_signal_proto_parse.py',ROOT/'scripts/check_lean_signal_receive.py',ROOT/'scripts/check_lean_crypto.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sorted(files)},'cases':[row],'full_actual_rust_ratchet_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'custom_axioms':[],'remaining_boundaries':['X25519 agreement provenance','fresh shared keypair provenance','receiver chain selection and retention','SPQR state evolution','atomic persistent commit']}
    (ROOT/'benchmarks/results/lean-signal-new-ratchet-receive-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'SignalReference/new-ratchet-receive-axioms.txt').write_text(p.stdout)
    print(json.dumps(row),flush=True)
if __name__=='__main__':main()
