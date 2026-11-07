#!/usr/bin/env python3
"""Pinned-source audit and independent Python-HMAC numeric-artifact fixtures."""
from datetime import datetime, timezone
import hashlib
import hmac
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import tarfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def expected(mode,jump,capacity,raw):
    auth=raw[0] if mode=='committed' else 255
    data=raw[1:] if mode=='committed' else raw
    key,chain=data[:32],data[32:64]
    current,target=int.from_bytes(data[64:68],'big'),int.from_bytes(data[68:72],'big')
    store=data[72:]
    if auth!=255 or not current<=target<=current+jump or target==2**32-1:
        return bytes(33)+chain+data[64:68]+store
    for index in range(current,target+1):
        seed=hmac.digest(chain,b'\x01','sha256')
        chain=hmac.digest(chain,b'\x02','sha256')
        if index<target:
            store=(b'\xff'+key+index.to_bytes(4,'big')+seed+store)[:69*capacity]
    return b'\xff'+seed+chain+(target+1).to_bytes(4,'big')+store


def fixtures(mode,jump,capacity):
    rng=random.Random(0x414456+capacity+jump)
    rows=[]
    def add(label,current,target,auth=255,zero=False):
        key,chain=(bytes(32),bytes(32)) if zero else (rng.randbytes(32),rng.randbytes(32))
        # Include arbitrary invalid masks and holes; state rollback must preserve exact bytes.
        store=b''.join(bytes([rng.choice([0,1,254,255])])+rng.randbytes(68) for _ in range(capacity))
        data=key+chain+current.to_bytes(4,'big')+target.to_bytes(4,'big')+store
        raw=(bytes([auth]) if mode=='committed' else b'')+data
        rows.append((label,raw,expected(mode,jump,capacity,raw)))
    for current in [0,1,254,255,256,65534,65535,65536,2**31-1,2**31,2**32-4,2**32-3,2**32-2,2**32-1]:
        for distance in range(-1,jump+2):
            target=current+distance
            if 0<=target<2**32: add(f'counter{current}-distance{distance}',current,target)
    add('wrapped-target-zero',2**32-1,0)
    add('backward',1000,1)
    add('zero-chain',0,jump,zero=True)
    if mode=='committed':
        for auth in range(256): add(f'auth{auth}',255,255+jump,auth)
    for i in range(12):
        current=rng.randrange(2**32-jump-2)
        add(f'random{i}',current,current+rng.randrange(jump+2))
    return rows


def main():
    pins_path=HERE.parent/'pins.json';pins=json.loads(pins_path.read_text())
    rust=ROOT/'.deps/libsignal-v0.106.1';archive=ROOT/'.deps/libsignal-v0.106.1.tar.gz'
    references=[rust/p for p in ['rust/protocol/src/double_ratchet.rs','rust/protocol/src/ratchet/keys.rs','rust/protocol/src/consts.rs']]
    assert digest(archive)==pins['libsignal']['archive_sha256']
    with tarfile.open(archive) as bundle:
        for path in references:
            assert path.read_bytes()==bundle.extractfile('signalapp-libsignal-904c8dc/'+str(path.relative_to(rust))).read()
    subprocess.run(['lake','-d',str(HERE),'build','emit_receive_advance'],cwd=ROOT,check=True)
    sources={Path(__file__),HERE/'Export.lean',HERE/'Checks.lean',HERE/'lakefile.toml',HERE/'lake-manifest.json',
        HERE/'lean-toolchain',pins_path,archive,*references,ROOT/'backend_adapter/boolean.py',ROOT/'backend_adapter/aig.py',ROOT/'scripts/check_lean_crypto.py'}
    def visit(module):
        if not module.startswith('TlsMpc'):return
        path=ROOT/(module.replace('.','/')+'.lean')
        if path in sources:return
        sources.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)',path.read_text(),re.M):visit(imported)
    visit('TlsMpc.Signal.ReceiveAdvance')
    snapshot={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    checks=subprocess.run(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,capture_output=True,text=True,check=True)
    endpoints=re.findall(r'^#print axioms (\S+)',(HERE/'Checks.lean').read_text(),re.M)
    found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",checks.stdout)
    assert [n for n,_ in found]==endpoints
    allowed={'propext','Classical.choice','Quot.sound'}
    for name,axioms in found: assert not ({a.strip() for a in axioms.split(',') if a.strip()}-allowed),name
    (HERE/'axioms.txt').write_text(checks.stdout)
    directory=HERE/'Artifacts';directory.mkdir(exist_ok=True)
    binary=HERE/'.lake/build/bin/emit_receive_advance'
    results=[];fixture_records=[]
    for jump,capacity in [(0,0),(0,2),(2,2)]:
        for mode in ['advance','committed']:
            path=directory/f'signal-receive-{mode}-{jump}-{capacity}.json'
            with path.open('w') as output:
                subprocess.run([str(binary),mode,str(jump),str(capacity)],cwd=ROOT,stdout=output,check=True,timeout=240)
            image=load(path)
            cases=fixtures(mode,jump,capacity)
            observed=evaluate_lanes(image,[r[1] for r in cases])
            assert observed==[r[2] for r in cases],(mode,jump,capacity,[r[0] for r,got in zip(cases,observed) if got!=r[2]])
            results.append({'mode':mode,'max_jump':jump,'capacity':capacity,'artifact':str(path.relative_to(ROOT)),
                'artifact_sha256':digest(path),'input_bits':image['input_bits'],'output_bits':len(image['outputs']),
                'fixture_lanes':len(cases),'adapter_operations':statistics(image)})
            fixture_records += [{'mode':mode,'max_jump':jump,'capacity':capacity,'label':n,'input':i.hex(),'output':o.hex()} for n,i,o in cases]
            print(f'{mode} jump{jump} capacity{capacity}: {len(cases)} numeric-artifact HMAC fixtures passed',flush=True)
    fixture_path=HERE/'fixture-results.json';fixture_path.write_text(json.dumps(fixture_records,indent=2)+'\n')
    assert snapshot=={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':snapshot,
        'checked_endpoints':len(found),'theorems':endpoints,'allowed_foundational_axioms':sorted(allowed),'custom_axioms':[],
        'axiom_report_sha256':digest(HERE/'axioms.txt'),'native_exporter':str(binary.relative_to(ROOT)),
        'native_exporter_sha256':digest(binary),'artifacts':results,'fixture_report_sha256':digest(fixture_path),
        'numeric_artifact_fixture_count':len(fixture_records),
        'input_layout':'[auth1 for committed] || ratchetPublicKey32 || chainKey32 || currentCounterBE4 || targetCounterBE4 || slots69N',
        'output_layout':'found255/0 || seed32 || nextChain32 || nextCounterBE4 || slots69N',
        'slot_layout':'valid255/0 byte || ratchetPublicKey32 || counterBE4 || seed32; newest first; capacity public',
        'public_boundary':'Mode, maxJump and capacity only; counters, keys, masks, slots, authentication and outputs remain shared.',
        'eligibility':'current<=target<=current+maxJump and target<2^32-1. Never accepts wrapped counters. Next counter must fit u32.',
        'transaction':'Only authentication255 and found255 commit; failure zeroes seed and preserves exact original chain, counter and slots.',
        'rust_reference_commit':pins['libsignal']['commit'],
        'rust_correspondence_review':{
            'consume_message_key':'Forward path caches each intermediate message_keys(), advances chain, stores next chain past target, returns target message_keys().',
            'chain_derivation':'keys.rs ChainKey: HMAC-SHA256(chain,01) message seed; HMAC-SHA256(chain,02) next key; index+1.',
            'differences':['Public bounded maxJump, not full MAX_FORWARD_JUMPS=25000 or unrestricted self-session policy.',
                'Fixed flat seed-only store, not full protobuf receiver chains or MAX_MESSAGE_KEYS=2000 storage.',
                'Target=uint32.max is rejected explicitly; Rust next_chain_key uses index+1.',
                'Authentication-gated commit is an added transaction boundary; no full decrypt or session persistence here.',
                'Backward counters reject here; caller can route them to SkippedKeys lookup.']},
        'actual_rust_wrapper_equivalence':False,'complete_session_or_persistence':False,
        'backend_compiled':False,'native_mpc_executed':False,
        'trust_boundary':'Lean compiler/evaluation, HMAC specification and transaction theorems; native exporter/JSON/adapter unverified and checked by independent public fixtures.'}
    path=HERE/'proof-report.json';path.write_text(json.dumps(report,indent=2)+'\n')
    print('proof-report.json SHA256: '+digest(path),flush=True)


if __name__=='__main__':main()
