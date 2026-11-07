#!/usr/bin/env python3
"""Audit fixed-capacity secret skipped-seed store and native numeric artifacts.

No backend compilation or native MPC is performed. Python fixtures independently
specify first-match removal, authorization rollback, insertion and eviction.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def slot(valid, key, counter, seed):
    return bytes([valid])+key+counter.to_bytes(4,'big')+seed


def lookup(key, counter, store):
    slots = [store[i:i+69] for i in range(0,len(store),69)]
    query = key+counter.to_bytes(4,'big')
    for index, row in enumerate(slots):
        if row[0] == 255 and row[1:37] == query:
            return b'\xff'+row[37:]+b''.join(slots[:index]+slots[index+1:]+[bytes(69)])
    return bytes(33)+store


def expected(mode, raw, count):
    if mode == 'insert':
        return (b'\xff'+raw[:68]+raw[68:])[:69*count]
    auth = raw[0] if mode == 'consume' else 255
    data = raw[1:] if mode == 'consume' else raw
    candidate = lookup(data[:32],int.from_bytes(data[32:36],'big'),data[36:])
    return candidate if mode == 'lookup' or auth == 255 else bytes(33)+data[36:]


def fixtures(mode, count):
    rng = random.Random(0x534b4950+count)
    key = rng.randbytes(32)
    base = [slot(255,rng.randbytes(32),i,rng.randbytes(32)) for i in range(count)]
    cases=[]
    def add(name, rows, query=key, counter=0x01020304, auth=255, seed=None):
        if mode == 'insert':
            raw=query+counter.to_bytes(4,'big')+(seed if seed is not None else bytes(range(32)))+b''.join(rows)
        else:
            raw=query+counter.to_bytes(4,'big')+b''.join(rows)
            if mode == 'consume': raw=bytes([auth])+raw
        cases.append((name,raw,expected(mode,raw,count)))
    add('miss',base)
    add('empty-slots',[bytes(69)]*count)
    for i in range(count):
        rows=base.copy();rows[i]=slot(255,key,0x01020304,bytes([i+1])*32)
        add(f'hit-position{i}',rows)
        add(f'wrong-counter-position{i}',rows,counter=0x04030201)
        add(f'wrong-key-position{i}',rows,query=bytes([key[0]^1])+key[1:])
    if count:
        for valid in range(256):
            rows=base.copy();rows[0]=slot(valid,key,0x01020304,b'v'*32)
            add(f'validity{valid}',rows)
        rows=base.copy(); rows[0]=slot(255,key,0x01020304,b'A'*32)
        if count>1: rows[1]=slot(255,key,0x01020304,b'B'*32)
        add('duplicates-first-wins',rows)
        if mode=='consume':
            for auth in range(256): add(f'authentication{auth}',rows,auth=auth)
        if count>1:
            rows[0]=slot(1,key,0x01020304,b'A'*32)
            add('invalid-first-valid-second',rows)
    for i in range(20):
        rows=[slot(rng.choice([0,1,254,255]),rng.randbytes(32),rng.getrandbits(32),rng.randbytes(32)) for _ in range(count)]
        if count and i%2:
            target=i%count; chosen=rows[target]
            rows[target]=b'\xff'+chosen[1:]
            add(f'random-hit{i}',rows,chosen[1:33],int.from_bytes(chosen[33:37],'big'),rng.choice([0,255]))
        else: add(f'random-miss{i}',rows,auth=rng.choice([0,255]))
    return cases


def main():
    pins_path=HERE.parent/'pins.json';pins=json.loads(pins_path.read_text())
    rust=ROOT/'.deps/libsignal-v0.106.1'
    references=[rust/name for name in ['rust/protocol/src/double_ratchet.rs','rust/protocol/src/ratchet/keys.rs','rust/protocol/src/consts.rs']]
    archive=ROOT/'.deps/libsignal-v0.106.1.tar.gz'
    assert digest(archive)==pins['libsignal']['archive_sha256']
    with tarfile.open(archive) as bundle:
        for path in references:
            assert path.read_bytes()==bundle.extractfile('signalapp-libsignal-904c8dc/'+str(path.relative_to(rust))).read()
    sources={Path(__file__),HERE/'Export.lean',HERE/'Checks.lean',HERE/'lakefile.toml',HERE/'lake-manifest.json',
             HERE/'lean-toolchain',pins_path,archive,*references,ROOT/'backend_adapter/boolean.py',ROOT/'backend_adapter/aig.py',
             ROOT/'scripts/check_lean_crypto.py'}
    def visit(module):
        if not module.startswith('TlsMpc'):return
        path=ROOT/(module.replace('.','/')+'.lean')
        if path in sources:return
        sources.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)',path.read_text(),re.M):visit(imported)
    visit('TlsMpc.Signal.SkippedKeys')
    snapshot={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    subprocess.run(['lake','-d',str(HERE),'build','emit_skipped_keys'],cwd=ROOT,check=True)
    checks=subprocess.run(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,capture_output=True,text=True,check=True)
    endpoints=re.findall(r'^#print axioms (\S+)',(HERE/'Checks.lean').read_text(),re.M)
    found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",checks.stdout)
    assert [n for n,_ in found]==endpoints
    allowed={'propext','Classical.choice','Quot.sound'}
    for name,axioms in found:assert not ({a.strip() for a in axioms.split(',') if a.strip()}-allowed),name
    (HERE/'axioms.txt').write_text(checks.stdout)
    directory=HERE/'Artifacts';directory.mkdir(exist_ok=True)
    binary=HERE/'.lake/build/bin/emit_skipped_keys'
    results=[];images={};fixture_records=[]
    for count in [0,1,4,16]:
        for mode in ['lookup','consume','insert']:
            path=directory/f'signal-skipped-{mode}-{count}.json'
            with path.open('w') as output:
                subprocess.run([str(binary),mode,str(count)],cwd=ROOT,stdout=output,check=True,timeout=120)
            image=load(path);images[mode,count]=image
            rows=fixtures(mode,count)
            observed=evaluate_lanes(image,[row[1] for row in rows])
            assert observed==[row[2] for row in rows],(mode,count,[row[0] for row,got in zip(rows,observed) if got!=row[2]])
            results.append({'mode':mode,'capacity':count,'artifact':str(path.relative_to(ROOT)),
                'artifact_sha256':digest(path),'input_bits':image['input_bits'],'output_bits':len(image['outputs']),
                'fixture_lanes':len(rows),'adapter_operations':statistics(image)})
            fixture_records += [{'mode':mode,'capacity':count,'label':n,'input':i.hex(),'output':o.hex()} for n,i,o in rows]
            print(f'{mode} capacity{count}: {len(rows)} numeric-artifact fixtures passed',flush=True)
    # Feed actual exported insert outputs into later lookup and transactional
    # consume artifacts. This checks eviction, duplicates, and rollback.
    count=4;store=bytes(69*count);history=[]
    key=bytes(range(32))
    def run(mode,raw):
        actual=evaluate_lanes(images[mode,count],[raw])[0]
        assert actual==expected(mode,raw,count)
        history.append({'mode':mode,'input':raw.hex(),'output':actual.hex()})
        return actual
    for index in range(7):store=run('insert',key+index.to_bytes(4,'big')+bytes([index])*32+store)
    assert run('lookup',key+bytes(4)+store)[0]==0
    store=run('insert',key+(6).to_bytes(4,'big')+b'Z'*32+store)
    query=key+(6).to_bytes(4,'big')
    assert run('lookup',query+store)[1:33]==b'Z'*32
    assert run('consume',b'\x01'+query+store)[33:]==store
    result=run('consume',b'\xff'+query+store);store=result[33:]
    assert result[1:33]==b'Z'*32
    assert run('lookup',query+store)[1:33]==bytes([6])*32
    result=run('consume',b'\xff'+query+store);store=result[33:]
    assert run('lookup',query+store)[0]==0
    fixture_path=HERE/'fixture-results.json'
    fixture_path.write_text(json.dumps({'cases':fixture_records,'artifact_composition':history},indent=2)+'\n')
    assert snapshot=={str(p.relative_to(ROOT)):digest(p) for p in sorted(sources)}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':snapshot,
        'checked_endpoints':len(found),'theorems':endpoints,'allowed_foundational_axioms':sorted(allowed),'custom_axioms':[],
        'axiom_report_sha256':digest(HERE/'axioms.txt'),'native_exporter':str(binary.relative_to(ROOT)),
        'native_exporter_sha256':digest(binary),'artifacts':results,'fixture_report_sha256':digest(fixture_path),
        'numeric_artifact_fixture_count':len(fixture_records),'artifact_composition_steps':len(history),
        'slot_layout':'valid255/0 byte || ratchetPublicKey32 || counterBE4 || seed32; newest first; capacity public',
        'lookup_output':'found255/0 || secret seed32 (zero on miss) || candidate compacted store',
        'consume_output':'committed255/0 || seed32 (zero on failure) || next store; only authentication255 and a hit commit',
        'insert_semantics':'Prepend new valid255 entry, take original public slot capacity; duplicate entries retained; oldest physical slot dropped.',
        'public_boundary':'Capacity and operation only. All validity masks, identifiers, counters, seeds, authentication and outputs remain shared.',
        'rust_reference_commit':pins['libsignal']['commit'],
        'rust_correspondence_review':{'take_skipped_key':'Find first receiver chain by public key; first matching counter position; remove before from_pb.',
            'store_skipped_key':'insert(0,key.into_pb()); pop oldest if length exceeds MAX_MESSAGE_KEYS=2000.',
            'seed_path':'ChainKey.message_keys produces a32-byte HMAC seed; Seed stores seed and counter and later derives keys with optional PQR key.',
            'differences':['This flat fixed-capacity component is not the Rust per-receiver-chain2000-key policy or receiver-chain selection.',
                'Stable compaction pads empty slots; packed valid-prefix states model a bounded list, arbitrary holes remain physical slots.',
                'Authentication-gated commit is an explicit transaction policy; take_skipped_key itself removes immediately, before deserialization.',
                'Only seed32 storage is represented; legacy expanded message keys and corrupt/protobuf records are excluded.']},
        'actual_rust_wrapper_equivalence':False,'complete_session_or_persistence':False,
        'backend_compiled':False,'native_mpc_executed':False,
        'trust_boundary':'Lean compiler/evaluation proofs and transaction theorems; native exporter/JSON/adapter are unverified and checked by public fixtures.'}
    path=HERE/'proof-report.json';path.write_text(json.dumps(report,indent=2)+'\n')
    print('proof-report.json SHA256: '+digest(path),flush=True)


if __name__=='__main__':main()
