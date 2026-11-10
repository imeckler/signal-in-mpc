"""Re-run the mixed EMP/native-field bridge controls on the validated-v3 engine.

Functional and fault-control evidence for the candidate backend at statistical
128 on the Boolean side. Not a security proof; the daBit pool parameters and the
cross-engine composition argument are separate obligations.
"""
import hashlib,json,os,pathlib,re,subprocess,sys,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';MP=BASE/'data61-MP-SPDZ-113c4e4';HERE=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def launch(binary,prefix,port,args,fault=None,deadline_seconds=180):
    work=pathlib.Path(tempfile.mkdtemp(prefix=prefix,dir=BASE));files=[];children=[];stats=[];failure=None;start=time.monotonic()
    with open(work/'ssl-setup.log','w') as log:subprocess.run(['bash',str(MP/'Scripts/setup-ssl.sh'),'2'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
    try:
        for party in (1,2):
            log=open(work/f'{party}.log','w');files.append(log);env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP))
            if fault and party==2:env[fault]='1'
            children.append(subprocess.Popen([str(binary),str(party),str(port),*args],cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT))
        deadline=start+deadline_seconds
        for c in children:
            while True:
                pid,status,u=os.wait4(c.pid,os.WNOHANG)
                if pid:c.returncode=os.waitstatus_to_exitcode(status);stats.append(dict(exit_code=c.returncode,cpu_seconds=u.ru_utime+u.ru_stime,peak_rss_bytes=u.ru_maxrss));break
                if time.monotonic()>deadline:raise TimeoutError('deadline')
                time.sleep(.02)
    except Exception as e:failure=type(e).__name__
    finally:
        for c in children:
            if c.returncode is None:
                if c.poll() is None:c.kill()
                c.wait()
        for f in files:f.close()
    logs=[(work/f'{p}.log').read_text() for p in (1,2)]
    for s,log in zip(stats,logs):
        values=re.findall(r'^EMP_EXACT_SOCKET_BYTES sent=(\d+) received=(\d+)',log,re.M)
        if len(values)==1:s['emp_sent_bytes'],s['emp_received_bytes']=map(int,values[0])
        values=re.findall(r'NATIVE_PROTOCOL_SENT bytes=(\d+)',log)
        if len(values)==1:s['native_protocol_sent_bytes_excluding_tls']=int(values[0])
    return dict(fault=fault,seconds=time.monotonic()-start,directory=str(work),failure_category=failure,parties=stats),logs
def word_roundtrip(binding,port,fault=None):
    r,logs=launch(BASE/'word-roundtrip-fixture-v3','word-roundtrip-v3-',port,[pow(444,256,2**255-19).to_bytes(32,'little').hex(),binding],fault,90)
    s=r['parties'];ok=r['failure_category'] is None and len(s)==2
    if fault:ok=ok and all(x['exit_code']!=0 for x in s) and all('word roundtrip fixture passed' not in l for l in logs) and any('stage=word-back-reserve' in l for l in logs)
    else:ok=ok and all(x['exit_code']==0 for x in s) and all('word roundtrip fixture passed pairs_consumed=510 private_result_equality=1 native_roundtrip_equality=1' in l for l in logs) and s[0].get('emp_sent_bytes')==s[1].get('emp_received_bytes') and s[1].get('emp_sent_bytes')==s[0].get('emp_received_bytes')
    r['passed']=ok;return r
def wire_bits(data):return bytes((b>>(7-i))&1 for b in data for i in range(8))
V1=('curve-fixture-v3','hybrid curve fixture passed canonical_private_bytes=32 consumed_pairs=766')
V2=('curve-v2-fixture-v3','hybrid curve v2 fixture passed private_result_bits=255 word_masks_generated=16 word_masks_consumed=2 bit_pairs_consumed=0')
V2_64=('curve-v2-64-fixture-v3','hybrid curve v2 fixture passed private_result_bits=255 word_masks_generated=64 word_masks_consumed=2 bit_pairs_consumed=0')
V2_BITS=('curve-v2-bits-fixture-v3','hybrid curve v2 fixture passed private_result_bits=255 word_masks_generated=15 word_masks_consumed=2 bit_pairs_consumed=252')
KDF=('curve-kdf-fixture-v3','curve kdf fixture passed private_secret_bytes=128 dh_opened=0 word_masks_consumed=2')
def tls_handshake_secrets(ecdhe,transcript):
    """Independent RFC 8446 handshake key schedule (hashlib/hmac)."""
    import hmac
    def extract(salt,ikm):return hmac.new(salt,ikm,hashlib.sha256).digest()
    def expand_label(secret,label,context):
        full=b'tls13 '+label;info=(32).to_bytes(2,'big')+bytes([len(full)])+full+bytes([len(context)])+context
        return hmac.new(secret,info+b'\x01',hashlib.sha256).digest()
    empty=hashlib.sha256(b'').digest();zero=bytes(32)
    handshake=extract(expand_label(extract(zero,zero),b'derived',empty),ecdhe)
    return handshake+expand_label(handshake,b'c hs traffic',transcript)+expand_label(handshake,b's hs traffic',transcript)+extract(expand_label(handshake,b'derived',empty),zero)
def curve(binding,port,kind,variant=V1,fault=None,stage=None,kdf=False):
    """Private scalar and point enter as XOR shares; only equality and nonzero status open."""
    from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey,X25519PublicKey
    from cryptography.hazmat.primitives import serialization as ser
    scalar=os.urandom(32)
    point=bytes(32) if kind=='low-order' else X25519PrivateKey.generate().public_key().public_bytes(ser.Encoding.Raw,ser.PublicFormat.Raw)
    expected=bytes(32) if kind=='low-order' else X25519PrivateKey.from_private_bytes(scalar).exchange(X25519PublicKey.from_public_bytes(point))
    fourth,fifth=None,None;extra_secret=b''
    if kdf=='signal':
        # Root key is private state: XOR-shared like the scalar and coordinate.
        import hmac
        root=os.urandom(32);extra_secret=root
        def hkdf(salt,ikm,info,length):
            prk=hmac.new(salt,ikm,hashlib.sha256).digest();out=b'';block=b'';i=1
            while len(out)<length:block=hmac.new(prk,block+info+bytes([i]),hashlib.sha256).digest();out+=block;i+=1
            return out[:length]
        secrets=bytes([0])+root+bytes(36) if expected==bytes(32) else bytes([255])+hkdf(root,expected,b'WhisperRatchet',64)+bytes(4)
        if kind=='mismatch':secrets=bytes([secrets[0]^1])+secrets[1:]
        fourth,fifth=secrets.hex(),'-'
    elif kdf:
        # The fixture receives the derived secrets and a public transcript hash, never the DH value.
        transcript=os.urandom(32);secrets=tls_handshake_secrets(expected,transcript)
        if kind=='mismatch':secrets=bytes([secrets[0]^1])+secrets[1:]
        fourth,fifth=secrets.hex(),transcript.hex()
    elif kind=='mismatch':expected=bytes([expected[0]^1])+expected[1:]
    # Scalar and coordinate use the application wire order; the root key uses the key-derivation circuit's order (bit b of byte j at 8*j+b).
    secret=wire_bits(scalar+point)+bytes((b>>i)&1 for b in extra_secret for i in range(8));share_a=bytes(b&1 for b in os.urandom(len(secret)));share_b=bytes(x^y for x,y in zip(secret,share_a))
    staging=pathlib.Path(tempfile.mkdtemp(prefix='curve-v3-inputs-',dir=BASE));(staging/'1.share').write_bytes(share_a);(staging/'2.share').write_bytes(share_b)
    flat=ROOT/'.deps/emp-hybrid-curve-v1/x25519.flat'
    # Each party gets only its own share; argv differs per party, so launch twice-parameterised.
    work=pathlib.Path(tempfile.mkdtemp(prefix='curve-v3-',dir=BASE));files=[];children=[];stats=[];failure=None;start=time.monotonic()
    with open(work/'ssl-setup.log','w') as log:subprocess.run(['bash',str(MP/'Scripts/setup-ssl.sh'),'2'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
    try:
        for party in (1,2):
            log=open(work/f'{party}.log','w');files.append(log);env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP))
            if fault and party==2:env[fault]='1'
            children.append(subprocess.Popen([str(BASE/variant[0]),str(party),str(port),str(staging/f'{party}.share'),fourth or expected.hex(),fifth or str(flat),binding,str(work/f'{party}.json')],cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT))
        deadline=start+300
        for c in children:
            while True:
                pid,status,u=os.wait4(c.pid,os.WNOHANG)
                if pid:c.returncode=os.waitstatus_to_exitcode(status);stats.append(dict(exit_code=c.returncode,cpu_seconds=u.ru_utime+u.ru_stime,peak_rss_bytes=u.ru_maxrss));break
                if time.monotonic()>deadline:raise TimeoutError('deadline')
                time.sleep(.05)
    except Exception as e:failure=type(e).__name__
    finally:
        for c in children:
            if c.returncode is None:
                if c.poll() is None:c.kill()
                c.wait()
        for f in files:f.close()
        for p in (1,2):(staging/f'{p}.share').unlink(missing_ok=True)
        staging.rmdir()
    logs=[(work/f'{p}.log').read_text() for p in (1,2)]
    for p,s in zip((1,2),stats):
        m=work/f'{p}.json'
        if m.exists():s['metrics']=json.loads(m.read_text())
        values=re.findall(r'NATIVE_PROTOCOL_SENT bytes=(\d+)',logs[p-1])
        if len(values)==1:s['native_protocol_sent_bytes_excluding_tls']=int(values[0])
        values=re.findall(r'NATIVE_LOGICAL completed_products=(\d+) local_inputs=(\d+)',logs[p-1])
        if len(values)==1:s['native_products'],s['native_local_inputs']=map(int,values[0])
    ok=failure is None and len(stats)==2
    # In the Signal ratchet an all-zero agreement is handled inside the circuit: the run succeeds with the old root kept.
    if (kind=='valid' or (kdf=='signal' and kind=='low-order')) and not fault:ok=ok and all(s['exit_code']==0 for s in stats) and all(variant[1] in l for l in logs)
    else:
        # A rejection is first seen by one party; the peer then fails on the closed channel.
        expected=stage or ('curve-nonzero' if kind=='low-order' else 'curve-equality')
        ok=ok and all(s['exit_code']!=0 for s in stats) and all('fixture passed' not in l for l in logs) and (all if not fault else any)('stage='+expected in l for l in logs)
    return dict(passed=ok,kind=kind,fault=fault,binary=variant[0],seconds=time.monotonic()-start,directory=str(work),failure_category=failure,parties=stats,last_stage=[re.findall(r'stage=([\w-]+)',l)[-1:] for l in logs])
def os_buffer_exhausted(result):
    """Loopback runs back to back can exhaust kernel socket buffers (ENOBUFS). That is a host condition, not a protocol outcome."""
    d=pathlib.Path(result['directory'])
    return any('No buffer space available' in p.read_text(errors='replace') for p in d.glob('*.log'))
def retrying(function):
    def wrapped(*args,**kwargs):
        attempts=[]
        for _ in range(4):
            result=function(*args,**kwargs)
            if result['passed'] or not os_buffer_exhausted(result):break
            attempts.append(result['directory']);time.sleep(8)
        result['os_buffer_retries']=attempts;return result
    return wrapped
word_roundtrip=retrying(word_roundtrip);curve=retrying(curve)
if __name__=='__main__':
    build=json.loads((BASE/'hybrid-v3-build.json').read_text())
    closure={'binary':build['word-roundtrip']['binary_sha256'],'emp_source':build['emp_source']['files'],'native_library':sha(MP/'libSPDZ.so'),'parties':'A=EMP1/native0,B=EMP2/native1','boolean_statistical':128,'computational_target':128,'epoch':0}
    binding=hashlib.sha256(json.dumps(closure,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    results=dict(word_roundtrip=word_roundtrip(binding,33610));time.sleep(1)
    results['word_roundtrip_wrong_counter']=word_roundtrip(binding,33640,'EMP_TEST_WRONG_POOL_COUNTER')
    if 'curve' in build:
        closure['binary']=build['curve']['binary_sha256'];closure['flat']=sha(ROOT/'.deps/emp-hybrid-curve-v1/x25519.flat')
        curve_binding=hashlib.sha256(json.dumps(closure,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        for i,kind in enumerate(('valid','low-order','mismatch')):
            time.sleep(1);results['curve_'+kind]=curve(curve_binding,33700+40*i,kind)
    if 'curve-v2' in build:
        closure['binary']=build['curve-v2']['binary_sha256']
        v2_binding=hashlib.sha256(json.dumps(closure,sort_keys=True,separators=(',',':')).encode()).hexdigest();port=34000
        for name,kind,fault,stage in (('valid','valid',None,None),('low-order','low-order',None,None),('mismatch','mismatch',None,None),
                ('all_candidates_inconsistent','valid','EMP_TEST_WORD_INCONSISTENT','word-masks'),('one_candidate_inconsistent','valid','EMP_TEST_WORD_ONE_BAD','word-masks'),('scalar_nonbit','valid','EMP_TEST_SCALAR_NONBIT','scalar-field-bits')):
            time.sleep(1);results['curve_v2_'+name]=curve(v2_binding,port,kind,V2,fault,stage);port+=40
        for name,variant,fault,stage in (('batch64_valid',V2_64,None,None),('boolean_scalar_valid',V2_BITS,None,None),
                ('boolean_scalar_wrong_field_bit',V2_BITS,'EMP_TEST_BITBLOCK_WRONG','word-masks'),('boolean_scalar_nonbit_field_input',V2_BITS,'EMP_TEST_BITBLOCK_NONBIT','word-masks')):
            if variant[0].replace('-fixture-v3','') in build:time.sleep(1);results['curve_v2_'+name]=curve(v2_binding,port,'valid',variant,fault,stage);port+=40
    if 'curve-kdf' in build:
        closure['binary']=build['curve-kdf']['binary_sha256']
        kdf_binding=hashlib.sha256(json.dumps(closure,sort_keys=True,separators=(',',':')).encode()).hexdigest();port=35000
        for name,kind,stage in (('valid','valid',None),('all_zero_shared_secret','low-order','curve-nonzero'),('wrong_secrets','mismatch','secrets-equality')):
            time.sleep(1);results['curve_kdf_'+name]=curve(kdf_binding,port,kind,KDF,None,stage,kdf=True);port+=40
    if 'curve-ratchet' in build:
        closure['binary']=build['curve-ratchet']['binary_sha256']
        ratchet_binding=hashlib.sha256(json.dumps(closure,sort_keys=True,separators=(',',':')).encode()).hexdigest();port=35400
        RATCHET=('curve-ratchet-fixture-v3','curve kdf fixture passed private_secret_bytes=69 dh_opened=0 word_masks_consumed=2')
        for name,kind,stage in (('valid','valid',None),('zero_agreement_keeps_root','low-order',None),('wrong_state','mismatch','secrets-equality')):
            time.sleep(1);results['signal_ratchet_'+name]=curve(ratchet_binding,port,kind,RATCHET,None,stage,kdf='signal');port+=40
    ok=all(r['passed'] for r in results.values())
    report=dict(passed=ok,secure_hybrid_backend=False,program_binding_sha256=binding,results=results,build=build,scope='Bridge controls re-run on validated-v3 (Boolean statistical 128, authenticated PUBLIC openings). Private native-field value to 255 EMP bits and back with 510 checked masks; wrong operation counter rejected before the reverse mask opens. Bridge pools use the statistical-128 cut/bucket profile (parameters-128-report.json). Native X25519 over the pinned FieldDag with XOR-shared private scalar and point: result checked inside MPC against an independent library value, opening only equality and nonzero status; all-zero point and wrong expectation both rejected. Local loopback fixture; no remote identity binding, erasure or composition proof.',cost_note='Native protocol bytes exclude TLS framing and include unused live preprocessing (batch 10000).')
    (HERE/'hybrid-v3-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=ok,cases={k:v['passed'] for k,v in results.items()},seconds={k:round(v['seconds'],1) for k,v in results.items()})))
    if not ok:raise SystemExit(1)
