"""First real EMP/native checked coin experiment; no full conversion claim."""
import hashlib,json,os,pathlib,re,subprocess,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';MP=BASE/'data61-MP-SPDZ-113c4e4';HERE=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def run(port,bad=None):
    work=pathlib.Path(tempfile.mkdtemp(prefix='word-roundtrip-',dir=BASE));files=[];children=[];stats=[];failure=None;start=time.monotonic()
    with open(work/'ssl-setup.log','w') as log:subprocess.run(['bash',str(MP/'Scripts/setup-ssl.sh'),'2'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
    try:
        for party in (1,2):
            log=open(work/f'{party}.log','w');files.append(log);env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP))
            if bad and party==2:
                env['EMP_TEST_WRONG_POOL_COUNTER']='1' 
            children.append(subprocess.Popen([str(BASE/'word-roundtrip-fixture'),str(party),str(port),pow(444,256,2**255-19).to_bytes(32,'little').hex(),program_binding],cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT))
        deadline=start+90
        for c in children:
            while True:
                pid,status,u=os.wait4(c.pid,os.WNOHANG)
                if pid:c.returncode=os.waitstatus_to_exitcode(status);stats.append(dict(exit_code=c.returncode,cpu_seconds=u.ru_utime+u.ru_stime,peak_rss_bytes=u.ru_maxrss));break
                if time.monotonic()>deadline:raise TimeoutError('bridge deadline')
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
        for label,key in [('EMP_EXACT_SOCKET_BYTES','emp'),('EXACT_SOCKET_BYTES','native_incomplete_socket')]:
            values=re.findall(r'^'+label+r' sent=(\d+) received=(\d+)',log,re.M)
            if len(values)==1:s[key+'_sent_bytes'],s[key+'_received_bytes']=map(int,values[0])
        values=re.findall(r'NATIVE_PROTOCOL_SENT bytes=(\d+)',log)
        if len(values)==1:s['native_protocol_sent_bytes_excluding_tls']=int(values[0])
    passed=failure is None and len(stats)==2 and (all(s['exit_code']!=0 for s in stats) and all('word roundtrip fixture passed' not in log for log in logs) and any('stage=word-back-reserve' in log for log in logs) if bad else all(s['exit_code']==0 for s in stats) and all('word roundtrip fixture passed pairs_consumed=510 private_result_equality=1 native_roundtrip_equality=1' in log for log in logs))
    if passed and not bad:passed=stats[0]['emp_sent_bytes']==stats[1]['emp_received_bytes'] and stats[1]['emp_sent_bytes']==stats[0]['emp_received_bytes']
    return dict(passed=passed,fault=bad,seconds=time.monotonic()-start,directory=str(work),failure_category=failure,parties=stats)
if __name__=='__main__':
    build=json.loads((BASE/'word-roundtrip-build.json').read_text())
    # Public code/runtime/config ONLY; no input-share/preprocessing file hashes.
    closure={'binary':build['binary_sha256'],'dependencies':build['dependencies'],'native_sources':build['field_build']['sources'],'native_library':sha(MP/'libSPDZ.so'),'EMP_pins':build['emp_build']['pins'],'overlay':build['linear_mask_overlay'],'parties':'A=EMP1/native0,B=EMP2/native1','statistical':40,'computational_target':128,'epoch':0}
    program_binding=__import__('hashlib').sha256(json.dumps(closure,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    results=[run(32210)]
    time.sleep(1)
    results.append(run(32240,'counter'))
    report=dict(program_binding_sha256=program_binding,passed=all(r['passed'] for r in results),results=results,build=json.loads((BASE/'word-roundtrip-build.json').read_text()),source_sha256=sha(HERE/'word_roundtrip_fixture.cpp'),scope='Private native-field arithmetic→EMP255bits→native-field full-word roundtrip,510 distinct masks from512-pair checked pool with two ordered direction-bound frames; independent EMP equality and native roundtrip equality only. Wrong second operation counter rejects before reverse mask opening. No X25519,remote identity,erasure or malicious-composition proof.',security='Current unaudited EMP and pinned native MASCOT,t1/abort,configured40. Exact combinatorial model checked separately; implementation/theorem composition unvalidated.',counter_scope='EMP counters include final flush/sibling. Native protocol bytes exclude TLS framing; raw native socket counters omit OpenSSL BIO payload. Live batch10000 creates much unused preprocessing.')
    target=HERE/'word-roundtrip-report.json';target.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=report['passed'],report=str(target))))
    if not report['passed']:raise SystemExit(1)
