"""Native owner control, no EMP interoperability claim."""
import json,os,pathlib,re,subprocess,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';MP=BASE/'data61-MP-SPDZ-113c4e4';HERE=pathlib.Path(__file__).resolve().parent
work=pathlib.Path(tempfile.mkdtemp(prefix='native-field-',dir=BASE));files=[];children=[];stats=[];failure=None;start=time.monotonic()
with open(work/'ssl-setup.log','w') as log:subprocess.run(['bash',str(MP/'Scripts/setup-ssl.sh'),'2'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
try:
    for p in (0,1):
        log=open(work/f'{p}.log','w');files.append(log)
        children.append(subprocess.Popen([str(BASE/'native-field-fixture'),str(p),'31570'],cwd=work,env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP)),stdout=log,stderr=subprocess.STDOUT))
    deadline=start+90
    for c in children:
        while True:
            pid,status,u=os.wait4(c.pid,os.WNOHANG)
            if pid:
                c.returncode=os.waitstatus_to_exitcode(status);stats.append(dict(exit_code=c.returncode,cpu_seconds=u.ru_utime+u.ru_stime,peak_rss_bytes=u.ru_maxrss));break
            if time.monotonic()>deadline:raise TimeoutError('native field deadline')
            time.sleep(.02)
except Exception as e:failure=type(e).__name__
finally:
    for c in children:
        if c.returncode is None:
            if c.poll() is None:c.kill()
            c.wait()
    for f in files:f.close()
logs=[(work/f'{p}.log').read_text() for p in (0,1)]
for s,log in zip(stats,logs):
    counters=re.findall(r'EXACT_SOCKET_BYTES sent=(\d+) received=(\d+)',log)
    if len(counters)==1:s['sent_bytes'],s['received_bytes']=map(int,counters[0])
passed=failure is None and len(stats)==2 and all(s['exit_code']==0 for s in stats) and all('native field fixture passed equality_only=2' in log for log in logs)
# Raw socket overlay does not include OpenSSL BIO payload on CryptoPlayer.
# It is diagnostic only and MUST NOT be used as complete wire accounting.
for s,log in zip(stats,logs):
    values=re.findall(r'NATIVE_PROTOCOL_SENT bytes=(\d+)',log)
    if len(values)==1:s['protocol_sent_bytes_excluding_tls']=int(values[0])
report=dict(passed=passed,failure_category=failure,directory=str(work),seconds=time.monotonic()-start,parties=stats,build=json.loads((BASE/'field-build.json').read_text()),scope='Native p25519 authenticated input/multiply/check/open owner, second operation consumes retained product. Opens only fixture equality zeros. NOT an EMP bridge or daBit validation.',counter_scope='Raw EXACT_SOCKET_BYTES misses OpenSSL BIO payload; not complete wire bytes. Player total_comm includes native protocol child channels but excludes TLS framing.',security='MP-SPDZ pinned secure-OT candidate,2PC/t1/abort, fresh local preprocessing/MAC state; caught-failure erasure unvalidated.')
target=HERE/'field-owner-report.json';target.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(passed=passed,directory=str(work))))
if not passed:raise SystemExit(1)
