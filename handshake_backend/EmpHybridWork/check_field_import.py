#!/usr/bin/env python3
"""Run the field-import fixture (field_import_fixture.cpp) for both parties.

Cases: malicious build, honest shares (must open correctly); malicious build,
one party shifts a value share (the opening must be rejected by its MAC check);
semi-honest build, honest shares.
"""
import json,os,pathlib,subprocess,sys,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parents[2];BASE=ROOT/'.deps/two-party-comparison';MP=BASE/'data61-MP-SPDZ-113c4e4';HERE=pathlib.Path(__file__).resolve().parent
def run(binary,port,extra):
    work=pathlib.Path(tempfile.mkdtemp(prefix='field-import-',dir=BASE))
    with open(work/'ssl-setup.log','w') as log:subprocess.run(['bash',str(MP/'Scripts/setup-ssl.sh'),'2'],cwd=work,stdout=log,stderr=subprocess.STDOUT,check=True)
    children=[];logs=[];start=time.monotonic()
    for party in (0,1):
        log=open(work/f'{party}.log','w');logs.append(log)
        children.append(subprocess.Popen([str(BASE/binary),str(party),str(port),*extra],cwd=work,env=dict(os.environ,DYLD_LIBRARY_PATH=str(MP)),stdout=log,stderr=subprocess.STDOUT))
    codes=[]
    try:
        for c in children:codes.append(c.wait(timeout=300))
    except subprocess.TimeoutExpired:
        for c in children:c.terminate()
        codes=['timeout']
    for log in logs:log.close()
    lines=[line for party in (0,1) for line in (work/f'{party}.log').read_text(errors='replace').split('\n') if line.startswith('FIELD_IMPORT') or 'field import fixture' in line]
    return dict(exit_codes=codes,seconds=round(time.monotonic()-start,1),lines=lines,work=str(work))
report={'malicious':run('field-import-fixture-v3',23110,[]),'malicious-tamper':run('field-import-fixture-v3',23130,['tamper']),'semi-honest':run('field-import-sh-fixture-v3',23150,[])}
report['passed']=all(case['exit_codes']==[0,0] for case in report.values())
(HERE/'field-import-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
sys.exit(0 if report['passed'] else 1)
