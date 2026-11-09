#!/usr/bin/env python3
"""Public directory/journal checks, not private semantic or native admission."""
import hashlib,json,pathlib,subprocess,tempfile,time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[2]
with tempfile.TemporaryDirectory(prefix='shard-directory-',dir=ROOT/'.deps') as tmp:
 tmp=pathlib.Path(tmp);binary=tmp/'checks'
 subprocess.run(['c++','-std=c++20','-O1','-g','-fsanitize=address,undefined','-I/opt/homebrew/opt/openssl@3/include',str(HERE/'directory_checks.cpp'),'-L/opt/homebrew/opt/openssl@3/lib','-lcrypto','-o',str(binary)],check=True)
 start=time.monotonic();run=subprocess.run([str(binary),str(tmp/'data')],capture_output=True,text=True,check=True,timeout=180)
 report=json.loads(run.stdout);report['seconds']=time.monotonic()-start;report['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [HERE/'directory_checks.cpp',HERE/'ShardDirectory.h',HERE/'ShardCheckpoint.h',pathlib.Path(__file__)]}
 (HERE/'directory-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
