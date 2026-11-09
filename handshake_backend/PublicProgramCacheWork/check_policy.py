#!/usr/bin/env python3
from pathlib import Path
import subprocess,tempfile,json,hashlib
work=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory(prefix='tls-public-code-policy-')as directory:
 directory=Path(directory);binary=directory/'checks'
 subprocess.run(['c++','-std=c++17','-fsanitize=address,undefined','-I/opt/homebrew/include',str(work/'cache_checks.cpp'),'-L/opt/homebrew/lib','-lsodium','-o',str(binary)],check=True)
 result=subprocess.run([str(binary),str(directory/'public-input')],text=True,capture_output=True,check=True)
 assert result.stdout.startswith('PASS public LRU/')
report={'passed':True,'scope':'public-only policy/snapshot host checks, separate from actual MPC fixture','sanitizers':['address','undefined'],'checks':['LRU eviction','accounted budget','entry replacement','oversized bypass','configuration identity separation','explicit clear','SHA mutation rejection','missing pin rejection','parse snapshot stable after pathname mutation','stream seek/tell'], 'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [Path(__file__),work/'cache_checks.cpp',work/'PublicCodeCache.h',work/'PinnedPublicCode.h']}}
(work/'policy-report.json').write_text(json.dumps(report,indent=2)+'\n');print(result.stdout.strip())
