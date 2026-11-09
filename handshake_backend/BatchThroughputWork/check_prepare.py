#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys,tempfile
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from handshake_backend.BatchThroughputWork.prepare_service import phase
with tempfile.TemporaryDirectory(prefix='tls-public-phase-')as folder:
 path=Path(folder)
 receipt=phase([sys.executable,'-c','print("public phase fixture")'],path,path/'pass.log',10)
 assert receipt['elapsed_seconds']>=0 and receipt['pid']>0 and receipt['user_cpu_seconds']>=0 and receipt['rusage_maxrss']>0
 try:phase([sys.executable,'-c','raise SystemExit(7)'],path,path/'reject.log',10);raise AssertionError('child failure accepted')
 except subprocess.CalledProcessError as error:assert error.returncode==7
 try:phase([sys.executable,'-c','import time;time.sleep(10)'],path,path/'timeout.log',.01);raise AssertionError('deadline accepted')
 except TimeoutError:pass
print('public phase PID/rusage/exit/timeout-reap checks passed')
