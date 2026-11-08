#!/usr/bin/env python3
"""Focused native adapter compile/link and public fixture dimensions only."""
import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';binary=ROOT/'.deps/private-text-adapters-probe'
subprocess.run(['make','-f',str(HERE/'Makefile'),'TEXT_WORK='+str(HERE),'TEXT_OUTPUT='+str(binary),str(binary)],cwd=runtime,check=True)
subprocess.run([str(binary)],check=True)
files=[Path(__file__),HERE/'adapters_probe.cpp',HERE/'Makefile',HERE/'NativeTextNotification.h',HERE/'TextNotificationInput.h',HERE/'PublicTextFixture.h',ROOT/'handshake_backend/NativeWorker.h']
report=dict(compile_link_and_fixture_dimensions_passed=True,native_MPC_executed=False,
 source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
(HERE/'adapter-report.json').write_text(json.dumps(report,indent=2)+'\n')
