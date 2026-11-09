#!/usr/bin/env python3
"""Compile adapter type/shape only. Does not execute MPC or admit providers."""
import hashlib,json,subprocess
from pathlib import Path
here=Path(__file__).resolve().parent;root=here.parents[1];runtime=root/'.deps/sharing-refresh/MP-SPDZ'
cmd=['clang++','-std=c++20','-fsyntax-only','-DUSE_GF2N_LONG','-I'+str(root/'handshake_backend'),'-I'+str(root/'signal_backend'),'-I'+str(runtime),'-I'+str(runtime/'deps'),'-I/opt/homebrew/include',str(here/'native_record_probe.cpp')]
p=subprocess.run(cmd,text=True,capture_output=True);assert p.returncode==0,p.stderr
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
files=[here/'check_native_record_header.py',here/'NativeCanonicalRecord.h',here/'native_record_probe.cpp',root/'handshake_backend/NativeWorker.h',root/'signal_backend/VariableServiceWork/VariableShape.h']
(here/'native-record-header-report.json').write_text(json.dumps(dict(passed=True,syntax_only=True,linked=False,native_MPC=False,provider_admission=False,command=cmd,source_sha256={str(p.relative_to(root)):sha(p)for p in files}),indent=2)+'\n');print('native canonical record adapter syntax passed')
