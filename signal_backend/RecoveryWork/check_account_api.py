#!/usr/bin/env python3
"""Real OwnedBits/candidate runtime header boundary, no native activation."""
import hashlib,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ'
cmd=['clang++','-std=c++20','-fsyntax-only','-DUSE_GF2N_LONG',*['-I'+str(p)for p in [ROOT/'handshake_backend',ROOT/'signal_backend',runtime,runtime/'deps',pathlib.Path('/opt/homebrew/include'),pathlib.Path('/opt/homebrew/opt/openssl@3.5/include')]],str(HERE/'account_api_compile.cpp')]
p=subprocess.run(cmd,capture_output=True,text=True);assert p.returncode==0,p.stderr
files=[pathlib.Path(__file__),HERE/'account_api_compile.cpp',HERE/'AccountAdmission.h',HERE/'NativeAccountAdmission.h',HERE/'NativeAccountReadmit.h',HERE/'NativeAccountOutbox.h',HERE/'AccountDurableOwnerV1.h',HERE/'AccountRecoveryEngineV1.h',HERE/'ImportV2Work/RawFieldReadmitV2.h',ROOT/'handshake_backend/SessionWork/NativeLifecycle.h']
(HERE/'account-api-report.json').write_text(json.dumps(dict(passed=True,syntax_only=True,native_MPC=False,candidate_engine_wired=True,capability_constructed=False,whole_account_activation=False,command=cmd,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files}),indent=2)+'\n');print('PASS: actual account admission/readmit API syntax')
