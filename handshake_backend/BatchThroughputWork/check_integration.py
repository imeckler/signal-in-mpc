#!/usr/bin/env python3
"""Focused host ownership/protocol tests; no full service batch execution claim."""
from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
binary=Path('/tmp/tls-mux-batch-checked')
subprocess.run(['c++','-std=c++20','-O1','-g','-fsanitize=address,undefined','-I'+str(ROOT/'handshake_backend/WebSocketWork'),'-I'+str(ROOT/'handshake_backend'),str(WORK/'mux_batch_checks.cpp'),'-o',str(binary)],check=True)
subprocess.run([str(binary)],check=True)
subprocess.run([sys.executable,str(ROOT/'scripts/check_private_mux_registry.py')],check=True,cwd=ROOT)
subprocess.run(['lake','env','lean',str(ROOT/'handshake_backend/WebSocketWork/MuxProviderController.lean')],check=True,cwd=ROOT)
for source in ['programs/signal_variable_service_batch.mpc','scripts/check_native_text_mux_profile.py']:subprocess.run([sys.executable,'-m','py_compile',source],check=True,cwd=ROOT)
paths=[WORK/'NativeBatchService.h',WORK/'mux_batch_checks.cpp',ROOT/'handshake_backend/NativeSession.h',ROOT/'handshake_backend/NativeDispatch.h',ROOT/'handshake_backend/PublicProtocol.h',*[ROOT/'handshake_backend/WebSocketWork'/name for name in ['NativeConversation.h','PrivateMuxRegistry.h','MuxProviderCoordinator.h','mux_worker_main.cpp','MuxProviderController.lean']],ROOT/'TlsMpc/TlsWorker.lean',ROOT/'TlsMpc/TlsWorkerPipe.lean',ROOT/'programs/signal_variable_service_batch.mpc',ROOT/'signal_backend/VariableServiceWork/VariableSendStore.h',ROOT/'signal_backend/VariableServiceWork/VariableSendBatch.h']
report={'passed':True,'scope':'Sanitized registry batch ownership/rejection/one-checkpoint/independentcompletion, oldregistry regressions and actualLean controller elaboration; OwnedBits API compiled separately. No fullservicebatch artifact/native execution or application gate promotion.','source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths}}
(WORK/'integration-report.json').write_text(json.dumps(report,indent=2)+'\n');print('batch host integration checks passed')
