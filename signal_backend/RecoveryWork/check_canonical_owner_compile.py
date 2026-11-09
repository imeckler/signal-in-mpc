#!/usr/bin/env python3
"""Compile-only internal canonical owner candidate; no MPC or admission test."""
import hashlib,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
SOURCES=['signal_backend/RecoveryWork/NativeRecordBinding.h','signal_backend/RecoveryWork/NativeCanonicalSendOwner.h','signal_backend/RecoveryWork/canonical_owner_compile.cpp','SignalReference/PrivateRecordWork/ExportBinding.lean']
def main():
    command=['clang++','-std=c++20','-fsyntax-only','-DUSE_GF2N_LONG','-Ihandshake_backend','-Isignal_backend','-I.deps/sharing-refresh/MP-SPDZ','-I.deps/sharing-refresh/MP-SPDZ/deps','-I/opt/homebrew/include',SOURCES[2]]
    result=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,check=True)
    subprocess.run(['lake','env','lean',SOURCES[3]],cwd=ROOT,capture_output=True,text=True,check=True)
    dependencies=['signal_backend/VariableServiceWork/VariableShape.h','signal_backend/VariableServiceWork/VariableSendStore.h','signal_backend/VariableServiceWork/VariableSendBatch.h','signal_backend/VariableServiceWork/NativeVariableService.h','handshake_backend/NativeWorker.h']
    report={'passed':True,'scope':'C++20 forced template instantiation for candidate B1/batch canonical owner and Lean binding exporter typecheck only. No pinned binding artifact, native evaluation, transaction execution, recovery or admission evidence.','command':command,'compiler':subprocess.check_output(['clang++','--version'],text=True).splitlines()[0],'diagnostics':result.stderr,'source_sha256':{s:hashlib.sha256((ROOT/s).read_bytes()).hexdigest() for s in SOURCES+dependencies}}
    (ROOT/'signal_backend/RecoveryWork/canonical-owner-compile-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: candidate owner templates and binding exporter typecheck')
if __name__=='__main__':main()
