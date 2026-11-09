#!/usr/bin/env python3
"""Compile/link only; no native MPC/execution or bootstrap acceptance."""
import hashlib,json,os,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def main():
 runtime=ROOT/'.deps/tls-caught-failure-runtime/MP-SPDZ';binary=ROOT/'.deps/bootstrap-adapter-probe'
 subprocess.run(['make','-C',str(runtime),'-f',str(HERE/'Makefile'),'BOOTSTRAP_WORK='+str(HERE),'BOOTSTRAP_PROBE='+str(binary),str(binary)],check=True)
 subprocess.run([str(binary)],env=dict(os.environ,DYLD_LIBRARY_PATH=str(runtime)),check=True)
 files=[pathlib.Path(__file__),HERE/'adapter_probe.cpp',HERE/'Makefile',HERE/'NativeKyber1024.h',HERE/'NativeBootstrapDh.h',ROOT/'handshake_backend/NativeWorker.h']
 report=dict(compile_link_passed=True,native_MPC=False,whole_bootstrap=False,binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'adapter-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
