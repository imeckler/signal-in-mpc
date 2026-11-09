#!/usr/bin/env python3
"""Public local exact CCD cell-shape admission regression; no MPC or opens."""
import hashlib,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent

def main():
 runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';binary=ROOT/'.deps/signal-archive-shape-check'
 command=['make','-C',str(runtime),'-f',str(HERE/'CanonicalMakefile'),'CANONICAL_WORK='+str(HERE),'SHAPE_OUTPUT='+str(binary),str(binary)]
 subprocess.run(command,check=True,capture_output=True,text=True)
 run=subprocess.run([str(binary)],check=True,capture_output=True,text=True);assert run.stdout.strip()=='12 archive exact-cell admission checks passed'
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 sources=[pathlib.Path(__file__),HERE/'NativeOwnShareArchive.h',HERE/'archive_shape_check.cpp',HERE/'CanonicalMakefile',ROOT/'handshake_backend/NativeWorker.h',runtime/'GC/TinySecret.h',runtime/'GC/Secret.h']
 (HERE/'archive-shape-report.json').write_text(json.dumps(dict(passed=True,checks=12,native_MPC=False,keys_opened=False,one_bit_constants_accepted=True,default_packed64_rejected=True,two_register_and_outer_widths_rejected=True,archive_guard_not_relaxed=True,stdout=run.stdout,binary_sha256=sha(binary),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources}),indent=2)+'\n')
 print(run.stdout,end='')
if __name__=='__main__':main()
