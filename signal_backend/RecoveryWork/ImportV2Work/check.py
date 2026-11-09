#!/usr/bin/env python3
"""Candidate private-container hygiene; no protocol-owner retirement claim."""
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
def main():
 source=HERE.parent/'RawFieldReadmit.h';original=source.read_bytes()
 subprocess.run(['python3',str(HERE/'prepare.py')],check=True);assert source.read_bytes()==original
 runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';binary=ROOT/'.deps/signal-import-wipe-check'
 subprocess.run(['make','-C',str(runtime),'-f',str(HERE.parent/'CanonicalMakefile'),'CANONICAL_WORK='+str(HERE.parent),'WIPE_OUTPUT='+str(binary),str(binary)],check=True,capture_output=True,text=True)
 run=subprocess.run([str(binary)],check=True,capture_output=True,text=True);assert run.stdout.strip()=='9 wiping allocator checks passed'
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[pathlib.Path(__file__),HERE/'prepare.py',HERE/'WipingAllocator.h',HERE/'RawFieldReadmitV2.h',HERE/'wipe_check.cpp',HERE/'derivation.json',source,HERE.parent/'CanonicalMakefile']
 (HERE/'report.json').write_text(json.dumps(dict(passed=True,local_public_checks=9,raw_helper_V2_typechecked=True,base_helper_unchanged=True,native_MPC=False,private_container_reallocation_and_final_deallocation_wipe=True,protocol_prep_input_PRNG_owners_not_covered=True,full_restore_admission=False,stdout=run.stdout,binary_sha256=sha(binary),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n')
 print(run.stdout,end='')
if __name__=='__main__':main()
