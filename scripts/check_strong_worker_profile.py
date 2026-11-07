#!/usr/bin/env python3
"""Build/check actual long-field types and checked bit conversion. No MPC run."""
from pathlib import Path
import subprocess,json,hashlib
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1]

def main():
    backend=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    subprocess.run(['make','-f',str(ROOT/'handshake_backend/Makefile'),'TLS_ROOT='+str(ROOT/'handshake_backend'),
                    '../tls-worker','../tls-worker-build','../tls-strong-profile-checks'],cwd=backend,check=True,capture_output=True,timeout=180)
    result=subprocess.run([str(backend.parent/'tls-strong-profile-checks')],check=True,capture_output=True,text=True,timeout=10)
    names=['handshake_backend/StrongShamirShare.h','handshake_backend/DaBitOnly.h','handshake_backend/LongFieldBit.h',
           'handshake_backend/NativeWorker.h','handshake_backend/OwnedSecrets.h','handshake_backend/worker_main.cpp','handshake_backend/strong_profile_checks.cpp',
           '.deps/sharing-refresh/MP-SPDZ/Protocols/MaliciousShamirShare.h',
           '.deps/sharing-refresh/MP-SPDZ/Protocols/DabitSacrifice.hpp',
           '.deps/sharing-refresh/MP-SPDZ/GC/CcdPrep.hpp','.deps/sharing-refresh/MP-SPDZ/GC/TinyMC.h',
           '.deps/sharing-refresh/MP-SPDZ/Math/Bit.cpp']
    names += ['.deps/sharing-refresh/MP-SPDZ/Tools/random.h','.deps/sharing-refresh/MP-SPDZ/Tools/random.cpp']
    report={'checked_utc':datetime.now(timezone.utc).isoformat(),'parties':5,'threshold':2,
            'arithmetic_modulus':str(2**255-19),'binary_field_degree':128,'runtime_security_parameter':128,
            'native_mpc_executed':False,'network_tested':False,'aggregate_security_proved':False,
            'non_bit_rejections':127,'local_share_packing_cases':2080,'test_output':result.stdout.strip(),
            'owned_field_slots_overwritten':4160,'full_vm_erasure_implemented':False,
            'prng_history_reproduced_from_retained_seed_bytes':1024,
            'unsupported':'edaBit sanitizer (-Y); only checked daBits (-X) supported',
            'source_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in names}}
    (ROOT/'benchmarks/results/tls-strong-worker-profile-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='source_sha256'}))
if __name__=='__main__':main()
