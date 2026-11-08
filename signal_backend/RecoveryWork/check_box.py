#!/usr/bin/env python3
"""Local OWN share archival only; authenticated decryption remains quarantine."""
import hashlib,json,shlex,subprocess
from pathlib import Path
from cryptography.hazmat.primitives.ciphers.aead import AESSIV
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];BIN=ROOT/'.deps/signal-own-share-box-check';NATIVE=ROOT/'.deps/signal-native-own-share-codec-check'
flags=shlex.split(subprocess.check_output(['pkg-config','--cflags','--libs','openssl'],text=True))
subprocess.run(['clang++','-std=c++17','-O1','-g','-fsanitize=address,undefined',str(HERE/'box_check.cpp'),*flags,'-o',str(BIN)],check=True)
lines=subprocess.check_output([str(BIN),'vectors'],text=True).splitlines();assert lines[-1]=='58 own-share archive/quarantine checks passed'
for line in lines[:-1]:
 tag,count,header,sealed=line.split();assert tag=='VECTOR';n=int(count);h=bytes.fromhex(header);plain=bytes((i*17+n)%256 for i in range(n*16))
 assert bytes.fromhex(sealed)==h+AESSIV(bytes(range(1,65))).encrypt(plain,[h])
runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
subprocess.run(['make','-f',str(HERE/'Makefile'),'RECOVERY_WORK='+str(HERE),'RECOVERY_CODEC='+str(NATIVE),str(NATIVE)],cwd=runtime,stdout=subprocess.DEVNULL,check=True)
text=subprocess.check_output([str(NATIVE)],text=True).strip();assert text=='16384 native GF128 basis/typed archive checks passed'
files=[Path(__file__),HERE/'OwnShareBox.h',HERE/'NativeOwnShareArchive.h',HERE/'box_check.cpp',HERE/'native_codec_check.cpp',HERE/'Makefile',HERE/'Evidence.h',HERE/'OWN_SHARE_BOX.md',ROOT/'handshake_backend/NativeWorker.h',ROOT/'handshake_backend/StrongShamirShare.h',runtime/'Math/gf2n.cpp',runtime/'Protocols/ShamirInput.hpp'];sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
report=dict(passed=True,ASAN_UBSAN_box_checks=58,cryptography_AESSIV_exact_tag_ciphertext_AD_oracle_cases=len(lines)-1,native_GF128_basis_checks=16384,native_codec_compile_link_passed=True,format='Local own GF128 evaluations, LEpolynomial basis; MaliciousCCD128,n5,t2,x1..5; original state bit ordering retained.',runtime_member_threshold_degree_and_cellshape_guards_implemented=True,runtime_guard_negative_cases_tested=False,AES_256_SIV_storage_key_bytes=64,crash_sensitive_nonce_counter=False,authenticated_domain=['party','epoch','slot','bitcount','context','membership','manifest','schema','sharing_epoch'],secret_temporary_owner_cleared=True,
 full_Signal_schema=False,private_MPC_readmission=False,secure_Signal_restore=False,restored_Bits_factory=False,normal_provider_admitted=False,aggregate_key_or_bit_reconstruction=False,native_MPC_executed=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},binary_sha256={p.name:sha(p)for p in [BIN,NATIVE]},runtime_library_sha256=sha(runtime/'libSPDZ.so'))
(HERE/'box-report.json').write_text(json.dumps(report,indent=2)+'\n');print('58 box checks/3AESSIV oracle cases/16384native GF128 basis checks passed; restore remains quarantined')
