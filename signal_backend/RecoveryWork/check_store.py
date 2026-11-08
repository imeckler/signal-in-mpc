#!/usr/bin/env python3
"""Actual encrypted local-file persistence; no Signal provider restore admission."""
import hashlib,json,shlex,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];BIN=ROOT/'.deps/signal-ciphertext-store-check'
flags=shlex.split(subprocess.check_output(['pkg-config','--cflags','--libs','openssl'],text=True))
subprocess.run(['clang++','-std=c++17','-O1','-g','-fsanitize=address,undefined',str(HERE/'store_check.cpp'),*flags,'-o',str(BIN)],check=True)
text=subprocess.check_output([str(BIN)],text=True).strip();assert text=='12 encrypted own-share persistence checks passed'
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest();files=[Path(__file__),HERE/'CiphertextStore.h',HERE/'store_check.cpp',HERE/'OwnShareBox.h',HERE/'Evidence.h']
report=dict(passed=True,ASAN_UBSAN_checks=12,child_process_durable_save_then_exit_without_cleanup=True,parent_reopen_authenticated_own_evaluation_roundtrip=True,immutable_idempotent_content_addressed_ciphertext=True,corruption_wrong_digest_wrong_size_symlink_and_conflicting_overwrite_refused=True,plaintext_or_local_evaluations_written_to_disk=False,fsync_file_and_directory_before_success=True,full_Signal_schema=False,private_share_readmission=False,complete_4of5_phase_and_recovery_protocol=False,secure_Signal_restore=False,production_provider_admitted=False,platform_honest_durability_assumptions=True,binary_sha256=sha(BIN),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
(HERE/'store-report.json').write_text(json.dumps(report,indent=2)+'\n');print(text)
