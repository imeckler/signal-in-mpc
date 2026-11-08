#!/usr/bin/env python3
"""Public control-plane candidate only: actual signatures + durable vote evidence."""
import hashlib,json,shlex,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];BINARY=ROOT/'.deps/signal-recovery-evidence-check'
flags=shlex.split(subprocess.check_output(['pkg-config','--cflags','--libs','openssl'],text=True))
subprocess.run(['clang++','-std=c++17','-O1','-g','-fsanitize=address,undefined',str(HERE/'check.cpp'),*flags,'-o',str(BINARY)],check=True)
result=subprocess.check_output([str(BINARY)],text=True).strip();assert result=='655 recovery signature/journal/intersection checks passed'
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
files=[Path(__file__),HERE/'Evidence.h',HERE/'check.cpp',HERE/'PROTOCOL.md']
report=dict(passed=True,checks=655,ASAN_UBSAN=True,actual_OpenSSL_Ed25519=True,five_distinct_member_keys=True,certificate_threshold=4,fault_bound=2,honest_quorum_intersection_exhaustive=True,quorum3_counterexample=True,close_reopen_idempotent_vote=True,actual_child_process_exit_without_cleanup=True,conflicting_vote_after_restart_refused=True,fresh_challenge_signed_highwater=True,old_challenge_tampered_status_rejected=True,torn_altered_symlink_wrong_domain_and_lock_conflicts_rejected=True,write_and_directory_fsync_before_signature=True,
 scope='Public signatures/certificate/no-double-sign/highwater evidence candidate only. No Signal/share bytes serialized or restored; no full phase-chain or recovery protocol admission.',honest_durable_journal_assumption=True,encrypted_full_state_outbox_codec=False,private_MPC_share_consistency_import=False,full_recovery_protocol=False,secure_Signal_restore=False,TLS_state_restore=False,production_provider_admitted=False,
 openssl_pkg_config_version=subprocess.check_output(['pkg-config','--modversion','openssl'],text=True).strip(),binary_sha256=sha(BINARY),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
(HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(result)
