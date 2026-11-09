#!/usr/bin/env python3
"""PUBLIC fixture integration; no normal provider/private runtime admission."""
import hashlib,json,shlex,subprocess,tempfile
from pathlib import Path
here=Path(__file__).resolve().parent;root=here.parents[1];binary=root/'.deps/signal-account-archive-check';oracle=root/'.deps/signal-established-send-oracle-target/debug/signal-recovery-send-record-oracle'
flags=shlex.split(subprocess.check_output(['pkg-config','--cflags','--libs','openssl'],text=True))
subprocess.run(['clang++','-std=c++17','-O1','-g','-fsanitize=address,undefined',str(here/'account_archive_check.cpp'),*flags,'-o',str(binary)],check=True)
fixtures=[]
for conv,seed in enumerate([19,23]):
 f=json.loads(subprocess.check_output([str(oracle)],input=json.dumps(dict(seed=seed,account_seed=65000,recipient_uuid='ffeeddcc-bbaa-9988-7766-55443322110'+str(conv),plaintext=(b'Public recovery ciphertext fixture'.ljust(79,b'\0')+b'\x80').hex()))+'\n',text=True))
 fixtures.append(f['rows'][0])
assert fixtures[0]['account_identity']==fixtures[1]['account_identity']
assert fixtures[0]['sender_selected_after']!=fixtures[1]['sender_selected_after']
with tempfile.TemporaryDirectory(prefix='signal-account-restart-')as d:
 p=Path(d);(p/'fixture').mkdir();(p/'durable').mkdir()
 for i,row in enumerate(fixtures):
  assert row['actual_new_DH_message_decrypt'] and row['canonical_record_projection_reload']
  assert len(bytes.fromhex(row['sender_selected_after']))==525
  (p/'fixture'/f'before-record{i}').write_bytes(bytes.fromhex(row['sender_record_before']))
  (p/'fixture'/f'before-state{i}').write_bytes(bytes.fromhex(row['sender_selected_before']))
  (p/'fixture'/f'record{i}').write_bytes(bytes.fromhex(row['sender_record_after']))
  (p/'fixture'/f'state{i}').write_bytes(bytes.fromhex(row['sender_selected_after']))
  raw=bytes.fromhex(row['input']);n=int.from_bytes(raw[718:720],'big');(p/'fixture'/f'wire{i}').write_bytes(raw[720:720+n])
 (p/'fixture'/'identity').write_bytes(bytes.fromhex(fixtures[0]['account_identity']))
 result=subprocess.check_output([str(binary),str(p/'durable'),str(p/'fixture')],text=True).strip()
 assert result=='133 durable account-section/outbox checks passed'
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
files=[here/x for x in ['LocalAccountCheckpoint.h','EvidenceCodec.h','AccountSchemaV1.h','Evidence.h','OwnShareBox.h','CiphertextStore.h','CertifiedArchiveGate.h','account_archive_check.cpp','check_account_archive.py','ACCOUNT_ARCHIVE.md','OutboxDisposition.h']]+[root/'signal_backend/Oracle/src/bin/signal-recovery-send-record-oracle.rs',root/'signal_backend/Oracle/src/session_projection.rs',root/'signal_backend/Oracle/src/session_send_projection.rs']
report=dict(passed=True,checks=133,ASAN_UBSAN=True,actual_pinned_sender_RecordStructure_and_wire=True,actual_peer_decrypts_both_outboxes=True,two_independent_same_identity_conversations=True,own_full_GF128_evaluation_bytes=True,AES256SIV=True,immutable_ciphertext_fsync=True,actual_Ed25519_reserve_commit_certificates=True,state_commit_independent_of_delivery=True,earlier_unacknowledged_outbox_retained=True,no_remote_ack_required=True,observed_higher_unresolved_reservation_rejected=True,phase_schema_binding=True,inner_section_encoding_digest_bound=True,child_exit_without_destructors=True,reopened_fresh_challenge_highwater=True,all_sections_exact_after_reload=True,unrelated_conversation_retained=True,old_checkpoint_rejected=True,altered_certificate_rejected=True,normal_bootstrap_sections_dummy=True,selected_service_input_only_sender136=True,native_private_MPC_restore=False,actual_store_checkpoint_callbacks_bound=False,reserve_precedes_actual_oracle_encryption=False,private_canonical_codec_invoked_in_this_test=False,full_outbox_retry_policy=False,worker_retirement_integrated=False,normal_provider_admitted=False,scope='Public actual sender record/ciphertext pair archived as disposable local polynomial evaluations; real local archive/certificate/restart integration, not complete private runtime recovery',source_sha256={str(p.relative_to(root)):sha(p)for p in files},binary_sha256=sha(binary),oracle_binary_sha256=sha(oracle))
(here/'account-archive-report.json').write_text(json.dumps(report,indent=2)+'\n');print(result)
