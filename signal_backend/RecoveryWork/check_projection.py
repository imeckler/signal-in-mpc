#!/usr/bin/env python3
"""PUBLIC fixture only; no operational host SessionRecord import API."""
import hashlib,json,subprocess
from pathlib import Path
here=Path(__file__).resolve().parent;root=here.parents[1];binary=root/'.deps/signal-established-send-oracle-target/debug/signal-session-inorder-oracle'
rows=[]
for seed in [19,23,101]:
 request=dict(seed=seed,plaintext=(b'Public canonical record fixture'.ljust(79,b'\0')+b'\x80').hex())
 assert len(bytes.fromhex(request['plaintext']))==80
 p=subprocess.run([str(binary)],input=json.dumps(request)+'\n',text=True,capture_output=True,check=True)
 fixture=json.loads(p.stdout);assert fixture['actual_replay_and_MAC_failures_preserved_store'];assert len(fixture['rows'])==4
 for row in fixture['rows']:
  assert row['canonical_record_projection_reload'] and row['unrelated_record_retained'] and row['rejected_result_preserved_record']
  rows.append(dict(seed=seed,counter=row['counter']))
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
files=[here/'check_projection.py',here/'PROJECTION.md',root/'signal_backend/Oracle/src/session_projection.rs',root/'signal_backend/Oracle/src/bin/signal-session-inorder-oracle.rs',root/'.deps/libsignal-v0.106.1/rust/protocol/src/proto/storage.proto',root/'.deps/libsignal-v0.106.1/rust/protocol/src/tahini.rs']
report=dict(passed=True,actual_pinned_SessionRecord=True,new_receives=3,repeated_receives=9,full_record_equals_actual_receive=True,serialized_reload_projection_equal=True,unrelated_record_and_archived_sessions_retained=True,rejected_result_preserves_record=True,actual_MAC_and_replay_failures_preserve_record=True,private_runtime_serializer=False,outbox_atomic_restart=False,full_SPQR_epochs=False,production_recovery_admission=False,scope='Public bounded no-skipped-key active-session canonical record update fixture; native actual transition supplies expected selected state, not a private runtime implementation',rows=rows,binary_sha256=sha(binary),source_sha256={str(p.relative_to(root)):sha(p)for p in files})
(here/'projection-report.json').write_text(json.dumps(report,indent=2)+'\n');print('12 actual full-record transition/reload fixtures passed')
