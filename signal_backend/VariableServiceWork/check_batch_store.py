#!/usr/bin/env python3
import hashlib,json,subprocess
from pathlib import Path
here=Path(__file__).resolve().parent;root=here.parents[1];binary=root/'.deps/signal-batch-store-checks'
subprocess.run(['clang++','-std=c++17','-O1','-g','-fsanitize=address,undefined',str(here/'batch_store_checks.cpp'),'-o',str(binary)],check=True)
result=subprocess.check_output([str(binary)],text=True).strip();assert result=='156 staged batch-store checks passed'
subprocess.run(['python3',str(root/'signal_backend/RecoveryWork/check_transaction.py')],check=True)
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
files=[here/x for x in ['VariableSendStore.h','VariableSendBatch.h','VariableShape.h','batch_store_checks.cpp','check_batch_store.py','BATCH_STORE.md']]
report=dict(passed=True,ASAN_UBSAN=True,checks=156,batch_sizes=[1,2,4,8],reserve_callbacks_per_batch=1,commit_callbacks_per_batch=1,independent_conversation_completion=True,partial_install_failure_no_outputs=True,poison_all_on_uncertainty=True,move_only_weak_lease_tickets=True,default_mock_profiles=32,prior_checkpoint_checks=12,native_MPC=False,durable_account_callback_binding=False,runtime_retirement=False,normal_recovery_admission=False,source_sha256={str(p.relative_to(root)):sha(p)for p in files},binary_sha256=sha(binary))
(here/'batch-store-report.json').write_text(json.dumps(report,indent=2)+'\n');print(result)
