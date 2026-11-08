#!/usr/bin/env python3
import hashlib,json,subprocess,tempfile
from pathlib import Path
here=Path(__file__).resolve().parent;root=here.parents[1]
for name,src in [('signal-checkpoint-order-check',here/'transaction_check.cpp'),('signal-variable-store-checks',root/'signal_backend/VariableServiceWork/store_checks.cpp')]:
 subprocess.run(['clang++','-std=c++17','-O1','-g','-fsanitize=address,undefined',str(src),'-o',str(root/'.deps'/name)],check=True)
result=subprocess.check_output([str(root/'.deps/signal-checkpoint-order-check')],text=True).strip();assert result=='12 private-store checkpoint ordering checks passed'
with tempfile.TemporaryDirectory(prefix='signal-store-check-')as d:
 result2=subprocess.check_output([str(root/'.deps/signal-variable-store-checks'),d],text=True).splitlines()[-1];assert result2=='32 public mock store profiles passed'
files=[here/x for x in ['check_transaction.py','transaction_check.cpp','STORE_CHECKPOINT.md']]+[root/'signal_backend/VariableServiceWork'/x for x in ['VariableSendStore.h','VariableShape.h','store_checks.cpp']]
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
report=dict(passed=True,ASAN_UBSAN=True,checkpoint_ordering_checks=12,default_mock_profiles=32,scope='Host transaction hook ordering/binding only, no actual durable archive/certificate/private canonical integration',normal_path_tombstone_unchanged=True,normal_provider_checkpoint_admission=False,atomic_outbox_restart=False,source_sha256={str(p.relative_to(root)):sha(p)for p in files})
(here/'transaction-report.json').write_text(json.dumps(report,indent=2)+'\n');print(result);print(result2)
