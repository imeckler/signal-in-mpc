#!/usr/bin/env python3
"""ASAN/UBSAN public mock host-store checks, not native MPC evidence."""
import hashlib,json,subprocess,tempfile
from pathlib import Path
from shape import VariableShape
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def main():
 binary=ROOT/'.deps/variable-store-checks'
 subprocess.run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-fsanitize=address,undefined','-O1','-g',str(HERE/'store_checks.cpp'),'-o',str(binary)],check=True)
 with tempfile.TemporaryDirectory(prefix='private-conversation-store-') as directory:output=subprocess.check_output([str(binary),directory],text=True)
 expected=[VariableShape(cert,plain,chunk,addr).descriptor for cert in [1,127,128,1024] for plain in [0,1024] for chunk in [0,1] for addr in [0,1]]
 assert output.splitlines()[:-1]==expected
 files=[Path(__file__),HERE/'store_checks.cpp',HERE/'VariableSendStore.h',HERE/'VariableShape.h',HERE/'shape.py',ROOT/'signal_backend/PersistentSendFence.h']
 report={'public_mock_profiles':32,'two_state_and_request_id_transitions_per_profile':True,'payload_timestamp_overlay':True,
  'pending_stale_ticket_runtime_failure_result_shape_and_restart_rejections':True,'asan_ubsan_passed':True,
  'native_mpc_executed':False,'recoverable_durable_state':False,'byzantine_durability':False,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
 (HERE/'store-report.json').write_text(json.dumps(report,indent=2)+'\n');print(output.splitlines()[-1])
if __name__=='__main__':main()
