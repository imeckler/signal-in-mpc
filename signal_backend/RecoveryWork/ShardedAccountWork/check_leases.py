#!/usr/bin/env python3
"""Public signed-Commit/boot/cell-generation helper; not registry/native ACK test."""
import hashlib,json,pathlib,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[2]
with tempfile.TemporaryDirectory(prefix='shard-leases-',dir=ROOT/'.deps')as tmp:
 binary=pathlib.Path(tmp)/'checks';subprocess.run(['c++','-std=c++20','-O1','-g','-fsanitize=address,undefined','-I/opt/homebrew/opt/openssl@3/include',str(HERE/'lease_checks.cpp'),'-L/opt/homebrew/opt/openssl@3/lib','-lcrypto','-o',str(binary)],check=True)
 output=subprocess.check_output([str(binary)],text=True);assert output.strip()=='completion leases passed 41 checks'
 report=dict(passed=True,checks=41,sanitizers=['ASAN','UBSAN'],actual_signatures=True,unequal_conversation_activity=True,stale_ACK_after_reuse=True,private_request_IDs_opened=False,registry_integration_test=False,native_MPC=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [pathlib.Path(__file__),HERE/'lease_checks.cpp',HERE/'ResponseLeases.h']})
 (HERE/'lease-report.json').write_text(json.dumps(report,indent=2)+'\n');print(output.strip())
