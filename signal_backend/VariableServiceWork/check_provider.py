#!/usr/bin/env python3
"""Focused host lifecycle API test; no openings or native/MPC claim."""
import hashlib,json,subprocess,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def main():
 with tempfile.TemporaryDirectory(prefix='signal-private-provider-')as temp:
  binary=Path(temp)/'provider-checks';slots=Path(temp)/'slots';slots.mkdir()
  command=['clang++','-std=c++17','-Wall','-Wextra','-Werror','-fsanitize=address,undefined','-I',str(HERE),str(HERE/'provider_checks.cpp'),'-o',str(binary)]
  subprocess.run(command,cwd=ROOT,check=True);result=subprocess.run([str(binary),str(slots)],cwd=ROOT,text=True,capture_output=True,check=True)
  assert result.stdout=='39 failclosed provider transitions; two-send lifecycle passed\n' and not result.stderr,result.stderr
 files=[Path(__file__),HERE/'PrivateProvider.h',HERE/'provider_checks.cpp',HERE/'VariableSendStore.h',HERE/'VariableShape.h',ROOT/'signal_backend/PersistentSendFence.h']
 report={'host_mock_lifecycle_test_passed':True,'sanitizers':['ASAN','UBSAN'],'rejection_transition_checks':39,'successful_two_send_lifecycle':True,
  'connection_allocator_override_tested':True,'override_used_in_eval_and_returned_id':True,'ordinary_send_uses_committed_next_id':True,
  'covered':['upgrade must precede authenticated upgrade_complete','credentials consumed once','send blocked before HTTPaccept and while response pending','matching response ticket required','callback/dimension failures poison state','reentrant completion/close cannot resurrect provider','stable slot restart refusal'],
  'no_open_or_plaintext_import_api':True,'native_MPC_evaluation_tested_here':False,'authenticated_bootstrap_implemented':False,'recoverable_persistence_implemented':False,
  'upstream_computed_validity_propagation':'Owning TLS registry retains credential/state/per-input validity and gates outputs; this wrapper supplies no correctness flags.',
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files}}
 (HERE/'provider-report.json').write_text(json.dumps(report,indent=2)+'\n');print(result.stdout,end='')
if __name__=='__main__':main()
