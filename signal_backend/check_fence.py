#!/usr/bin/env python3
"""Public crash/concurrency tests of the temporary fail-closed send fence."""
import hashlib,json,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];HERE=ROOT/'signal_backend'
def main():
 binary=ROOT/'.deps/signal-fence-checks'
 subprocess.run(['c++','-std=c++17','-Wall','-Wextra','-Werror','-fsanitize=address,undefined',
  '-O1','-g',str(HERE/'fence_checks.cpp'),'-o',str(binary)],check=True)
 with tempfile.TemporaryDirectory(prefix='signal-fence-') as directory:
  output=subprocess.check_output([str(binary),directory],text=True)
 report={'temporary_fail_closed_boundary':True,'recoverable_shared_state':False,'byzantine_durability':False,
  'cases':['child crash after fsynced reserve','concurrent same-slot create','normal restart','runtime failure then retry'],
  'all_reuse_refused':True,'asan_ubsan_passed':True,'no_secret_or_share_serialization':True,
  'assumptions':['Stable opaque session-slot mapping is authoritative; an old state cannot be relabeled to a fresh slot.',
    'Local filesystem honors fsync and tombstones are not deleted/rolled back.'],
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [
    Path(__file__),HERE/'PersistentSendFence.h',HERE/'fence_checks.cpp',HERE/'EstablishedSendStore.h']},
  'output':output.strip()}
 (HERE/'fence-report.json').write_text(json.dumps(report,indent=2)+'\n');print(output.strip())
if __name__=='__main__':main()
