#!/usr/bin/env python3
import hashlib,json,shlex,subprocess
from pathlib import Path
here=Path(__file__).resolve().parent;root=here.parents[1]
binary=root/'.deps/signal-recovery-schema-check'
flags=shlex.split(subprocess.check_output(['pkg-config','--cflags','--libs','openssl'],text=True))
subprocess.run(['clang++','-std=c++17','-O1','-g','-fsanitize=address,undefined',str(here/'schema_check.cpp'),*flags,'-o',str(binary)],check=True)
result=subprocess.check_output([str(binary)],text=True).strip();assert result=='8 account schema checks passed'
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
files=[here/x for x in ['CertifiedArchiveGate.h','Evidence.h','OwnShareBox.h','schema_check.cpp','check_phase.py','PHASE_GATE.md']]
report=dict(passed=True,checks=8,ASAN_UBSAN=True,scope='Canonical full-account section capacity descriptor and exact local evaluation pack/unpack only; populated session codec and coherent projection missing',full_state_schema_implemented=False,provider_admission=False,import_retirement_integrated=False,fresh_TLS_required=True,source_sha256={str(p.relative_to(root)):sha(p)for p in files},binary_sha256=sha(binary))
(here/'schema-report.json').write_text(json.dumps(report,indent=2)+'\n');print(result)
