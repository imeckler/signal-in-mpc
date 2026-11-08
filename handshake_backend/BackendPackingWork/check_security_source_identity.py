#!/usr/bin/env python3
"""Verify inspected, unmodified security sources against authoritative archive."""
from pathlib import Path
import json,hashlib,tarfile
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
manifest=json.loads((ROOT/'benchmarks/config/dependencies.json').read_text())
archive=ROOT/'.deps/mp-spdz-v0.4.4.tar.gz';digest=hashlib.sha256(archive.read_bytes()).hexdigest()
assert digest==manifest['mp_spdz']['source_archive_sha256']
names=['GC/TinyPrep.hpp','GC/TinierShare.h','GC/TinierSharePrep.hpp','GC/TinierSharePrep.h','GC/TinyMC.h','OT/OTMultiplier.hpp','OT/OTMultiplier.h','OT/MascotMacKey.hpp','OT/MascotMacKey.h','OT/OTExtension.cpp','OT/OTExtensionWithMatrix.cpp','OT/OTExtensionWithMatrix.h','OT/OTCorrelator.hpp','OT/OTTripleSetup.cpp','OT/OTTripleSetup.h','OT/NPartyTripleGenerator.hpp','OT/NPartyTripleGenerator.h','OT/MascotParams.cpp','OT/BitMatrix.hpp','Protocols/ShuffleSacrifice.hpp','Protocols/ShuffleSacrifice.h','CONFIG']
report=dict(upstream=manifest['mp_spdz'],archive_sha256=digest,files={},revision_identity_source='authoritative manifest and archive; never parent git rev-parse')
with tarfile.open(archive) as source:
 prefix=source.getmembers()[0].name.split('/')[0]
 for name in names:
  data=source.extractfile(prefix+'/'+name).read()
  assert data==(ROOT/'.deps/tls-session-runtime/MP-SPDZ'/name).read_bytes(),name
  report['files'][name]=hashlib.sha256(data).hexdigest()
(WORK/'security-source-identity.json').write_text(json.dumps(report,indent=2)+'\n')
print('verified',len(names),'security source files against pinned archive')
