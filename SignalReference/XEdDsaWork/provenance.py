#!/usr/bin/env python3
"""Check oracle source identity against accepted pins and locked package checksums."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def packages(path):
 return [dict(re.findall(r'^(name|version|checksum) = "([^"]*)"',s,re.M)) for s in path.read_text().split('[[package]]')[1:]]
def main():
 pins=json.loads((ROOT/'SignalReference/pins.json').read_text());checked={}
 for entry,names in [(pins['libsignal'],['rust/core/src/curve.rs','rust/core/src/curve/curve25519.rs','Cargo.lock']),
   (pins['signal_dependencies']['curve25519-dalek@5.0.0'],['src/scalar.rs']),
   (pins['signal_dependencies']['sha2@0.11.0'],['src/consts.rs','src/lib.rs','Cargo.toml'])]:
  base=(ROOT/'SignalReference'/entry['source_directory']).resolve()
  for name in names:
   p=base/name;actual=sha(p);assert actual==entry['files'][name],str(p)
   checked[str(p.relative_to(ROOT))]=actual
 oracle=packages(WORK/'Oracle/Cargo.lock');locked=packages(ROOT/'.deps/libsignal-v0.106.1/Cargo.lock')
 for row in oracle:
  if row['name']!='signal-xeddsa-oracle':assert row in locked,row
 report={'reference':pins['libsignal']['commit'],'tag':pins['libsignal']['tag'],'checked_existing_pin_files':checked,
  'oracle_packages_matching_actual_lock':len(oracle)-1,'oracle_dependency_identity':oracle,
  'oracle_manifest_sha256':sha(WORK/'Oracle/Cargo.toml'),'oracle_lock_sha256':sha(WORK/'Oracle/Cargo.lock'),
  'oracle_main_sha256':sha(WORK/'Oracle/src/main.rs'),'actual_source_edits':[],
  'rustc':subprocess.check_output(['rustc','+nightly-2025-09-24','--version'],text=True).strip(),
  'build_flags':['--offline','--ignore-rust-version','--locked'],
  'rust_version_note':'Pinned libsignal declares1.93.1. Installed nightly is used with Cargo MSRV gate ignored; computational sources remain unchanged and compiled successfully.',
  'aeneas_generated_reference':False,'trusted_rust_wrapper_replacement':False,
  'source_audit':{'verifier':'rust/core/src/curve/curve25519.rs:129-175',
   'length_wrapper':'rust/core/src/curve.rs:134-151','prekey_policy_caller':'rust/protocol/src/session.rs:220-254',
   'montgomery_recovery':'curve25519-dalek5/src/montgomery.rs:239-268',
   'scalar_compatibility':'Clear signature bit511, reject s bits253/254; reduce remaining253-bit s modulo ell. Do not impose canonical s<ell.',
   'message_domain':'Actual serialized typed signed-prekey and KEM public keys; current adapter accepts exact caller-supplied message bytes and does not enforce bundle/identity policy.',
   'low_order':'Actual Montgomery recovery accepts some small-order points; no added subgroup rejection policy. x=0 compresses with sign0 even if requested sign1.'}}
 (WORK/'source-provenance.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
