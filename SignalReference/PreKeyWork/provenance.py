#!/usr/bin/env python3
"""Verify actual native prekey reference sources and full locked dependency set."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def packages(p):return [dict(re.findall(r'^(name|version|checksum) = "([^"]*)"',s,re.M)) for s in p.read_text().split('[[package]]')[1:]]
def main():
 pins=json.loads((ROOT/'SignalReference/pins.json').read_text())['libsignal'];base=ROOT/'.deps/libsignal-v0.106.1'
 for n in ['Cargo.lock','rust/core/src/curve.rs','rust/core/src/curve/curve25519.rs']:
  assert sha(base/n)==pins['files'][n],n
 actual=packages(base/'Cargo.lock');used=packages(WORK/'Oracle/Cargo.lock')
 for p in used:
  if p['name']!='signal-prekey-oracle':assert p in actual,p
 names=['rust/protocol/src/state/bundle.rs','rust/protocol/src/session.rs','rust/protocol/src/kem.rs','rust/protocol/src/identity_key.rs','rust/protocol/src/storage/traits.rs','rust/core/src/curve.rs','rust/core/src/address.rs']
 report={'reference_commit':pins['commit'],'reference_tag':pins['tag'],'computational_rust_source_edits':[],
  'actual_source_sha256':{n:sha(base/n) for n in names},'oracle_dependency_count_matching_actual_lock':len(used)-1,
  'oracle_package_identity':used,'oracle_source_sha256':sha(WORK/'Oracle/src/main.rs'),'oracle_lock_sha256':sha(WORK/'Oracle/Cargo.lock'),
  'rustc':subprocess.check_output(['rustc','+nightly-2025-09-24','--version'],text=True).strip(),
  'build_flags':['--offline','--ignore-rust-version','--locked'],'feature_profiles':{'base':'actual default protocol features, Kyber1024tag8','all':'actual kyber768 + mlkem1024 features, tags7/8/10'},
  'msrv_boundary':'Actual source compiles unchanged on installed nightly with Cargo MSRV check ignored; source declares1.93.1.',
  'actual_native_apis':['core::curve::PublicKey::deserialize/serialize','core::DeviceId::try_from(u32)','kem::PublicKey::deserialize/serialize','PreKeyBundle::try_from(PreKeyBundleContent)','process_prekey_bundle'],
  'native_process_boundary':'Real process_prekey_bundle runs through external Sending trust and both real signature checks. A fixture SessionStore intentionally returns an error at load_session, the first operation after validation. Code0 means prefix reached that sentinel, not full process success.',
  'policy_boundary':'Fixture IdentityKeyStore models all three Result<bool> outcomes and asserts identity plus Direction::Sending; this is not an implemented trust policy. Shared adapter accepts that external result separately, bound to canonical identity/address by caller.',
  'typed_input_boundary':'The actual constructor accepts already typed keys/device. EC/KEM/device raw decoding is checked independently; local adapter code32 signifies unsatisfied typed-input precondition, with decoder errors separate. No universal raw-parser error ordering is asserted.',
  'missing_order':['registration_id','device_id','signed_pre_key_id','signed_pre_key_public','signed_pre_key_signature','kyber_pre_key_id','kyber_pre_key_public','kyber_pre_key_signature','identity_key'],
  'optional_pair':'pre_key_id.zip(pre_key_public), mismatched presence discarded','ids':'registration and all prekey IDs retain full u32; DeviceId accepts1..127',
  'key_normalization':'EC tag5 minimum33 bytes, trailing bytes discarded on serialize; KEM supported tag and exact1185/1569 bytes, no coefficient validation in deserialize',
  'actual_aeneas_refinement':False,'native_mpc_executed':False}
 (WORK/'source-provenance.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
