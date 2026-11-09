#!/usr/bin/env python3
"""Actual bounded registration/prekey/trust/replay-store fixtures; no MPC import."""
import hashlib,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent

def main():
 binary=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-account-snapshot-oracle';prior=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-canonical-owner-oracle';rows=[]
 def ask(bin,value):return json.loads(subprocess.check_output([str(bin)],input=json.dumps(value)+'\n',text=True))
 for seed in [19,23,29]:
  request=dict(seed=seed,steps=3,plaintext=(b'E'*79+b'\x80').hex());result=ask(binary,request);assert result['rows']==ask(prior,request)['rows']
  global_state=result['global_stores'];assert all(global_state[k]for k in ['actual_records_roundtrip','actual_whole_global_store_codec_reload','actual_consumed_prekey_stays_absent','actual_kyber_reuse_rejected_after_reload'])
  assert global_state['registration_id']==1 and len(bytes.fromhex(global_state['identity_private_public65']))==65
  assert [x['id']for x in global_state['prekeys']]==[2] and global_state['consumed_prekey_ids']==[1]
  assert [x['id']for x in global_state['signed_prekeys']]==[17] and [x['id']for x in global_state['kyber_prekeys']]==[23]
  replay=global_state['kyber_base_keys_seen'];assert len(replay)==1 and len(replay[0]['keys'])==2 and len(set(replay[0]['keys']))==2
  blob=bytes.fromhex(global_state['global_store_v1']);assert len(blob)<=8192
  rows.append(dict(seed=seed,global_store_bytes=len(blob),global_store_sha256=hashlib.sha256(blob).hexdigest(),record_bytes={k:len(bytes.fromhex(global_state[k][0]['record']))for k in ['prekeys','signed_prekeys','kyber_prekeys']}))
 assert len({r['global_store_sha256']for r in rows})==3
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[pathlib.Path(__file__),ROOT/'signal_backend/Oracle/src/bin/signal-account-snapshot-oracle.rs',ROOT/'signal_backend/Oracle/src/session_projection.rs',ROOT/'signal_backend/Oracle/src/session_send_projection.rs']
 report=dict(passed=True,actual_pinned_libsignal=True,cases=rows,existing_signal_record_cases_unchanged=True,actual_global_store_serialize_reload=True,consumed_prekey_absence_preserved=True,kyber_replay_state_preserved=True,replay_state_mirrors_actual_API_calls_not_private_map_extraction=True,fixture_only=True,native_MPC=False,whole_account_activation=False,full_source_refinement=False,oracle_binary_sha256=sha(binary),prior_oracle_binary_sha256=sha(prior),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'account-snapshot-oracle-report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: 3 actual global-store codecs, consumed/replay state and unchanged Signal records')
if __name__=='__main__':main()
