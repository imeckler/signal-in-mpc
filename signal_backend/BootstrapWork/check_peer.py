#!/usr/bin/env python3
"""Actual Rust recipient/reference test; no native sender acceptance claim."""
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 binary=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-bootstrap-peer-oracle';rows=[]
 for seed in [3027,3031,3049,3061]:
  reference=subprocess.run([str(binary)],input=json.dumps(dict(mode='reference',seed=seed))+'\n',capture_output=True,text=True,check=True)
  result=json.loads(reference.stdout);assert result['actual_Rust_reference_only']and not result['native_MPC']and not result['phase_override'];assert len(result['rows'])==2
  # Separate fresh recipient: no host sender runs in this IPC process. Wires
  # below are public Rust-reference controls, later replaced by MPC outputs.
  commands=[dict(mode='init',seed=seed)]
  for row in result['rows']:
   commands += [dict(mode='check',wire=row['wire']),dict(mode='check',wire=row['wire'])]
  process=subprocess.run([str(binary)],input=''.join(json.dumps(x)+'\n'for x in commands),capture_output=True,text=True,check=True)
  replies=list(map(json.loads,process.stdout.splitlines()));assert len(replies)==5
  assert replies[0]==result['fixture']
  for index in range(2):
   good,bad=replies[1+2*index:3+2*index];expected=result['rows'][index]
   assert good['accepted']and good['plaintext']==expected['plaintext']and good['one_time_consumed']and good['sender_identity_matches']
   assert not bad['accepted']and bad['error']=='duplicate'and bad['session_record_preserved']and bad['one_time_presence_preserved']and bad['trusted_identity_preserved']
   assert expected['tamper_rejected_preserved']and expected['replay_rejected_preserved']
  rows.append(dict(seed=seed,wire_bytes=[len(bytes.fromhex(x['wire']))for x in result['rows']],plaintext_bytes=[len(bytes.fromhex(x['plaintext']))for x in result['rows']],phase_override=False,actual_prekey_decryptions=2,prekey_consumption_and_trusted_sender_checked=True,MAC_tamper_and_replay_preserve_session_record=True,independent_recipient_IPC_passed=True))
  print('actual bootstrap recipient seed',seed,'passed',flush=True)
 report=dict(passed=True,native_MPC=False,Rust_sender_only_in_reference_control=True,private_production_sender_host_execution=False,cases=rows,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in [pathlib.Path(__file__),ROOT/'signal_backend/Oracle/src/bin/signal-bootstrap-peer-oracle.rs',ROOT/'signal_backend/Oracle/Cargo.lock',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/session.rs',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/ratchet.rs',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/session_management.rs',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/protocol.rs']},oracle_sha256=sha(binary))
 (HERE/'peer-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
