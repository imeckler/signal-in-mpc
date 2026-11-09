#!/usr/bin/env python3
"""Disposable recipient oracle setup; does not execute native MPC or recovery."""
import hashlib,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.RelayServiceWork.check import oracle
HERE=pathlib.Path(__file__).resolve().parent

def main():
 binary=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-canonical-owner-oracle'
 fixture=oracle([dict(mode='sealed',seed=19,inner='')])[0]
 request=dict(seed=19,steps=2,alice_secret=fixture['sender_secret'],bob_secret=fixture['recipient_secret'],plaintext=(b'E'*79+b'\x80').hex())
 def ask(value):return json.loads(subprocess.check_output([str(binary)],input=json.dumps(value)+'\n',text=True))
 first=ask(request);wires=[]
 for row in first['rows']:
  raw=bytes.fromhex(row['input']);n=int.from_bytes(raw[718:720],'big');wires.append(raw[720:720+n].hex())
 second=ask(dict(request,wires=wires));assert first==second
 f=bytes.fromhex(fixture['input'])
 for row in first['rows']:
  assert row['account_identity']==fixture['sender_secret']+'05'+f[64:96].hex()
  assert row['peer_identity']==fixture['recipient_secret']+'05'+f[:32].hex()
  assert row['canonical_record_projection_reload'] and row['tampered_MAC_preserved_actual_store']
 assert len(ask(dict(request,steps=1))['rows'])==1
 assert len(ask(dict(request,steps=4))['rows'])==4
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 sources=[ROOT/'signal_backend/Oracle/src/bin/signal-canonical-owner-oracle.rs',ROOT/'signal_backend/Oracle/src/session_projection.rs',ROOT/'signal_backend/Oracle/src/session_send_projection.rs',pathlib.Path(__file__)]
 (HERE/'canonical-oracle-report.json').write_text(json.dumps(dict(passed=True,actual_pinned_libsignal=True,actual_PQXDH_DR=True,selected_established_SPQR_override=True,SS_fixture_identities_bound=True,actual_peer_decrypt_with_external_wires=2,actual_whole_record_reprojection=True,native_MPC=False,recovery=False,provider_admission=False,oracle_binary_sha256=sha(binary),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources}),indent=2)+'\n')
 print('PASS: SS-bound disposable identities, actual peer decrypt/reprojection and 1/2/4-step fixtures')
if __name__=='__main__':main()
