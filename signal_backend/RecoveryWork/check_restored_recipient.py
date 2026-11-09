#!/usr/bin/env python3
"""Public disposable actual serialized Bob-state replay/next-text fixture."""
import hashlib,json,pathlib,subprocess,uuid
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent
TARGET=ROOT/'.deps/signal-established-send-oracle-target/debug'
def main():
 receiver=TARGET/'signal-restored-recipient-oracle';account=TARGET/'signal-account-snapshot-oracle';sealed=TARGET/'signal-established-send-oracle'
 def ask(binary,values):
  return [json.loads(x)for x in subprocess.check_output([str(binary)],input=''.join(json.dumps(v)+'\n'for v in values),text=True).splitlines()]
 body='Restored conversation: hello again!';timestamp=1900000000019
 padded=ask(receiver,[dict(mode='text',body=body.encode().hex(),timestamp=timestamp)])[0]['padded']
 identity_fixture=ask(sealed,[dict(mode='sealed',seed=19,inner='')])[0]
 legacy=(b'E'*79+b'\x80').hex();rows=ask(account,[dict(seed=19,steps=3,alice_secret=identity_fixture['sender_secret'],bob_secret=identity_fixture['recipient_secret'],plaintext=legacy,plaintexts=[legacy,legacy,padded])])[0]['rows']
 assert rows[0]['account_identity'][:64]==identity_fixture['sender_secret'] and rows[0]['peer_identity'][:64]==identity_fixture['recipient_secret']
 assert rows[0]['account_identity'][66:]==bytes.fromhex(identity_fixture['input'])[64:96].hex()
 from account_fixture import fixture
 assert rows[:2]==fixture()['states'][0]['rows'][:2], 'capture/recipient baseline mismatch'
 def inner(row):
  encoded=bytes.fromhex(row['input'])[-259:];assert encoded[0]==255
  return encoded[3:3+int.from_bytes(encoded[1:3],'big')].hex()
 old,new=inner(rows[1]),inner(rows[2]);envelopes=ask(sealed,[dict(mode='sealed',seed=19,inner=x)for x in [old,new]])
 sender='00112233-4455-6677-8899-aabbccddeeff';recipient='ffeeddcc-bbaa-9988-7766-554433221100'
 init=dict(mode='init',slot=0,session_record=rows[1]['record_after'],identity_key_pair=rows[0]['peer_identity'],sender_uuid=sender,recipient_uuid=recipient,sender_device=1,recipient_device=1,registration_id=2)
 answers=ask(receiver,[init,dict(slot=0,wire=old),dict(slot=0,wire=new),dict(slot=0,wire=new)])
 assert answers[0]=={'initialized':True}
 assert answers[1]=={'accepted':False,'error':'duplicate','state_preserved':True}
 assert answers[2]==dict(accepted=True,body=body,timestamp=timestamp,padded_bytes=80)
 assert answers[3]==answers[1]
 # Verify both SS envelopes using the actual pinned implementation too.
 decoded=ask(sealed,[dict(mode='sealed_decrypt',wire=e['wire'],recipient_secret=e['recipient_secret'],root_public=e['root_public'])for e in envelopes])
 assert [d['inner']for d in decoded]==[old,new] and all(d['certificate_valid']for d in decoded)
 fixture=dict(public_disposable_fixture_only=True,client_uuid=sender,client_password_hex=b'0123456789abcdefghijkl'.hex(),conversations=[dict(slot=0,sender_uuid=sender,recipient_uuid=recipient,access_key=hashlib.sha256(b'uak-19').digest()[:16].hex(),device_id=1,registration_id=2,recipient_secret=envelopes[0]['recipient_secret'],root_public=envelopes[0]['root_public'],bob_session_record=init['session_record'],bob_identity_key_pair=init['identity_key_pair'],events=[dict(kind='duplicate',timestamp=timestamp,expected_inner=old,sealed_wire=envelopes[0]['wire']),dict(kind='text',timestamp=timestamp,body=body,sealed_wire=envelopes[1]['wire'])])])
 (HERE/'restored-recipient-fixture.json').write_text(json.dumps(fixture,indent=2)+'\n')
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 files=[pathlib.Path(__file__),ROOT/'signal_backend/Oracle/src/bin/signal-restored-recipient-oracle.rs',ROOT/'signal_backend/Oracle/src/bin/signal-account-snapshot-oracle.rs',HERE/'restored-recipient-fixture.json',HERE/'account_fixture.py']
 report=dict(passed=True,public_disposable_fixture_only=True,target='libsignal 904c8dc',actual_serialized_session_reload=True,exact_first_two_capture_rows=True,actual_duplicate_rejection_preserves_record=True,actual_next_text_body_timestamp=True,actual_sealed_sender_decrypt_and_certificate=True,duplicate_next_duplicate_cases=3,native_MPC=False,whole_account_activation=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},binary_sha256={p.name:sha(p)for p in [receiver,account,sealed]})
 (HERE/'restored-recipient-report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: actual restored Bob duplicate / next Content text / duplicate, SS envelopes verified')
if __name__=='__main__':main()
