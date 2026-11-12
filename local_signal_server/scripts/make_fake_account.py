#!/usr/bin/env python3
"""make_fake_account.py LSS_ACCOUNT_JSON OUT_JSON: an account file in real_signal/register's exact
format (`account_json` in real_signal/register/src/main.rs) from a LOCAL test account, so that the
converter and the real-test launcher can be exercised against the local server. Keeps the local
account's one-time prekeys (the local server hands them out); a real registration has none."""
import base64, json, os, secrets, sys

src = json.load(open(sys.argv[1]))
fake = {
    "WARNING": "FAKE account in the real registration tool's format, made from a LOCAL test account. Local server only.",
    "environment": "local-test",
    "name": src["name"], "number": src["number"], "aci": src["aci"], "pni": src["pni"], "device_id": 1, "username": None,
    "password": src["password"], "recovery_password": base64.b64encode(secrets.token_bytes(32)).decode(),
    "registration_id": src["registration_id"], "pni_registration_id": src["pni_registration_id"],
    "profile_key": src["profile_key"], "access_key": src["access_key"],
    "unrestricted_unidentified_access": True,
    "aci_identity_key_pair": src["aci_identity_key_pair"], "aci_identity_key": src["aci_identity_key"],
    "pni_identity_key_pair": src["pni_identity_key_pair"],
    "sender_certificate": src["sender_certificate"],
    "prekeys": src["prekeys"],
    "signed_prekeys": src["signed_prekeys"], "kyber_prekeys": src["kyber_prekeys"],
    "pni_signed_prekeys": {}, "pni_kyber_prekeys": {},
    "peers": [], "sessions": {}, "identities": {},
}
real_fields = ["WARNING", "environment", "name", "number", "aci", "pni", "device_id", "username", "password", "recovery_password",
               "registration_id", "pni_registration_id", "profile_key", "access_key", "unrestricted_unidentified_access",
               "aci_identity_key_pair", "aci_identity_key", "pni_identity_key_pair", "sender_certificate", "prekeys",
               "signed_prekeys", "kyber_prekeys", "pni_signed_prekeys", "pni_kyber_prekeys", "peers", "sessions", "identities"]
assert sorted(fake) == sorted(real_fields)
with open(sys.argv[2], 'w') as f:
    json.dump(fake, f, indent=2)
os.chmod(sys.argv[2], 0o600)
print('wrote', sys.argv[2], 'fields', len(fake))
