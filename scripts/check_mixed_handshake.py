#!/usr/bin/env python3
"""Public differential fixtures for the exported field DAG and conversion gates."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import copy
import hashlib
import json
import random
import subprocess
import tempfile
from datetime import datetime, timezone
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
from handshake_backend.field_dag import load, validate, evaluate_clear, MODULUS
from handshake_backend.mixed import reduce_masked_sum, subtract_bits


def bits(n, width):
    return [(n >> i) & 1 for i in range(width)]


def integer(b):
    return sum(x << i for i, x in enumerate(b))


def main():
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'x25519.json'
        with path.open('w') as out:
            subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), 'x25519-field'], stdout=out, check=True)
        image = load(path)
    rng = random.Random(7748)
    count = 0
    # Exhaustive accepted-mask conversion, including non-power-of-two fields.
    for p in (3, 5, 7, 11, 13, 17, 31):
        width = p.bit_length()
        for r in range(1 << width):
            _, valid = subtract_bits(bits(r, width), bits(p, width), 0, 1)
            assert valid == (r < p)
            if not valid:
                continue
            for c in range(p):
                assert integer(reduce_masked_sum(bits(r, width), bits(c, width), bits(p, width), 0, 1)) == (r+c) % p
                count += 1
    for r in [0, 1, MODULUS-1, MODULUS-2] + [rng.randrange(MODULUS) for _ in range(100)]:
        for c in [0, 1, MODULUS-1, MODULUS-2] + [rng.randrange(MODULUS)]:
            assert integer(reduce_masked_sum(bits(r,255),bits(c,255),bits(MODULUS,255),0,1)) == (r+c)%MODULUS
            count += 1
    cases = 0
    scalar = bytes.fromhex('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a')
    assert evaluate_clear(image, bits(int.from_bytes(scalar,'little'),256)+[9])[0].to_bytes(32,'little').hex() == '8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a'
    for _ in range(64):
        scalar = rng.randbytes(32)
        peer = rng.randbytes(32)
        expected = X25519PrivateKey.from_private_bytes(scalar).exchange(X25519PublicKey.from_public_bytes(peer))
        u = (int.from_bytes(peer,'little') & ((1 << 255)-1)) % MODULUS
        actual = evaluate_clear(image, bits(int.from_bytes(scalar,'little'),256)+[u])[0].to_bytes(32,'little')
        assert actual == expected
        cases += 1
    for u in (0,1):
        assert evaluate_clear(image, bits(int.from_bytes(scalar,'little'),256)+[u]) == [0]
    rejected=0
    for mutate in (lambda x:x.update(modulus='17'), lambda x:x.update(bit_inputs=[0,0]),
                   lambda x:x.update(outputs=[len(x['nodes'])]),
                   lambda x:x['nodes'].__setitem__(0,{'op':'mul','left':0,'right':0}),
                   lambda x:x['nodes'].__setitem__(0,{'op':'const','value':str(MODULUS)})):
        bad=copy.deepcopy(image); mutate(bad)
        try: validate(bad)
        except ValueError: rejected += 1
        else: raise AssertionError('malformed artifact accepted')
    report={'checked_utc':datetime.now(timezone.utc).isoformat(), 'kind':'mixed_handshake_public_fixtures',
            'conversion_cases':count,'random_x25519_differential_cases':cases,'rfc_public_key_case':True,
            'low_order_zero_cases':2,'malformed_artifacts_rejected':rejected,
            'field_nodes':len(image['nodes']),'field_multiplications':sum(n['op']=='mul' for n in image['nodes']),
            'native_mpc_executed':False,
            'source_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in
                ('handshake_backend/mixed.py','handshake_backend/field_dag.py','TlsMpc/X25519.lean','TlsMpc/FieldDag.lean','scripts/check_mixed_handshake.py')}}
    (ROOT/'benchmarks/results/lean-mixed-handshake-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__ == '__main__':
    main()
