#!/usr/bin/env python3
"""Numeric Lean parser artifacts against an independent buffered TLS framer.

Public fixtures only. No native MPC execution, traffic capture or resumption.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.aig import execute, statistics
from cryptography.hazmat.primitives.ciphers.aead import AESGCM


class Framer:
    def __init__(self):
        self.header = b''
        self.kind = 0
        self.remaining = 0
        self.bad = False

    def state(self):
        if self.header:
            phase, count = len(self.header), int.from_bytes(self.header[1:], 'big')
        else:
            phase, count = (4 if self.remaining else 0), self.remaining
        return bytes([phase, self.kind])+count.to_bytes(8, 'big')+bytes([255 if self.bad else 0])

    def record(self, kind, data, authenticated=255):
        if self.bad or authenticated != 255:
            self.bad = True
            return 0, 0
        if kind != 22:
            if self.header or self.remaining:
                self.bad = True
                return 0, 0
            if kind == 23:
                return 1, 0
            if kind == 21 and len(data) == 2:
                if data[1] == 0:
                    return 4, 0
                if data[1] == 90:
                    return 2, 0
            self.bad = True
            return 0, 0
        if not data:
            self.bad = True
            return 0, 0
        event, request = 2, 0
        while data:
            if event == 3:
                self.bad = True  # KeyUpdate must be last in this record.
                break
            if not self.remaining:
                count = min(4-len(self.header), len(data))
                self.header += data[:count]
                data = data[count:]
                self.kind = self.header[0]
                if self.kind not in (4, 24):
                    self.bad = True
                    break
                if len(self.header) < 4:
                    break
                self.remaining = int.from_bytes(self.header[1:], 'big')
                self.header = b''
                if self.kind == 24 and self.remaining != 1:
                    self.bad = True
                    break
                if not self.remaining:
                    continue
            count = min(self.remaining, len(data))
            if self.kind == 24 and count:
                if data[0] > 1:
                    self.bad = True
                    break
                event, request = 3, data[0]
            self.remaining -= count
            data = data[count:]
        return (0, 0) if self.bad else (event, request)


def numeric(image, inputs):
    mask = (1 << len(inputs))-1
    bits = [sum(((data[i] >> b) & 1) << lane for lane, data in enumerate(inputs))
            for i in range(len(inputs[0])) for b in range(7, -1, -1)]
    output = execute(image, bits, 0, mask)
    return [bytes(sum(((output[j+b] >> lane) & 1) << (7-b) for b in range(8))
                  for j in range(0, len(output), 8)) for lane in range(len(inputs))]


def parsed(capacity, kind, data, authenticated=255):
    assert len(data) <= capacity
    return bytes([authenticated, kind])+len(data).to_bytes(2, 'big')+data+bytes(capacity-len(data))


def sequences():
    rows = []
    for request in (0, 1):
        ku = bytes([24, 0, 0, 1, request])
        for mask in range(16):
            cuts = [0]+[i for i in range(1, 5) if mask & (1 << (i-1))]+[5]
            rows.append([(22, ku[a:b], 255) for a, b in zip(cuts, cuts[1:])]+[(23, b'end', 255)])
        rows.extend([[(22, ku+b'\x04', 255)], [(22, ku+ku, 255)]])
    ticket = b'\x04\x00\x00\x12'+bytes(range(18))
    for cut in range(1, len(ticket)):
        rows.append([(22, ticket[:cut], 255), (22, ticket[cut:], 255),
                     (22, bytes([24,0,0,1,1]), 255), (23, b'hello', 255)])
    rows += [[(22, ticket+bytes([24,0,0,1,0]), 255)],
             [(22, ticket+ticket, 255)], [(22, b'\x04\x00\x00\x00', 255)],
             [(22, b'\x18\x00', 255), (23, b'app', 255)],
             [(22, b'\x04\x00\x00\x04ab', 255), (21, b'\x01\x00', 255)],
             [(22, b'\x18\x00\x00\x02\x00\x00', 255)],
             [(22, b'\x18\x00\x00\x00', 255)], [(22, b'\x18\x00\x00\x01\x02', 255)],
             [(22, b'', 255)], [(22, b'\x0d', 255)],
             [(23, b'private recipient', 0), (23, b'next', 255)]]
    for kind in (0, 20, 21, 22, 23, 24, 255):
        for value in (b'', b'a', b'\x01\x00', b'\x02\x00', b'\x01\x5a', b'\x02\x14', b'\x00\xff', b'abc'):
            rows.append([(kind, value, 255)])
    rng = random.Random(193529)
    for _ in range(80):
        data = rng.randbytes(rng.randrange(1, 40))
        rows.append([(rng.choice([21,22,23]), data, rng.choice([255,255,0,1]))])
    return rows


def main():
    subprocess.run(['lake','build','emit_mpc'], cwd=ROOT, check=True)
    capacity = 64
    result = subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),'tls-post-handshake',str(capacity)],
                            cwd=ROOT, check=True, capture_output=True, timeout=180)
    image = json.loads(result.stdout)
    cases, inputs, expected = sequences(), [], []
    for sequence in cases:
        framer = Framer()
        for kind, data, auth in sequence:
            old = framer.state()
            event, request = framer.record(kind, data, auth)
            inputs.append(old+parsed(capacity, kind, data, auth))
            app = len(data).to_bytes(2,'big')+data+bytes(capacity-len(data)) if event == 1 else bytes(capacity+2)
            expected.append((event, request, framer.state(), app))
    outputs = numeric(image, inputs)
    for index, (out, (event, request, state, app)) in enumerate(zip(outputs, expected)):
        assert out[:2] == bytes([event, request]), (index, 'event', out[:2], event, request)
        assert out[13:] == app, (index, 'private application buffer')
        assert out[12] == state[10], (index, 'terminal flag')
        if event:
            assert out[2:13] == state, (index, 'shared framing state', out[2:13].hex(), state.hex())
    # Actual artifact output state is fed back for each record of a long stream.
    state = bytes(11)
    stream = [(22,b'\x04\x00\x00\x09abc',255),(22,b'defghi',255),
              (22,b'\x18\x00',255),(22,b'\x00\x01\x01',255),(23,b'payload',255),
              (21,b'\x01\x5a',255),(21,b'\x01\x00',255)]
    framer = Framer()
    for kind, data, auth in stream:
        out = numeric(image, [state+parsed(capacity,kind,data,auth)])[0]
        assert out[:2] == bytes(framer.record(kind,data,auth))
        state = out[2:13]
        assert state == framer.state()
    # Full numeric composition: independent AES-GCM records feed the private
    # parser directly. Neither an event nor application data bypasses the tag.
    full = subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),'tls-open-application-record','27'],
                          cwd=ROOT, check=True, capture_output=True, timeout=180)
    full_image = json.loads(full.stdout)
    key, iv, seq = bytes(range(16)), bytes(range(12)), bytes(8)
    aad = bytes([23,3,3,0,22])
    full_inputs, full_expected = [], []
    for kind, data in [(22,bytes([24,0,0,1,0])), (22,bytes([24,0,0,1,1])),
                       (22,bytes([24,0,0,1,2])), (22,bytes([4,0,0,1,99])),
                       (23,b'hello'), (23,b''), (21,b'\x01\x00'),
                       (21,b'\x02\x5a'), (21,b'\x01\x14')]:
        clear = data+bytes([kind])+bytes(5-len(data))
        wire = aad+AESGCM(key).encrypt(iv,clear,aad)
        f = Framer()
        event, request = f.record(kind,data)
        full_inputs.append(bytes(11)+key+iv+seq+wire)
        app = len(data).to_bytes(2,'big')+data+bytes(6-len(data)) if event == 1 else bytes(8)
        full_expected.append((event,request,app))
        damaged = wire[:-1]+bytes([wire[-1]^1])
        full_inputs.append(bytes(11)+key+iv+seq+damaged)
        full_expected.append((0,0,bytes(8)))
    for out, (event, request, app) in zip(numeric(full_image,full_inputs),full_expected):
        assert out[:2] == bytes([event,request])
        assert out[13:] == app
    names = ['TlsMpc/TlsPostHandshake.lean','Main.lean','scripts/check_tls_post_handshake.py']
    report = {'checked_at_utc':datetime.now(timezone.utc).isoformat(),
              'numeric_fixture_lanes':len(inputs),'protocol_sequences':len(cases),'chained_records':len(stream),
              'capacity':capacity,'statistics':statistics(image),
              'authenticated_numeric_lanes':len(full_inputs),'authenticated_statistics':statistics(full_image),
              'authenticated_artifact_sha256':hashlib.sha256(full.stdout).hexdigest(),
              'artifact_sha256':hashlib.sha256(result.stdout).hexdigest(),
              'source_sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names},
              'native_mpc_executed':False,'server_trace_used':False,
              'scope':'Shared post-handshake framing and disclosure layout; no resumption, backend binding or erasure claim.'}
    (ROOT/'benchmarks/results/tls-post-handshake-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
