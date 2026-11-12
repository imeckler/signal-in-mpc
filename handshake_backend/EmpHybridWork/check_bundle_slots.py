#!/usr/bin/env python3
"""Check `bundle-slot FIRST LAST ONETIME` (TlsMpc/BundleSlotKernels.lean): one circuit per item
position and one-time flag, for every digit count of the five numbers.

A CHECK only. Bodies of `GET /v2/keys/{uuid}/*` are built here with `json` and `base64` in the
shape Signal-Server writes (as check_bundle_kernels.py does), for 1 to 5 devices whose numbers
have every digit count the server's types allow (device id 1–3 digits, registration id 1–5,
key ids 1–10). For each item:
  1. the Lean splice (`bundle_slot_emitter splice D R S P K`) equals an independent one written
     here (each number right-aligned in its slot: 3, 5, 10, 10, 10, padded with the filler byte 0,
     NUL; `0` characters before the emitter batch, see EMITTER_BATCH.md);
  2. the kernel on the spliced item, the bytes around it and the digit counts gives exactly the
     fields a `json.loads` parse of the body gives (the outputs of `bundle-item`);
  3. altered inputs release nothing: a number with a leading zero in the body, a padding byte that
     is not the filler (`1`, or the old `0`), a digit count one too small or too large, 0, or
     beyond the slot, numbers out of range with the same digit counts, a template character
     changed.
Kernels come from `circuit_cache.py kernel bundle-slot ...` (which runs `bundle_slot_emitter`).

    check_bundle_slots.py        (run it under scripts/guarded.py; writes bundle-slots-report.json)
"""
import base64, json, random, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SPLICER = ROOT / '.lake/build/bin/bundle_slot_emitter'
SLOTS = (3, 5, 10, 10, 10)
FILLER = b'\x00'   # Lean's `BundleSlots.filler`


def kernel(*args):
    out = subprocess.run([sys.executable, str(HERE / 'circuit_cache.py'), 'kernel', *map(str, args)], check=True, capture_output=True).stdout.decode().split()
    flat, layout = Path(out[0]), Path(out[4])
    lines = flat.read_text().split('\n')
    n, count, _ = map(int, lines[1].split())
    if lines[0] != 'EMP_HYBRID_BOOL_V1':
        raise ValueError('flat header')
    gates = [(row[0], *map(int, row.split()[1:])) for row in lines[2:2 + count]]
    outputs = list(map(int, lines[2 + count].split()[1:]))
    fields, offset, opened = {}, {'I': 0, 'O': 0}, set()
    for row in layout.read_text().split('\n')[1:]:
        f = row.split()
        if len(f) >= 3:
            fields[(f[0], f[1])] = (offset[f[0]], int(f[2]))
            offset[f[0]] += int(f[2])
            if f[0] == 'O' and f[3] != '0':
                opened.add(f[1])
    names = {name for kind, name in fields if kind == 'I'}

    def run(**values):
        if set(values) != names:
            raise ValueError('inputs %s' % sorted(names ^ set(values)))
        wires = [0] * n
        for name, data in values.items():
            start, bits = fields[('I', name)]
            if bits != 8 * len(data):
                raise ValueError('input size ' + name)
            data = int.from_bytes(data, 'little')
            for i in range(bits):
                wires[start + i] = (data >> i) & 1
        for g in gates:
            if g[0] == 'N':
                wires.append(1 - wires[g[1]])
            elif g[0] == 'X':
                wires.append(wires[g[1]] ^ wires[g[2]])
            else:
                wires.append(wires[g[1]] & wires[g[2]])
        bits = [wires[o] for o in outputs]
        return {name: sum(bits[start + i] << i for i in range(size)).to_bytes(size // 8, 'little')
                for (kind, name), (start, size) in fields.items() if kind == 'O'}
    return run, sum(g[0] == 'A' for g in gates), opened, fields


def b64(data, padding=True):
    text = base64.b64encode(data).decode()
    return text if padding else text.rstrip('=')


def unb64(text):
    return base64.b64decode(text + '=' * (-len(text) % 4), validate=True)


def make_device(rng, device, registration, signed_id, kyber_id, one_time_id):
    return dict(device=device, registration=registration, signed_id=signed_id, signed_key=rng.randbytes(32), signed_signature=rng.randbytes(64),
                one_time_id=one_time_id, one_time_key=rng.randbytes(32), kyber_id=kyber_id, kyber_key=rng.randbytes(1568), kyber_signature=rng.randbytes(64))


def item_text(d):
    """PreKeyResponseItem as Jackson writes it (field order of the Java class, no whitespace)."""
    pre = 'null' if d['one_time_id'] is None else '{"keyId":%s,"publicKey":"%s"}' % (d['one_time_id'], b64(b'\x05' + d['one_time_key']))
    return ('{"deviceId":%s,"registrationId":%s,"signedPreKey":{"keyId":%s,"publicKey":"%s","signature":"%s"},"preKey":%s,'
            '"pqPreKey":{"keyId":%s,"publicKey":"%s","signature":"%s"}}') % (
        d['device'], d['registration'], d['signed_id'], b64(b'\x05' + d['signed_key']), b64(d['signed_signature'], False), pre,
        d['kyber_id'], b64(b'\x08' + d['kyber_key']), b64(d['kyber_signature'], False))


def response(identity, devices):
    return ('{"identityKey":"%s","devices":[%s]}' % (b64(b'\x05' + identity), ','.join(item_text(d) for d in devices))).encode()


def expected(body, index):
    """The fields a JSON parse gives (bundle-item's outputs)."""
    whole = json.loads(body)
    d = whole['devices'][index]
    key = lambda text, kind: (lambda raw: raw[1:] if raw[0] == kind else None)(unb64(text))
    out = dict(valid=b'\xff', identityKey=key(whole['identityKey'], 5), deviceId=bytes([d['deviceId']]), registrationId=d['registrationId'].to_bytes(4, 'big'),
               signedPrekeyId=d['signedPreKey']['keyId'].to_bytes(4, 'big'), signedPrekey=key(d['signedPreKey']['publicKey'], 5),
               signedPrekeySignature=unb64(d['signedPreKey']['signature']), kyberPrekeyId=d['pqPreKey']['keyId'].to_bytes(4, 'big'),
               kyberPrekey=key(d['pqPreKey']['publicKey'], 8), kyberPrekeySignature=unb64(d['pqPreKey']['signature']))
    if d['preKey'] is not None:
        out.update(oneTimePrekeyId=d['preKey']['keyId'].to_bytes(4, 'big'), oneTimePrekey=key(d['preKey']['publicKey'], 5))
    return out


def number_spans(item):
    """(start, digits) of the five numbers in an item's text (one-time prekey id: absent or not), in order."""
    spans, at = [], 0
    for name in (b'"deviceId":', b'"registrationId":', b'"signedPreKey":{"keyId":', b'"preKey":{"keyId":', b'"pqPreKey":{"keyId":'):
        found = item.find(name, at)
        if found < 0:
            spans.append(None)
            continue
        start = found + len(name)
        end = start
        while item[end:end + 1].isdigit():
            end += 1
        spans.append((start, end - start))
        at = end
    return spans


def splice_reference(item):
    """Each number right-aligned in its slot, padded with the filler; everything else copied."""
    out, at = b'', 0
    for span, slot in zip(number_spans(item), SLOTS):
        if span is None:
            continue
        start, digits = span
        out += item[at:start] + FILLER * (slot - digits) + item[start:start + digits]
        at = start + digits
    return out + item[at:]


def splice_lean(widths, item):
    rows = subprocess.run([str(SPLICER), 'splice', *map(str, widths)], check=True, capture_output=True, text=True).stdout.split('\n')
    out, at = b'', 0
    for row in rows:
        if row.strip():
            zeros, copy = map(int, row.split())
            out += FILLER * zeros + item[at:at + copy]
            at += copy
    if at != len(item):
        raise AssertionError('the Lean splice does not copy the whole item')
    return out


def items_of(body, count):
    """(start, item bytes, widths) per device, from the text (independent of the kernels)."""
    whole = json.loads(body)
    rows, start = [], body.index(b'[') + 1
    for d in whole['devices']:
        text = item_text_from(d, body, start)
        spans = number_spans(text)
        widths = [s[1] if s else 0 for s in spans]
        rows.append((start, text, widths))
        start += len(text) + 1
    if len(rows) != count:
        raise AssertionError('device count')
    return rows


def item_text_from(d, body, start):
    depth, at = 0, start
    while True:
        c = body[at:at + 1]
        depth += {b'{': 1, b'}': -1}.get(c, 0)
        at += 1
        if depth == 0:
            return body[start:at]


def main():
    rng = random.Random(20261112)
    report = dict(kernels={}, cases=[], rejected=0)
    cache = {}

    def load(first, last, one_time):
        key = (first, last, one_time)
        if key not in cache:
            run, ands, opened, fields = kernel('bundle-slot', first, last, one_time)
            if opened:
                raise AssertionError('bundle-slot opens %s' % sorted(opened))
            cache[key] = run
            report['kernels']['bundle-slot %d %d %d' % key] = dict(and_gates=ands)
        return cache[key]

    def number(digits, limit=None):
        low = 10 ** (digits - 1) if digits > 1 else 0
        high = min(10 ** digits - 1, limit if limit is not None else 10 ** digits - 1)
        return rng.randint(low, high)

    identity = rng.randbytes(32)
    # Every digit count at least once: device id 1–3 (≤ 127), registration id 1–5 (≤ 16383), key ids 1–10 (< 2^32).
    configurations = []
    for k in range(10):
        configurations.append(dict(device=number(1 + k % 3, 127), registration=number(1 + k % 5, 16383), signed=number(1 + k, 2 ** 32 - 1),
                                   one_time=None if k % 3 == 0 else number(1 + (k * 7) % 10, 2 ** 32 - 1), kyber=number(10 - k, 2 ** 32 - 1)))
    # As a real three-device account (Android primary, two linked devices), and the real run's digit total.
    configurations += [dict(device=1, registration=12345, signed=14000123, one_time=9876543, kyber=16000001),
                       dict(device=2, registration=812, signed=345, one_time=4096, kyber=12),
                       dict(device=3, registration=16383, signed=2147483647, one_time=None, kyber=99999999)]
    groups = [configurations[0:1], configurations[1:3], configurations[3:6], configurations[6:10], configurations[10:13], configurations[3:8]]
    for group in groups:
        devices = [make_device(rng, c['device'], c['registration'], c['signed'], c['kyber'], c['one_time']) for c in group]
        body = response(identity, devices)
        rows = items_of(body, len(devices))
        for index, (start, text, widths) in enumerate(rows):
            spliced = splice_reference(text)
            if splice_lean(widths, text) != spliced:
                raise AssertionError('splice differs for widths %s' % widths)
            first, last, one_time = int(index == 0), int(index + 1 == len(rows)), int(widths[3] != 0)
            run = load(first, last, one_time)

            def inputs(item=spliced, digits=widths, whole=body, at=start, length=len(text)):
                values = dict(head=whole[:73], item=item, end=whole[-2:], widths=bytes(digits))
                if not first:
                    values['before'] = whole[at - 1:at]
                if not last:
                    values['after'] = whole[at + length:at + length + 1]
                return values
            got = run(**inputs())
            want = expected(body, index)
            if got != want:
                raise AssertionError('fields differ for widths %s: %s' % (widths, [k for k in want if got.get(k) != want[k]]))

            def rejected(why, **change):
                got = run(**{**inputs(), **change})
                if any(any(v) for v in got.values()):
                    raise AssertionError('accepted or released: %s (widths %s)' % (why, widths))
                report['rejected'] += 1
            # digit counts that do not match the slots
            for position in range(5):
                if position == 3 and not one_time:
                    continue
                for delta in (-1, 1):
                    other = list(widths)
                    other[position] += delta
                    rejected('width %d %+d' % (position, delta), widths=bytes(other))
            rejected('device width 0', widths=bytes([0] + widths[1:]))
            rejected('registration width beyond the slot', widths=bytes([widths[0], 6] + widths[2:]))
            # a padding byte that is not the filler (the first byte of the device-id slot is padding
            # when D < 3): a digit, or the character `0` the splice used before the emitter batch
            spans = number_spans(spliced)
            if widths[0] < 3:
                at = spans[0][0]
                rejected('padding 1', item=spliced[:at] + b'1' + spliced[at + 1:])
                rejected('padding 0 character', item=spliced[:at] + b'0' + spliced[at + 1:])
                # the former defect (NEEDS_REVIEW.md 3f, 2): the body's device id written `0d` (two
                # digits, leading zero) and spliced with two digits, declared with one or with two
                if widths[0] == 1:
                    leading = spliced[:at + 1] + b'0' + spliced[at + 2:]
                    rejected('leading zero spliced with 2 digits, declared 1', item=leading)
                    rejected('leading zero spliced with 2 digits, declared 2', item=leading,
                             widths=bytes([2] + widths[1:]))
            # a number written with a leading zero, kept at its digit count (the body would be
            # invalid JSON): take the registration id's slot and make its first real digit `0`
            if widths[1] > 1:
                at = spans[1][0] + 5 - widths[1]
                rejected('leading zero', item=spliced[:at] + b'0' + spliced[at + 1:])
            # template text
            at = spliced.index(b'"pqPreKey"')
            rejected('template', item=spliced[:at + 1] + b'P' + spliced[at + 2:])
        report['cases'].append(dict(devices=len(devices), body_bytes=len(body), widths=[r[2] for r in rows]))
    # Numbers out of range with the same digit counts: device id 128, key id 2^32.
    for (name, value, position) in ((b'"deviceId":', 128, 0), (b'"signedPreKey":{"keyId":', 2 ** 32, 2)):
        c = dict(device=12, registration=812, signed=345, one_time=None, kyber=12)
        devices = [make_device(rng, c['device'], c['registration'], c['signed'], c['kyber'], c['one_time'])]
        body = response(identity, devices)
        start, text, widths = items_of(body, 1)[0]
        good = splice_reference(text)
        spans = number_spans(good)
        slot_start, _ = spans[position]
        slot = SLOTS[position]
        bad = good[:slot_start] + FILLER * (slot - len(str(value))) + str(value).encode() + good[slot_start + slot:]
        widths = list(widths)
        widths[position] = len(str(value))
        got = load(1, 1, 0)(head=body[:73], item=bad, end=body[-2:], widths=bytes(widths))
        if any(any(v) for v in got.values()):
            raise AssertionError('out of range accepted: %s' % value)
        report['rejected'] += 1
    (HERE / 'bundle-slots-report.json').write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps(dict(kernels=report['kernels'], cases=len(report['cases']), rejected=report['rejected'], passed=True)))


if __name__ == '__main__':
    main()
