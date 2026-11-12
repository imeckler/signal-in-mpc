#!/usr/bin/env python3
"""Turn fingerprint_terminator.py transcripts into a normalized, REDACTED client fingerprint.

    analyze.py TRANSCRIPT_DIR [OUT.json]

Everything a server could use to recognise the client is kept: the ClientHello field by field
(with JA3 and JA4 strings), the client's record pattern (ChangeCipherSpec, KeyUpdate, close),
the WebSocket upgrade request (header names, order, value shapes), every client WebSocket frame
(opcode, length encoding, masking), every chat request (protobuf field order, verb, path shape,
headers, request id, JSON key order, value shapes, canonical form) and the timing of keepalives.

Secrets and identities are replaced by their shapes: UUIDs become "{uuid}", base64 values
"<base64:N>" (N decoded bytes), the Basic credentials "<uuid>[.<device>]:<password:N>", JSON
numbers that would identify a device or registration by "<int>" (with their digit count and
whether they were space padded). So the output contains no account data and can be stored in the
repository.
"""
import base64, hashlib, json, re, sys
from pathlib import Path

UUID = re.compile(r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}')
EXT_NAMES = {0: 'server_name', 5: 'status_request', 10: 'supported_groups', 11: 'ec_point_formats',
             13: 'signature_algorithms', 16: 'alpn', 18: 'signed_certificate_timestamp', 21: 'padding',
             23: 'extended_master_secret', 27: 'compress_certificate', 35: 'session_ticket', 41: 'pre_shared_key',
             42: 'early_data', 43: 'supported_versions', 44: 'cookie', 45: 'psk_key_exchange_modes',
             51: 'key_share', 17513: 'application_settings', 65037: 'encrypted_client_hello', 65281: 'renegotiation_info'}
GREASE = {0x0a0a + 0x1010 * i for i in range(16)}


def u(b, i, n):
    return int.from_bytes(b[i:i + n], 'big')


def vec(b, i, n):
    length = u(b, i, n)
    return b[i + n:i + n + length], i + n + length


# ---------------------------------------------------------------- TLS

def records(raw):
    out, i = [], 0
    while i + 5 <= len(raw):
        length = u(raw, i + 3, 2)
        out.append((raw[i], u(raw, i + 1, 2), raw[i + 5:i + 5 + length]))
        i += 5 + length
    return out


def client_hello(raw):
    recs = records(raw)
    first = recs[0]
    body = b''.join(r[2] for r in recs if r[0] == 22)
    assert body[0] == 1, 'not a ClientHello'
    h = body[4:4 + u(body, 1, 3)]
    legacy = u(h, 0, 2)
    session, i = vec(h, 34, 1)
    suites, i = vec(h, i, 2)
    comp, i = vec(h, i, 1)
    exts_raw, i = vec(h, i, 2)
    ciphers = [u(suites, j, 2) for j in range(0, len(suites), 2)]
    exts, j = [], 0
    while j < len(exts_raw):
        kind, data = u(exts_raw, j, 2), exts_raw[j + 4:j + 4 + u(exts_raw, j + 2, 2)]
        j += 4 + len(data)
        exts.append((kind, data))
    out = dict(record_version=f'0x{first[1]:04x}', record_length=len(first[2]), handshake_length=len(h),
               legacy_version=f'0x{legacy:04x}', session_id_length=len(session),
               cipher_suites=[f'0x{c:04x}' for c in ciphers], compression=list(comp),
               extensions=[EXT_NAMES.get(k, str(k)) for k, _ in exts], extension_codes=[k for k, _ in exts])
    detail = {}
    groups, sigalgs, versions, alpn = [], [], [], []
    for kind, data in exts:
        name = EXT_NAMES.get(kind, str(kind))
        if kind == 0:
            names, _ = vec(data, 0, 2)
            detail[name] = dict(type=names[0], host_length=u(names, 1, 2))
        elif kind == 10:
            lst, _ = vec(data, 0, 2)
            groups = [u(lst, k, 2) for k in range(0, len(lst), 2)]
            detail[name] = [f'0x{g:04x}' for g in groups]
        elif kind == 13:
            lst, _ = vec(data, 0, 2)
            sigalgs = [u(lst, k, 2) for k in range(0, len(lst), 2)]
            detail[name] = [f'0x{g:04x}' for g in sigalgs]
        elif kind == 51:
            lst, _ = vec(data, 0, 2)
            shares, k = [], 0
            while k < len(lst):
                shares.append(dict(group=f'0x{u(lst, k, 2):04x}', length=u(lst, k + 2, 2)))
                k += 4 + u(lst, k + 2, 2)
            detail[name] = shares
        elif kind == 43:
            lst, _ = vec(data, 0, 1)
            versions = [u(lst, k, 2) for k in range(0, len(lst), 2)]
            detail[name] = [f'0x{g:04x}' for g in versions]
        elif kind == 45:
            detail[name] = list(vec(data, 0, 1)[0])
        elif kind == 16:
            lst, _ = vec(data, 0, 2)
            k = 0
            while k < len(lst):
                alpn.append(lst[k + 1:k + 1 + lst[k]].decode())
                k += 1 + lst[k]
            detail[name] = alpn
        elif kind == 21:
            detail[name] = dict(length=len(data))
        else:
            detail[name] = dict(length=len(data))
    out['extension_detail'] = detail
    # JA3: version,ciphers,extensions,groups,point formats (GREASE removed), decimal, '-' joined.
    ng = lambda xs: [x for x in xs if x not in GREASE]
    ja3 = ','.join([str(legacy), '-'.join(map(str, ng(ciphers))), '-'.join(map(str, ng([k for k, _ in exts]))),
                    '-'.join(map(str, ng(groups))), ''])
    out['ja3'] = ja3
    out['ja3_md5'] = hashlib.md5(ja3.encode()).hexdigest()
    # JA4 (FoxIO): t<ver><sni d|i><#ciphers><#exts><alpn first+last char>_<sha256/12 of sorted ciphers>_<sha256/12 of sorted exts (no SNI/ALPN)_sigalgs>
    ver = max(ng(versions)) if versions else legacy
    vcode = {0x0304: '13', 0x0303: '12', 0x0302: '11', 0x0301: '10'}.get(ver, '00')
    a = alpn[0] if alpn else ''
    acode = (a[0] + a[-1]) if a else '00'
    nc, ne = ng(ciphers), ng([k for k, _ in exts])
    head = f't{vcode}{"d" if any(k == 0 for k, _ in exts) else "i"}{min(len(nc), 99):02d}{min(len(ne), 99):02d}{acode}'
    hx = lambda x: f'{x:04x}'
    part_b = hashlib.sha256(','.join(sorted(map(hx, nc))).encode()).hexdigest()[:12]
    ext_sorted = ','.join(sorted(hx(k) for k in ne if k not in (0, 16)))
    sig = ','.join(hx(s) for s in ng(sigalgs))
    part_c = hashlib.sha256((ext_sorted + ('_' + sig if sig else '')).encode()).hexdigest()[:12]
    out['ja4'] = f'{head}_{part_b}_{part_c}'
    return out


def record_pattern(raw):
    """The client's records after the ClientHello: (content type, length) with KeyUpdate and
    close_notify recognised by their TLS 1.3 sizes under AES-GCM/ChaCha (inner 5+1 / 2+1 bytes)."""
    pattern = []
    for kind, version, body in records(raw)[1:]:
        if kind == 20:
            pattern.append('change_cipher_spec')
        elif kind == 23 and len(body) == 22:
            pattern.append('key_update(22)')
        elif kind == 23 and len(body) == 19:
            pattern.append('alert(19)')
        else:
            pattern.append(f'{kind}:{len(body)}')
    return pattern


# ---------------------------------------------------------------- HTTP / WebSocket

def shape_value(name, value):
    lname = name.lower()
    if lname == 'sec-websocket-key':
        return f'<base64:{len(base64.b64decode(value))}>'
    if lname == 'authorization' and value.startswith('Basic '):
        decoded = base64.b64decode(value[6:]).decode()
        user, _, password = decoded.partition(':')
        user = UUID.sub('<uuid>', user)
        user = re.sub(r'\.\d+$', '.<device>', user)
        return f'Basic <base64 of "{user}:<password:{len(password)}>">'
    if lname in ('unidentified-access-key', 'group-send-token'):
        return f'<base64:{len(base64.b64decode(value))}>'
    if lname == 'user-agent':
        return re.sub(r'\d+(\.\d+)+', '<version>', value)
    return UUID.sub('{uuid}', value)


def upgrade(plain):
    end = plain.index(b'\r\n\r\n')
    lines = plain[:end].decode().split('\r\n')
    headers = []
    for line in lines[1:]:
        name, _, value = line.partition(': ')
        headers.append([name, shape_value(name, value)])
    return dict(request_line=UUID.sub('{uuid}', lines[0]), headers=headers), plain[end + 4:]


def varint(b, i):
    n = shift = 0
    while True:
        n |= (b[i] & 0x7f) << shift
        shift += 7
        i += 1
        if not b[i - 1] & 0x80:
            return n, i


def fields(b):
    out, i = [], 0
    while i < len(b):
        key, i = varint(b, i)
        tag, wire = key >> 3, key & 7
        if wire == 0:
            value, i = varint(b, i)
            raw_len = None
        elif wire == 2:
            length, j = varint(b, i)
            raw_len = j - i
            value, i = b[j:j + length], j + length
        else:
            raise ValueError(f'wire type {wire}')
        out.append((tag, value, raw_len))
    return out


def json_shape(body):
    text = body.decode()
    parsed = json.loads(text)
    canonical = json.dumps(parsed, separators=(',', ':'), ensure_ascii=False)
    spaced = re.findall(r'"(\w+)":(\d+)( +)', text)

    def shape(v, key=None):
        if isinstance(v, dict):
            return {k: shape(x, k) for k, x in v.items()}
        if isinstance(v, list):
            return [shape(x) for x in v]
        if isinstance(v, str):
            try:
                return f'<base64:{len(base64.b64decode(v, validate=True))}>' if len(v) > 20 else v
            except Exception:
                return UUID.sub('{uuid}', v)
        if isinstance(v, bool) or v is None:
            return v
        if key == 'timestamp':
            return f'<int:{len(str(v))} digits>'
        if key in ('destinationDeviceId', 'destinationRegistrationId'):
            return '<int>'
        return v
    return dict(keys_in_order=list(_keys(parsed)), shape=shape(parsed), canonical=(canonical == text),
                space_padded_numbers=sorted({k for k, _, _ in spaced}))


def _keys(v, prefix=''):
    if isinstance(v, dict):
        for k, x in v.items():
            yield prefix + k
            yield from _keys(x, prefix + k + '.')
    elif isinstance(v, list) and v:
        yield from _keys(v[0], prefix + '[].')


def chat_message(payload):
    top = fields(payload)
    out = dict(field_order=[t for t, _, _ in top])
    for tag, value, _ in top:
        if tag == 1:
            out['type'] = {1: 'request', 2: 'response'}.get(value, value)
        elif tag in (2, 3):
            sub = fields(value)
            msg = dict(field_order=[t for t, _, _ in sub])
            headers = []
            for t, v, _ in sub:
                if tag == 2:
                    if t == 1: msg['verb'] = v.decode()
                    elif t == 2: msg['path'] = UUID.sub('{uuid}', v.decode())
                    elif t == 3: msg['body'] = json_shape(v) if v[:1] == b'{' else f'<{len(v)} bytes>'
                    elif t == 4: msg['id'] = v
                    elif t == 5:
                        name, _, value2 = v.decode().partition(':')
                        headers.append([name, value2[:1] == ' ', shape_value(name, value2.strip())])
                else:
                    if t == 1: msg['id'] = v
                    elif t == 2: msg['status'] = v
                    elif t == 3: msg['message'] = v.decode()
                    elif t == 4: msg['body'] = f'<{len(v)} bytes>'
                    elif t == 5: headers.append(v.decode())
            if headers:
                msg['headers'] = headers
            out['request' if tag == 2 else 'response'] = msg
    return out


def ws_frames(data):
    """Client frames: (fin, opcode, length encoding, masked, payload)."""
    out, i = [], 0
    while i + 2 <= len(data):
        b0, b1 = data[i], data[i + 1]
        length, j = b1 & 0x7f, i + 2
        enc = 'short'
        if length == 126:
            length, j, enc = u(data, j, 2), j + 2, '16-bit'
        elif length == 127:
            length, j, enc = u(data, j, 8), j + 8, '64-bit'
        mask = data[j:j + 4] if b1 & 0x80 else b'\0\0\0\0'
        if b1 & 0x80:
            j += 4
        if j + length > len(data):
            break
        payload = bytes(x ^ mask[k % 4] for k, x in enumerate(data[j:j + length]))
        out.append(dict(fin=bool(b0 & 0x80), rsv=(b0 >> 4) & 7, opcode=b0 & 0xf, length_encoding=enc,
                        masked=bool(b1 & 0x80), length=length, payload=payload))
        i = j + length
    return out, data[i:]


def connection(path):
    t = json.loads(Path(path).read_text())
    events = t['events']
    raw_c2s = b''.join(bytes.fromhex(e[3]) for e in events if e[1] == 'c2s' and e[2] == 'raw')
    plain_c2s = [(e[0], bytes.fromhex(e[3])) for e in events if e[1] == 'c2s' and e[2] == 'plain']
    out = dict(connection=t['connection'], negotiated=t.get('tls'), client_hello=client_hello(raw_c2s),
               client_records=record_pattern(raw_c2s))
    # Seconds from the first raw byte to the client's second flight (Finished), when visible.
    c2s_raw_times = [e[0] for e in events if e[1] == 'c2s' and e[2] == 'raw']
    if len(c2s_raw_times) > 1:
        out['seconds_to_client_finished'] = round(c2s_raw_times[1] - c2s_raw_times[0], 3)
    data = b''.join(p for _, p in plain_c2s)
    if not data:
        return out
    if data.startswith(b'GET '):
        out['upgrade'], rest = upgrade(data)
    else:
        out['transport'] = 'not HTTP/1.1 (h2 preface?)' if data.startswith(b'PRI * HTTP/2.0') else 'unknown'
        return out
    # Frame timing: attribute each frame to the plain chunk it ends in.
    times, position, offset = [], [], len(data) - len(rest)
    total = 0
    for when, chunk in plain_c2s:
        total += len(chunk)
        position.append((total, when))
    frames, _ = ws_frames(rest)
    seen, frames_out, ids, keepalive_times = 0, [], [], []
    last_activity = None
    for f in frames:
        seen += (2 + (2 if f['length_encoding'] == '16-bit' else 8 if f['length_encoding'] == '64-bit' else 0)
                 + (4 if f['masked'] else 0) + f['length'])
        when = next(w for end, w in position if end >= offset + seen)
        item = dict(at=when, fin=f['fin'], rsv=f['rsv'], opcode=f['opcode'], length_encoding=f['length_encoding'],
                    masked=f['masked'], length=f['length'])
        if f['opcode'] == 2:
            try:
                msg = chat_message(f['payload'])
                item['chat'] = msg
                req = msg.get('request')
                if req and 'id' in req:
                    ids.append(req['id'])
                if req and req.get('path') == '/v1/keepalive':
                    keepalive_times.append(round(when - last_activity, 1) if last_activity is not None else None)
            except Exception as e:
                item['chat'] = f'unparsed: {e}'
        elif f['opcode'] in (8, 9, 10):
            item['payload_hex'] = f['payload'].hex()
            if f['opcode'] == 9:
                keepalive_times.append(round(when - last_activity, 1) if last_activity is not None else None)
        last_activity = when
        frames_out.append(item)
    out['frames'] = frames_out
    out['request_ids'] = [str(i) for i in ids]
    out['keepalive_gaps_seconds'] = keepalive_times
    return out


def main():
    src = Path(sys.argv[1])
    conns = [connection(p) for p in sorted(src.glob('*.json'), key=lambda p: int(p.stem))]
    result = dict(source=str(src), connections=conns)
    text = json.dumps(result, indent=1, default=str)
    if len(sys.argv) > 2:
        Path(sys.argv[2]).write_text(text + '\n')
    else:
        print(text)


if __name__ == '__main__':
    main()
