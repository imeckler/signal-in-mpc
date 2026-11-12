#!/usr/bin/env python3
"""Compare the SIGNAL_RECORD files of two runs (REORGANIZATION_PLAN.md, test set D).

    compare_records.py BEFORE AFTER     each a record file (.jsonl) or a directory of them (matched
                                        by relative path); exit 1 on a difference
    compare_records.py --mask IN OUT    write IN's masked form (a file, or a directory tree):
                                        what tests/golden/ stores
    options: --strict-content  fail on differences in the server's revealed bytes as well
             --keep-timing     compare keepalives and pings too (normally only counted)
             --show N          print at most N differing events per file (default 12)

A record (PublicServiceController.lean, `recordEvent`) holds what one controller sent to the
Signal server and what it revealed of the server's records. Two runs of the same code differ in
times, randomness and the server's own data; everything else must be equal. Masked:
- `time_ms`, the `timestamp` of a send, 13-digit millisecond and 10-digit second values in text;
- WebSocket mask keys (frames are unmasked before comparing; in a request template the engines'
  slots, zero bytes on the wire, show as <slot N>), the `Sec-WebSocket-Key`, `mask_hex`, the
  handshake's `transcript_sha256`;
- values that are fresh per run but structural: UUIDs, base64 runs of 20 or more characters, hex
  runs of 32 or more, and request ids are replaced by aliases numbered in order of first
  appearance in the file (so "the same value in the same places" is still checked);
- the id a client response echoes (the server's request id), registration ids in JSON.
Server records: what was withheld (the length and destination of every passed-over run, in
order) is compared exactly. Where the revealed and withheld runs lie is compared exactly when the
two records have the same size; the contents and the size are the server's data (its ids are
varints of varying length, which moves later runs), so differences there are reported but fail
only with --strict-content; likewise the size of a response that echoes the server's request id.
Timing: keepalive requests, WebSocket pings and pongs, and the server records answering them,
depend on how long steps took. They are counted, not compared (unless --keep-timing); the
request-id aliases of the other requests skip them.
"""
import argparse, base64, difflib, json, os, re, sys

HEADER = {'compare_records': 1}


# ---- Masking of bytes and text.

class Aliases:
    def __init__(self):
        self.tables = {}

    def __call__(self, kind, value):
        table = self.tables.setdefault(kind, {})
        if value not in table:
            table[value] = len(table) + 1
        return f'<{kind}#{table[value]}>'


UUID = re.compile(r'[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{4}-[0-9a-fA-F]{12}')
B64 = re.compile(r'(?<![A-Za-z0-9+/_-])[A-Za-z0-9+/_-]{20,}={0,2}')
HEX = re.compile(r'(?<![0-9a-fA-F])[0-9a-fA-F]{32,}(?![0-9a-fA-F])')
MILLIS = re.compile(r'(?<!\d)1\d{12}(?!\d)')
SECONDS = re.compile(r'(?<!\d)1\d{9}(?!\d)')
DATE = re.compile(r'(?im)^(date:\s*)[^\r\n]*')
WS_KEY = re.compile(r'(?im)^(sec-websocket-key:\s*)[^\r\n]*')
REG_ID = re.compile(r'"(registrationId|pniRegistrationId)":\s*\d+')


def mask_text(s, alias):
    s = DATE.sub(r'\1<date>', s)
    s = WS_KEY.sub(r'\1<ws-key>', s)
    s = REG_ID.sub(lambda m: f'"{m.group(1)}":<registration-id>', s)
    s = UUID.sub(lambda m: alias('uuid', m.group(0).lower()), s)
    s = HEX.sub(lambda m: alias('hex', m.group(0).lower()), s)
    s = B64.sub(lambda m: alias('b64', m.group(0)) if not re.fullmatch(r'[a-z_/-]+', m.group(0)) else m.group(0), s)
    s = MILLIS.sub('<ms>', s)
    s = SECONDS.sub('<s>', s)
    return s


def show_bytes(b, alias):
    """Bytes as masked text: UTF-8 text as it is; otherwise printable ASCII as it is and every
    other byte as \\xNN, so that the text inside binary framing is masked too."""
    try:
        text = b.decode('utf-8')
        if all(c.isprintable() or c in '\r\n\t' for c in text):
            return mask_text(text, alias)
    except UnicodeDecodeError:
        pass
    return 'bin:' + mask_text(''.join(chr(x) if 32 <= x < 127 and x != 92 else f'\\x{x:02x}' for x in b), alias)


def varint(b, i):
    n, shift = 0, 0
    while True:
        if i >= len(b) or shift > 63:
            raise ValueError('varint')
        n |= (b[i] & 0x7f) << shift
        i += 1
        if not b[i - 1] & 0x80:
            return n, i
        shift += 7


def protobuf(b):
    """[(field, value)] of a protobuf message (varint and length-delimited fields only)."""
    out, i = [], 0
    while i < len(b):
        key, i = varint(b, i)
        field, wire = key >> 3, key & 7
        if field == 0:
            raise ValueError('field 0')
        if wire == 0:
            value, i = varint(b, i)
        elif wire == 2:
            size, i = varint(b, i)
            if i + size > len(b):
                raise ValueError('length')
            value, i = b[i:i + size], i + size
        else:
            raise ValueError('wire type')
        out.append((field, value))
    return out


def websocket_message(payload, alias, ids):
    """Signal's WebSocketMessage {type, request{verb,path,body,id,headers}, response{id,status,message,headers,body}}."""
    try:
        fields = protobuf(payload)
        out = {}
        for field, value in fields:
            if field == 1 and isinstance(value, int):
                out['type'] = value
            elif field in (2, 3) and isinstance(value, bytes):
                part = {}
                for f, v in protobuf(value):
                    if field == 2:
                        name = {1: 'verb', 2: 'path', 3: 'body', 4: 'id', 5: 'header'}.get(f, f'field{f}')
                    else:
                        name = {1: 'id', 2: 'status', 3: 'message', 4: 'header', 5: 'body'}.get(f, f'field{f}')
                    if name == 'id':
                        v = ids(v) if field == 2 else '<echo>'   # a response echoes the server's request id
                    elif isinstance(v, bytes):
                        v = show_bytes(v, alias)
                    if name == 'header':
                        part.setdefault('headers', []).append(v)
                    else:
                        part[name] = v
                out['request' if field == 2 else 'response'] = part
            else:
                raise ValueError('not a WebSocketMessage')
        return out
    except (ValueError, IndexError):
        return None


def websocket_frames(b, slots=False):
    """[(first byte, opcode, unmasked payload, masked?)] or None. With `slots`, zero runs (3 or
    more) on the wire in a masked payload are the engines' slots and become <slot N>."""
    frames, i = [], 0
    while i < len(b):
        if len(b) - i < 2:
            return None
        b0, b1 = b[i], b[i + 1]
        opcode, masked, size, j = b0 & 0x0f, b1 & 0x80, b1 & 0x7f, i + 2
        if b0 & 0x70 or opcode not in (0, 1, 2, 8, 9, 10):
            return None
        if size == 126:
            size, j = int.from_bytes(b[j:j + 2], 'big'), j + 2
        elif size == 127:
            size, j = int.from_bytes(b[j:j + 8], 'big'), j + 8
        key = b[j:j + 4] if masked else None
        j += 4 if masked else 0
        if j + size > len(b):
            return None
        wire = b[j:j + size]
        payload = bytes(x ^ key[k % 4] for k, x in enumerate(wire)) if masked else wire
        slotted = []
        if masked and slots:
            for m in re.finditer(rb'\x00{3,}', wire):
                slotted.append((m.start(), m.end()))
        frames.append((b0, opcode, payload, bool(masked), slotted))
        i = j + size
    return frames


def mask_payload(b, alias, ids, template=False):
    """The canonical form of bytes sent to the server, and whether they are timing-driven."""
    if re.match(rb'^[A-Z]+ /', b):
        return {'http': show_bytes(b, alias)}, False
    frames = websocket_frames(b, slots=template)
    if frames is None:
        return {'raw': show_bytes(b, alias)}, False
    out, timing = [], False
    for b0, opcode, payload, masked, slotted in frames:
        frame = {'fin_op': b0, 'masked': masked, 'bytes': len(payload)}
        if opcode in (9, 10):
            timing = True   # ping, pong
        elif slotted:
            pieces, at = [], 0
            for start, end in slotted:
                pieces.append(show_bytes(payload[at:start], alias))
                pieces.append(f'<slot {end - start}>')
                at = end
            pieces.append(show_bytes(payload[at:], alias))
            frame['template'] = pieces
        else:
            message = websocket_message(payload, alias, ids) if opcode == 2 else None
            frame['message'] = message if message is not None else show_bytes(payload, alias)
            if message and message.get('response', {}).get('id') == '<echo>':
                frame['bytes'] = '<depends on the echoed id>'   # the server's id is a varint of varying length
            if message and message.get('request', {}).get('path') == '/v1/keepalive':
                timing = True
        out.append(frame)
    return {'websocket': out}, timing


# ---- Records to canonical events.

def canonical(rows):
    """Canonical events (dicts) of one raw record file, in order."""
    alias, events = Aliases(), []
    timing_ids = set()
    raw_ids = {}   # request id -> alias, over requests that are not timing-driven only

    def ids(value):
        value = int(value)
        if value in timing_ids:
            return '<timing-id>'
        if value not in raw_ids:
            raw_ids[value] = f'<id#{len(raw_ids) + 1}>'
        return raw_ids[value]

    open_records = {}   # handle -> its canonical record event (revealed bytes collect in it)
    for row in rows:
        row = dict(row)
        row.pop('time_ms', None)
        kind = row.get('event')
        if kind == 'record':
            event = {'event': 'record', 'connection': row.get('connection'), 'content_bytes': row.get('content_bytes'),
                     'revealed': [], 'passed_over': [], '_bytes': {}}
            open_records[row.get('handle')] = event
            events.append(event)
            continue
        if kind in ('revealed', 'passed-over'):
            record = open_records.get(row.get('handle'))
            if record is None:
                record = {'event': 'record', 'connection': None, 'content_bytes': None, 'revealed': [], 'passed_over': [], '_bytes': {}}
                open_records[row.get('handle')] = record
                events.append(record)
            if kind == 'revealed':
                data = bytes.fromhex(row.get('hex', ''))
                record['revealed'].append([row.get('offset'), len(data)])
                for k, x in enumerate(data):
                    record['_bytes'][row.get('offset', 0) + k] = x
            else:
                record['passed_over'].append([row.get('offset'), row.get('bytes'), row.get('to')])
            continue
        timing = False
        for field in ('hex', 'template_hex', 'frame_hex'):
            if field in row:
                # Ids inside a timing-driven request must not consume an alias: decode twice.
                probe, timing = mask_payload(bytes.fromhex(row[field]), Aliases(), lambda v: v, template=field != 'hex')
                if timing:
                    for frame in probe.get('websocket', []):
                        message = frame.get('message')
                        if isinstance(message, dict) and 'id' in message.get('request', {}):
                            timing_ids.add(int(message['request']['id']))
                row[field], _ = mask_payload(bytes.fromhex(row[field]), alias, ids, template=field != 'hex')
        if 'request_id' in row:
            row['request_id'] = ids(row['request_id'])
        for field, value in (('timestamp', '<ms>'), ('mask_hex', '<mask>'), ('transcript_sha256', '<transcript>')):
            if field in row:
                row[field] = value
        if 'chain_der_hex' in row:
            row['chain_der_hex'] = [alias('cert', c) for c in row['chain_der_hex']]
        if 'contact' in row:
            row['contact'] = alias('contact', str(row['contact']))
        for field, value in list(row.items()):
            if isinstance(value, str) and field not in ('event',) and not value.startswith('<'):
                row[field] = mask_text(value, alias)
        if timing:
            row['timing'] = True
        events.append(row)
    # Server records: their revealed content (masked), and whether they answer a timing request.
    for event in events:
        if event.get('event') != 'record':
            continue
        known = event.pop('_bytes')
        # The record's size is the server's choice (its ids and timestamps vary in length): it is
        # compared with the server's content, not with what this node decided.
        size = event.pop('content_bytes', None) or (max(known) + 1 if known else 0)
        event['content_size'] = size
        if known and len(known) == size:
            data = bytes(known[k] for k in range(size))
            frames = websocket_frames(data)
            if frames:
                for _, opcode, payload, _, _ in frames:
                    if opcode in (9, 10):
                        event['timing'] = True
                    elif opcode == 2:
                        try:
                            for field, value in protobuf(payload):
                                if field == 3 and isinstance(value, bytes):
                                    for f, v in protobuf(value):
                                        if f == 1 and v in timing_ids:
                                            event['timing'] = True
                        except (ValueError, IndexError):
                            pass
            event['content'] = show_bytes(data, alias)
        else:
            event['content'] = ''.join(f'{known[k]:02x}' if k in known else '..' for k in range(size)) if known else ''
            event['content'] = mask_text(event['content'], alias)
    return events


def load(path):
    with open(path) as f:
        lines = [json.loads(line) for line in f if line.strip()]
    if lines and lines[0] == HEADER:
        return lines[1:]
    return canonical(lines)


SERVER_DRIVEN = ('content', 'content_size', 'revealed', 'passed_over')


def key(event, content):
    """What must be equal in order. For a server record: what was withheld (each passed-over
    run's length and destination); where exactly, and what was revealed, depends on the
    server's bytes and is checked separately (`spans`)."""
    e = {k: v for k, v in event.items() if content or k not in SERVER_DRIVEN}
    if not content and event.get('event') == 'record':
        e['withheld'] = [[length, to] for _, length, to in event.get('passed_over', [])]
    return json.dumps(e, sort_keys=True, ensure_ascii=False)


def spans(event):
    return event.get('revealed'), event.get('passed_over')


def compare_files(before, after, strict_content, keep_timing, show):
    a, b = load(before), load(after)
    timing = (sum(1 for e in a if e.get('timing')), sum(1 for e in b if e.get('timing')))
    if not keep_timing:
        a = [e for e in a if not e.get('timing')]
        b = [e for e in b if not e.get('timing')]
    problems, notes = [], []
    ka, kb = [key(e, False) for e in a], [key(e, False) for e in b]
    matcher = difflib.SequenceMatcher(a=ka, b=kb, autojunk=False)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == 'equal':
            for i, j in zip(range(i1, i2), range(j1, j2)):
                same_server = (a[i].get('content'), a[i].get('content_size')) == (b[j].get('content'), b[j].get('content_size'))
                if spans(a[i]) != spans(b[j]):
                    # The same server bytes must be revealed and withheld at the same places; the
                    # places may move only where the server's bytes differ (a longer varint).
                    (problems if same_server or a[i].get('content_size') == b[j].get('content_size') or strict_content else notes).append(
                        f'revealed/withheld places of event {i + 1}/{j + 1} differ'
                        + ('' if same_server else ' (the server\'s bytes differ too)')
                        + f':\n      - only before: {[s for s in a[i]["revealed"] if s not in b[j]["revealed"]][:12]} '
                          f'{[s for s in a[i]["passed_over"] if s not in b[j]["passed_over"]][:6]}'
                        + f'\n      + only after: {[s for s in b[j]["revealed"] if s not in a[i]["revealed"]][:12]} '
                          f'{[s for s in b[j]["passed_over"] if s not in a[i]["passed_over"]][:6]}')
                if not same_server:
                    (problems if strict_content else notes).append(
                        f'server content of event {i + 1}/{j + 1} ({a[i].get("event")}) differs:\n      - {str(a[i].get("content"))[:300]}\n      + {str(b[j].get("content"))[:300]}')
            continue
        for i in range(i1, i2):
            problems.append(f'- [{i + 1}] {ka[i][:600]}')
        for j in range(j1, j2):
            problems.append(f'+ [{j + 1}] {kb[j][:600]}')
    return dict(events=(len(a), len(b)), timing=timing, problems=problems, notes=notes, shown=problems[:show])


def record_files(path):
    if os.path.isfile(path):
        return {'': path}
    out = {}
    for dirpath, _, filenames in os.walk(path):
        for name in filenames:
            if name.endswith('.jsonl'):
                full = os.path.join(dirpath, name)
                out[os.path.relpath(full, path)] = full
    return out


def mask_to(source, target):
    files = record_files(source)
    for rel, full in sorted(files.items()):
        out = target if rel == '' else os.path.join(target, rel)
        os.makedirs(os.path.dirname(out) or '.', exist_ok=True)
        with open(out, 'w') as f:
            f.write(json.dumps(HEADER) + '\n')
            for event in load(full):
                f.write(json.dumps(event, sort_keys=True, ensure_ascii=False) + '\n')
        print(f'masked {full} -> {out}')


def main():
    p = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    p.add_argument('paths', nargs=2, metavar=('BEFORE', 'AFTER'))
    p.add_argument('--mask', action='store_true', help='write the masked form of the first path to the second')
    p.add_argument('--strict-content', action='store_true')
    p.add_argument('--keep-timing', action='store_true')
    p.add_argument('--show', type=int, default=12)
    a = p.parse_args()
    if a.mask:
        mask_to(*a.paths)
        return
    before, after = record_files(a.paths[0]), record_files(a.paths[1])
    failed = False
    for rel in sorted(set(before) | set(after)):
        name = rel or os.path.basename(a.paths[1])
        if rel not in before or rel not in after:
            print(f'FAIL {name}: only in {"AFTER" if rel in after else "BEFORE"}')
            failed = True
            continue
        r = compare_files(before[rel], after[rel], a.strict_content, a.keep_timing, a.show)
        status = 'FAIL' if r['problems'] else 'ok  '
        failed = failed or bool(r['problems'])
        print(f'{status} {name}: {r["events"][0]} / {r["events"][1]} events compared; timing-driven {r["timing"][0]} / {r["timing"][1]}'
              + (f'; {len(r["notes"])} server-content differences (not failing)' if r['notes'] else ''))
        for line in r['shown']:
            print('    ' + line)
        if len(r['problems']) > len(r['shown']):
            print(f'    ... {len(r["problems"]) - len(r["shown"])} more')
    print('compare_records: ' + ('DIFFERENT' if failed else 'same (modulo masks)'))
    sys.exit(1 if failed else 0)


if __name__ == '__main__':
    main()
