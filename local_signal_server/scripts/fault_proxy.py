#!/usr/bin/env python3
"""TEST ONLY: a plaintext proxy between a second TLS terminator and the local Signal-Server that
answers chosen chat requests itself, so that the MPC client's handling of 429, 5xx and a bad
prekey response can be run. The local server has no switch for these, and the TLS terminator
only forwards bytes; this proxy reads the WebSocket frames on the plain side.

    fault_proxy.py PORT LOG [BACKEND_PORT]       (listens on 127.0.0.1:PORT; backend 127.0.0.1:18080)

Everything is forwarded unchanged except a client request (a masked binary frame carrying a chat
`WebSocketRequestMessage`) that matches an armed rule: it is NOT forwarded to the server (so a
"failed" send is really not delivered), and the proxy writes the response to the client.

Commands on stdin, one per line (the reply is "ok"):
  answer STATUS COUNT SKIP PREFIX [RETRY_AFTER]   of the requests whose path starts with PREFIX, skip
                                                  SKIP, then answer COUNT with STATUS (and a
                                                  Retry-After header when given and not "-")
  garbage COUNT SKIP PREFIX SIZE                  answer 200 with SIZE bytes that are not a bundle
  forged COUNT SKIP PREFIX                        answer 200 with a well-formed prekey bundle of one
                                                  device whose keys and signatures are random
  clear                                           drop every rule
LOG gets one JSON line per matched or forwarded request: {"path", "id", "action", "status"}.
Prints "listening PORT" once ready. Only ever connects to 127.0.0.1.
"""
import base64, json, os, socket, sys, threading, time

rules = []          # dicts: kind, status, count, skip, prefix, retry, size
lock = threading.Lock()


def log(entry):
    entry['time'] = time.time()
    with lock:
        with open(LOG, 'a') as out:
            out.write(json.dumps(entry) + '\n')


def varint(n):
    out = bytearray()
    while True:
        out.append((n & 127) | (128 if n > 127 else 0))
        n >>= 7
        if not n:
            return bytes(out)


def read_varint(data, at):
    value, shift = 0, 0
    while True:
        byte = data[at]
        value |= (byte & 127) << shift
        at += 1
        shift += 7
        if byte < 128:
            return value, at


def parse_request(payload):
    """(path, id) of a chat request message, or None."""
    try:
        if payload[:3] != b'\x08\x01\x12':
            return None
        size, at = read_varint(payload, 3)
        end, path, ident = at + size, None, None
        while at < end:
            tag = payload[at]
            if tag == 0x20:
                ident, at = read_varint(payload, at + 1)
            elif tag in (0x0a, 0x12, 0x1a, 0x2a):
                count, at = read_varint(payload, at + 1)
                if tag == 0x12:
                    path = payload[at:at + count].decode('utf-8', 'replace')
                at += count
            else:
                return None
        return (path, ident) if path is not None and ident is not None else None
    except IndexError:
        return None


def response_frame(ident, status, message, body, headers):
    inner = b'\x08' + varint(ident) + b'\x10' + varint(status) + b'\x1a' + varint(len(message)) + message.encode()
    if body:
        inner += b'\x22' + varint(len(body)) + body
    for header in headers:
        inner += b'\x2a' + varint(len(header)) + header.encode()
    payload = b'\x08\x02\x1a' + varint(len(inner)) + inner
    if len(payload) < 126:
        return bytes([0x82, len(payload)]) + payload
    if len(payload) < 65536:
        return bytes([0x82, 126]) + len(payload).to_bytes(2, 'big') + payload
    return bytes([0x82, 127]) + len(payload).to_bytes(8, 'big') + payload


def forged_bundle():
    """The server's prekey response for one device (MULTI_DEVICE.md, section 2), every key and
    signature random: it has a bundle's shape and cannot verify."""
    def key(prefix, size):
        return base64.b64encode(bytes([prefix]) + os.urandom(size)).decode()
    def signature():
        return base64.b64encode(os.urandom(64)).decode().rstrip('=')
    item = {'deviceId': 1, 'registrationId': 4242,
            'signedPreKey': {'keyId': 1, 'publicKey': key(5, 32), 'signature': signature()},
            'preKey': None,
            'pqPreKey': {'keyId': 1, 'publicKey': key(8, 1568), 'signature': signature()}}
    return json.dumps({'identityKey': key(5, 32), 'devices': [item]}, separators=(',', ':')).encode()


def decide(path):
    """The armed rule this request falls under, if any (and count it)."""
    with lock:
        for rule in rules:
            if path.startswith(rule['prefix']):
                if rule['skip'] > 0:
                    rule['skip'] -= 1
                    return None
                if rule['count'] > 0:
                    rule['count'] -= 1
                    return dict(rule)
                continue
    return None


def exact(sock, n):
    data = b''
    while len(data) < n:
        part = sock.recv(n - len(data))
        if not part:
            raise ConnectionError('closed')
        data += part
    return data


def serve(client):
    try:
        server = socket.create_connection(('127.0.0.1', BACKEND))
    except OSError:
        return client.close()
    write = threading.Lock()

    def down():
        try:
            while True:
                data = server.recv(65536)
                if not data:
                    break
                with write:
                    client.sendall(data)
        except OSError:
            pass
        for s in (client, server):
            try:
                s.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass

    threading.Thread(target=down, daemon=True).start()
    try:
        # The HTTP upgrade request, unchanged.
        head = b''
        while b'\r\n\r\n' not in head:
            part = client.recv(4096)
            if not part:
                raise ConnectionError('closed')
            head += part
        cut = head.index(b'\r\n\r\n') + 4
        server.sendall(head[:cut])
        buffered = head[cut:]

        def take(n):
            nonlocal buffered
            while len(buffered) < n:
                part = client.recv(65536)
                if not part:
                    raise ConnectionError('closed')
                buffered += part
            data, buffered = buffered[:n], buffered[n:]
            return data

        while True:
            first = take(2)
            size, raw = first[1] & 127, first
            if size == 126:
                more = take(2)
                raw += more
                size = int.from_bytes(more, 'big')
            elif size == 127:
                more = take(8)
                raw += more
                size = int.from_bytes(more, 'big')
            masked = bool(first[1] & 128)
            mask = take(4) if masked else b''
            body = take(size)
            raw += mask + body
            request = None
            if masked and first[0] == 0x82:
                request = parse_request(bytes(b ^ mask[i % 4] for i, b in enumerate(body)))
            rule = decide(request[0]) if request else None
            if rule is None:
                server.sendall(raw)
                if request:
                    log(dict(path=request[0], id=request[1], action='forwarded'))
                continue
            if rule['kind'] == 'answer':
                headers = [f'Retry-After:{rule["retry"]}'] if rule['retry'] is not None else []
                frame = response_frame(request[1], rule['status'], 'injected by the test proxy', b'', headers)
            elif rule['kind'] == 'garbage':
                frame = response_frame(request[1], 200, 'OK', b'x' * rule['size'], ['Content-Type:application/json'])
            else:
                frame = response_frame(request[1], 200, 'OK', forged_bundle(), ['Content-Type:application/json'])
            with write:
                client.sendall(frame)
            log(dict(path=request[0], id=request[1], action=rule['kind'], status=rule.get('status', 200)))
    except (ConnectionError, OSError):
        pass
    for s in (client, server):
        try:
            s.close()
        except OSError:
            pass


def commands():
    for line in sys.stdin:
        words = line.split()
        with lock:
            if words[:1] == ['clear']:
                rules.clear()
            elif words[:1] == ['answer'] and len(words) in (5, 6):
                retry = words[5] if len(words) == 6 and words[5] != '-' else None
                rules.append(dict(kind='answer', status=int(words[1]), count=int(words[2]), skip=int(words[3]), prefix=words[4], retry=retry))
            elif words[:1] == ['garbage'] and len(words) == 5:
                rules.append(dict(kind='garbage', count=int(words[1]), skip=int(words[2]), prefix=words[3], size=int(words[4])))
            elif words[:1] == ['forged'] and len(words) == 4:
                rules.append(dict(kind='forged', count=int(words[1]), skip=int(words[2]), prefix=words[3]))
        sys.stdout.write('ok\n')
        sys.stdout.flush()


def main():
    global LOG, BACKEND
    port, LOG = int(sys.argv[1]), sys.argv[2]
    BACKEND = int(sys.argv[3]) if len(sys.argv) > 3 else 18080
    listener = socket.socket()
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind(('127.0.0.1', port))
    listener.listen(64)
    threading.Thread(target=commands, daemon=True).start()
    print('listening', port, flush=True)
    while True:
        client, _ = listener.accept()
        threading.Thread(target=serve, args=(client,), daemon=True).start()


if __name__ == '__main__':
    main()
