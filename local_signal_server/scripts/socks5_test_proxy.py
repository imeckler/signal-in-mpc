#!/usr/bin/env python3
"""A local SOCKS5 proxy standing in for a Tor client in tests. Never contacts anything but the
targets it is given (127.0.0.1); it is not Tor and gives no anonymity.

    socks5_test_proxy.py PORT LOG HOST:PORT=TARGET_HOST:TARGET_PORT...

Accepts only username/password authentication (RFC 1929), as the MPC leader always offers it:
the credentials stand for a Tor circuit (Tor's IsolateSOCKSAuth). A CONNECT is served only for a
mapped (hostname, port) asked for by hostname (address type 3); an IPv4/IPv6 address or an
unmapped name is refused and logged. Prints "listening PORT" once ready.

LOG gets one JSON line per event:
  {"event": "open", "id", "username", "password", "atyp", "host", "port", "time"}
  {"event": "refused", "id", "reason", ...}
  {"event": "close", "id", "username", "password", "up_bytes", "down_bytes",
   "up_records": {TLS content type: count}, "dropped": bool, "time"}
`up_records` counts the TLS records the client sent (application data is type 23).

Commands on stdin, one per line:
  drop PASSWORD            close the open connection(s) with this password now
  drop-after PASSWORD N    the next connection with this password is closed right after the
                           client's N-th application-data record has been forwarded
"""
import json, socket, sys, threading, time

lock = threading.Lock()
connections = {}   # id -> dict(password=..., sockets=[...])
armed = {}         # password -> records
next_id = [0]


def log(entry):
    entry['time'] = time.time()
    with lock:
        with open(LOG, 'a') as out:
            out.write(json.dumps(entry) + '\n')


def exact(sock, n):
    data = b''
    while len(data) < n:
        part = sock.recv(n - len(data))
        if not part:
            raise ConnectionError('closed during the SOCKS exchange')
        data += part
    return data


def close(conn):
    for s in conn['sockets']:
        try:
            s.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        try:
            s.close()
        except OSError:
            pass


def serve(client, number):
    entry = dict(id=number)
    try:
        version, count = exact(client, 2)
        methods = exact(client, count)
        if version != 5 or 2 not in methods:
            client.sendall(b'\x05\xff')
            log(dict(entry, event='refused', reason='no username/password method', methods=list(methods)))
            return client.close()
        client.sendall(b'\x05\x02')
        auth_version, = exact(client, 1)
        user = exact(client, exact(client, 1)[0]).decode('utf-8', 'replace')
        password = exact(client, exact(client, 1)[0]).decode('utf-8', 'replace')
        client.sendall(b'\x01\x00')
        entry.update(username=user, password=password)
        version, command, _, atyp = exact(client, 4)
        if atyp == 3:
            host = exact(client, exact(client, 1)[0]).decode('utf-8', 'replace')
        elif atyp == 1:
            host = socket.inet_ntop(socket.AF_INET, exact(client, 4))
        elif atyp == 4:
            host = socket.inet_ntop(socket.AF_INET6, exact(client, 16))
        else:
            host = None
        port = int.from_bytes(exact(client, 2), 'big')
        entry.update(atyp=atyp, host=host, port=port)
        target = TARGETS.get((host, port)) if atyp == 3 else None
        if version != 5 or command != 1 or auth_version != 1 or target is None:
            client.sendall(b'\x05\x02\x00\x01' + bytes(6))   # connection not allowed by ruleset
            log(dict(entry, event='refused', reason='not a mapped hostname'))
            return client.close()
        upstream = socket.create_connection(target)
        client.sendall(b'\x05\x00\x00\x01' + socket.inet_aton('127.0.0.1') + target[1].to_bytes(2, 'big'))
    except (ConnectionError, OSError) as e:
        log(dict(entry, event='refused', reason=str(e)))
        return client.close()
    with lock:
        drop_after = armed.pop(password, None)
        conn = connections[number] = dict(password=password, sockets=[client, upstream], up=0, down=0, records={}, dropped=False)
    log(dict(entry, event='open'))

    def down():
        try:
            while True:
                data = upstream.recv(65536)
                if not data:
                    break
                client.sendall(data)
                conn['down'] += len(data)
        except OSError:
            pass
        close(conn)

    reader = threading.Thread(target=down, daemon=True)
    reader.start()
    pending = b''
    try:
        while True:
            data = client.recv(65536)
            if not data:
                break
            pending += data
            # Forward whole TLS records only, so a drop falls right after a record.
            while len(pending) >= 5 and len(pending) >= 5 + int.from_bytes(pending[3:5], 'big'):
                size = 5 + int.from_bytes(pending[3:5], 'big')
                record, pending = pending[:size], pending[size:]
                upstream.sendall(record)
                conn['up'] += size
                kind = str(record[0])
                conn['records'][kind] = conn['records'].get(kind, 0) + 1
                if drop_after is not None and conn['records'].get('23', 0) >= drop_after:
                    conn['dropped'] = True
                    raise ConnectionError('dropped on request')
    except (ConnectionError, OSError):
        pass
    close(conn)
    reader.join(timeout=5)
    log(dict(id=number, event='close', username=user, password=password, up_bytes=conn['up'], down_bytes=conn['down'],
             up_records=conn['records'], dropped=conn['dropped']))
    with lock:
        connections.pop(number, None)


def commands():
    for line in sys.stdin:
        words = line.split()
        if len(words) == 2 and words[0] == 'drop':
            with lock:
                chosen = [c for c in connections.values() if c['password'] == words[1]]
            for c in chosen:
                c['dropped'] = True
                close(c)
            log(dict(event='command', command=line.strip(), connections=len(chosen)))
        elif len(words) == 3 and words[0] == 'drop-after':
            with lock:
                armed[words[1]] = int(words[2])
            log(dict(event='command', command=line.strip()))
        sys.stdout.write('ok\n')
        sys.stdout.flush()


def main():
    global LOG, TARGETS
    port, LOG = int(sys.argv[1]), sys.argv[2]
    TARGETS = {}
    for rule in sys.argv[3:]:
        name, target = rule.split('=')
        host, hport = name.rsplit(':', 1)
        thost, tport = target.rsplit(':', 1)
        if thost not in ('127.0.0.1', 'localhost'):
            sys.exit('targets must be local')
        TARGETS[(host, int(hport))] = (thost, int(tport))
    listener = socket.socket()
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind(('127.0.0.1', port))
    listener.listen(64)
    threading.Thread(target=commands, daemon=True).start()
    print('listening', port, flush=True)
    while True:
        client, _ = listener.accept()
        with lock:
            next_id[0] += 1
            number = next_id[0]
        threading.Thread(target=serve, args=(client, number), daemon=True).start()


if __name__ == '__main__':
    main()
