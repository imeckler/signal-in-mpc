#!/usr/bin/env python3
"""Volume test: N GB each way between the two machines, both directions at once, with the rate
recorded over time, to see whether either provider slows a large transfer down.

On machine b:   python3 volume_test.py serve 10.77.0.2
On machine a:   python3 volume_test.py run 10.77.0.2 --bind 10.77.0.1 --gb 200 --out logs/volume.csv

Both sides send --gb gigabytes (default 200) over --streams TCP connections (default 4) and count
what arrives. The log has a row every 10 seconds: seconds, bytes sent so far, bytes received so
far (as seen by machine a, the side that runs `run`). The data is zeros: inside WireGuard every
byte is encrypted, so the provider sees the same thing whatever is sent. Python standard library only.
`summary LOG` prints the mean rate each way, the slowest minute, and the last tenth against the
first tenth. Afterwards look at both providers' traffic graphs, invoice previews and mailboxes.
"""
import argparse, csv, socket, struct, sys, threading, time

CHUNK = 1 << 20
PORT = 5301


class Counter:
    def __init__(self):
        self.sent = self.received = 0
        self.lock = threading.Lock()

    def add(self, sent=0, received=0):
        with self.lock:
            self.sent += sent
            self.received += received


def pump(connection, total, counter):
    """Send `total` bytes and count what comes back, on one connection, until both are done."""
    def sender():
        block = bytes(CHUNK)
        left = total
        while left > 0:
            n = connection.send(block[:min(CHUNK, left)])
            left -= n
            counter.add(sent=n)
        connection.shutdown(socket.SHUT_WR)
    t = threading.Thread(target=sender, daemon=True)
    t.start()
    buffer = bytearray(CHUNK)
    while True:
        n = connection.recv_into(buffer)
        if n == 0:
            break
        counter.add(received=n)
    t.join()
    connection.close()


def serve(args):
    listener = socket.socket()
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind((args.bind, args.port))
    listener.listen(64)
    print(f'listening on {args.bind}:{args.port}; each connection states how much to send back', flush=True)
    counter = Counter()
    while True:
        connection, _ = listener.accept()
        header = b''
        while len(header) < 8:
            header += connection.recv(8 - len(header))
        threading.Thread(target=pump, args=(connection, struct.unpack('>Q', header)[0], counter), daemon=True).start()


def run(args):
    per_stream = int(args.gb * 1e9) // args.streams
    counter = Counter()
    threads = []
    for _ in range(args.streams):
        connection = socket.socket()
        if args.bind:
            connection.bind((args.bind, 0))
        connection.connect((args.peer, args.port))
        connection.sendall(struct.pack('>Q', per_stream))
        t = threading.Thread(target=pump, args=(connection, per_stream, counter), daemon=True)
        t.start()
        threads.append(t)
    started = time.time()
    with open(args.out, 'w', newline='') as f:
        out = csv.writer(f)
        out.writerow(['seconds', 'sent_bytes', 'received_bytes'])
        while any(t.is_alive() for t in threads):
            time.sleep(10)
            out.writerow([f'{time.time() - started:.1f}', counter.sent, counter.received])
            f.flush()
        out.writerow([f'{time.time() - started:.1f}', counter.sent, counter.received])
    print_summary(summarise(args.out))


def summarise(path):
    rows = [(float(r['seconds']), int(r['sent_bytes']), int(r['received_bytes'])) for r in csv.DictReader(open(path))]
    out = {}
    for name, column in (('sent', 1), ('received', 2)):
        total = rows[-1][column]
        active = [r for r in rows if r[column] < total] + [next(r for r in rows if r[column] >= total)]
        rates = [(b[column] - a[column]) * 8 / 1e6 / (b[0] - a[0]) for a, b in zip([(0.0, 0, 0)] + active, active) if b[0] > a[0]]
        minutes = [sum(rates[i:i + 6]) / len(rates[i:i + 6]) for i in range(0, len(rates), 6) if len(rates[i:i + 6]) == 6 or len(rates) < 6]
        tenth = max(1, len(rates) // 10)
        out[name] = dict(gb=total / 1e9, seconds=active[-1][0], mean_mbit=total * 8 / 1e6 / active[-1][0] if active[-1][0] else 0.0,
                         slowest_minute_mbit=min(minutes) if minutes else 0.0,
                         first_tenth_mbit=sum(rates[:tenth]) / tenth if rates else 0.0, last_tenth_mbit=sum(rates[-tenth:]) / tenth if rates else 0.0)
    return out


def print_summary(result):
    for name, f in result.items():
        print(f'{name:9} {f["gb"]:7.1f} GB in {f["seconds"]:7.0f} s: mean {f["mean_mbit"]:7.0f} Mbit/s, slowest minute {f["slowest_minute_mbit"]:7.0f}, '
              f'first tenth {f["first_tenth_mbit"]:7.0f}, last tenth {f["last_tenth_mbit"]:7.0f}')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='command', required=True)
    s = sub.add_parser('serve')
    s.add_argument('bind')
    s.add_argument('--port', type=int, default=PORT)
    r = sub.add_parser('run')
    r.add_argument('peer')
    r.add_argument('--bind', default='')
    r.add_argument('--port', type=int, default=PORT)
    r.add_argument('--gb', type=float, default=200)
    r.add_argument('--streams', type=int, default=4)
    r.add_argument('--out', default='volume.csv')
    m = sub.add_parser('summary')
    m.add_argument('log')
    args = p.parse_args()
    if args.command == 'serve':
        serve(args)
    elif args.command == 'run':
        run(args)
    else:
        print_summary(summarise(args.log))


if __name__ == '__main__':
    main()
