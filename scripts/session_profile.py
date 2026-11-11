#!/usr/bin/env python3
"""Where the workers' time went, from a harness output file (or one or more run directories).

Usage: session_profile.py HARNESS_OUTPUT_OR_RUN_DIRECTORY...

For every two-party session found: the worker's profile by category (each second counted once),
and the individual durations of the per-message operations, so setup can be told from the
steady cost. Reads party 0's worker log; measurement only.
"""
import collections, pathlib, re, sys

RUNS = pathlib.Path(__file__).resolve().parents[1] / '.deps/two-party-comparison/signal-service-local-run'
GROUPS = [
    ('Boolean circuits (garbling and evaluation)', lambda l: l.startswith('boolean circuit:')),
    ('Field triples: generation', lambda l: l.startswith('field triples: generation')),
    ('Field multiplication rounds, triples in stock', lambda l: l.startswith('field multiplication rounds')),
    ('Field programs: local work', lambda l: l.startswith('field program (local work)')),
    ('Conversion masks: generation', lambda l: l.startswith('conversion masks: generate')),
    ('Conversions between the engines (use)', lambda l: l.startswith('conversion:')),
    ('Opening outputs and revealed server bytes', lambda l: l.startswith('open ')),
    ('Circuit loading', lambda l: l.startswith('circuit load')),
    ('Per-operation overhead (request agreement, sockets, the rest)', lambda l: l.startswith('operation ')),
]


def sessions(argument):
    path = pathlib.Path(argument)
    if path.is_dir():
        return [path]
    found = []
    for name in re.findall(r'signal-service-local-run/([0-9a-f]{16})', path.read_text()):
        if RUNS / name not in found:
            found.append(RUNS / name)
    return found


def show(directory):
    text = (directory / 'party-0.log').read_text()
    rows = re.findall(r'operation (\d+) ok seconds=([\d.e+-]+) and_gates=(\d+) emp_sent_bytes=(\d+) field_sent_bytes=(\d+) field_products=(\d+)', text)
    profile = re.findall(r'tls-worker-v3 profile seconds=([\d.e+-]+) calls=(\d+) and_gates=(\d+) field_products=(\d+) boolean_bytes=(\d+) field_bytes=(\d+) label=(.*)', text)
    if not rows:
        return
    mode = re.search(r'security_mode=(\S+)', text)
    total = float(rows[-1][1])
    print('\n=== %s  %s  worker time %.1f s  AND %.2fM  field products %s' % (directory.name, mode.group(1) if mode else '', total, int(rows[-1][2]) / 1e6, rows[-1][5]))
    startup = float(rows[0][1]) if rows[0][0] == '0' else 0.0
    print('  start-up before the first operation (engines, first conversion masks): %.1f s' % startup)
    if profile:
        print('  by category:')
        grouped = collections.OrderedDict((name, [0.0, 0, 0, 0, 0]) for name, _ in GROUPS)
        detail = collections.defaultdict(list)
        for seconds, calls, gates, products, bb, fb, label in profile:
            for name, test in GROUPS:
                if test(label):
                    g = grouped[name]
                    g[0] += float(seconds); g[1] += int(calls); g[2] += int(gates); g[3] += int(products); g[4] += int(bb) + int(fb)
                    detail[name].append((float(seconds), int(calls), int(gates), int(products), label))
                    break
        accounted = sum(g[0] for g in grouped.values())
        for name, g in grouped.items():
            print('    %6.1f s %4.0f%%  AND %6.2fM  products %6d  sent %7.2f GB  %s' % (g[0], 100 * g[0] / total, g[2] / 1e6, g[3], g[4] / 1e9, name))
        print('    %6.1f s %4.0f%%  not in any scope (start-up, waiting for the controller)' % (total - accounted, 100 * (total - accounted) / total))
        for name in ('Boolean circuits (garbling and evaluation)', 'Field triples: generation', 'Field multiplication rounds, triples in stock',
                     'Per-operation overhead (request agreement, sockets, the rest)'):
            top = sorted(detail[name], reverse=True)[:8]
            if top:
                print('  largest in "%s":' % name)
                for seconds, calls, gates, products, label in top:
                    if seconds >= 0.005 * total:
                        print('    %6.2f s  x%-4d AND %6.2fM  products %6d  %s' % (seconds, calls, gates / 1e6, products, label.split(': ', 1)[-1]))
    # Time outside the worker, by the operation that followed it.
    busy = re.findall(r'operation (\d+) ok seconds=([\d.e+-]+) .* busy=([\d.e+-]+)', text)
    if busy:
        outside = collections.defaultdict(lambda: [0.0, 0]); last = 0.0
        for op, seconds, inside in busy:
            gap = float(seconds) - last - float(inside); last = float(seconds)
            outside[int(op)][0] += max(gap, 0.0); outside[int(op)][1] += 1
        what = {43: 'before a reveal call: the controller parsing what was just revealed', 12: 'before opening a record: waiting for the server, polling',
                41: 'before a send: building the message', 42: 'before the request frame: building the request around the envelope',
                13: 'before sealing a record', 33: 'before joint randomness', 38: 'before sealing contact state: database client', 36: 'before a contact key: database client',
                37: 'before opening contact state', 39: 'before an exchange between parties: database client', 50: 'before receive part 1', 51: 'before receive part 2: decapsulation',
                17: 'polling', 10: 'before a socket send', 11: 'before a socket receive'}
        print('  time outside the worker (controller, database client, server), %.1f s in all:' % sum(v[0] for v in outside.values()))
        for op, (seconds, count) in sorted(outside.items(), key=lambda kv: -kv[1][0])[:8]:
            if seconds >= 0.005 * total:
                print('    %6.1f s  x%-4d %s' % (seconds, count, what.get(op, 'before operation %d' % op)))
    # Individual durations of the repeated operations, in order.
    previous = 0.0
    each = collections.defaultdict(list)
    for op, seconds, gates, _, _, products in rows:
        each[int(op)].append(float(seconds) - previous)
        previous = float(seconds)
    names = {41: 'send: session encryption + sealed sender', 42: 'send: request frame', 13: 'seal a TLS record', 12: 'open a TLS record',
             43: 'reveal server bytes (calls)', 36: 'contact key from shares', 37: 'contact state open', 38: 'contact state seal',
             50: 'receive: unseal, certificate, prekey part', 51: 'receive: agreements, session, text'}
    print('  repeated operations, each call in order (seconds):')
    for op, label in names.items():
        if op in each:
            values = each[op]
            if op == 43:
                print('    %-44s %d calls, %.1f s in all, %.0f ms each' % (label, len(values), sum(values), 1000 * sum(values) / len(values)))
            else:
                print('    %-44s %s' % (label, ' '.join('%.2f' % v for v in values)))


for argument in sys.argv[1:]:
    for directory in sessions(argument):
        show(directory)
