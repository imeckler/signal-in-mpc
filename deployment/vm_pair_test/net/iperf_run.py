#!/usr/bin/env python3
"""iperf3 between the two machines inside the tunnel, logged every second.

On machine b (the far side), leave a server running:      python3 iperf_run.py server 10.77.0.2
On machine a, run the sequence (2.5 hours by default):    python3 iperf_run.py client 10.77.0.2 --bind 10.77.0.1

The sequence, each for --seconds (default 1800):
    a-to-b-1      one stream, a sends
    b-to-a-1      one stream, b sends (iperf3 -R)
    a-to-b-8      eight parallel streams, a sends
    b-to-a-8      eight parallel streams, b sends
    both-4        both directions at once, four streams each way (iperf3 --bidir)
--tests picks a subset. Logs: LOGS/iperf-TEST.log (iperf3's own text, in Mbit/s, one line per
second and stream). `summary` reads them back: mean, the lowest 10-second mean, and the mean of
the last tenth against the first tenth of the run (a throttle shows there).
"""
import argparse, pathlib, re, statistics, subprocess, sys

TESTS = {
    'a-to-b-1': ['-P', '1'],
    'b-to-a-1': ['-P', '1', '-R'],
    'a-to-b-8': ['-P', '8'],
    'b-to-a-8': ['-P', '8', '-R'],
    'both-4': ['-P', '4', '--bidir'],
}
ROW = re.compile(r'\[\s*(SUM|\d+)\]\s*(?:\[(TX|RX)-[CS]\])?\s*(\d+\.\d+)-(\d+\.\d+)\s+sec\s+[\d.]+\s+\w+\s+([\d.]+)\s+Mbits/sec(?!.*(sender|receiver))')


def series(path):
    """{'TX': [Mbit/s per second...], 'RX': [...]} from one log (single direction: 'TX' only; -R: 'RX')."""
    text = pathlib.Path(path).read_text(errors='replace')
    reverse = 'Reverse mode' in text
    sums, streams = {}, {}
    for line in text.split('\n'):
        m = ROW.search(line)
        if not m or not 0.5 <= float(m[4]) - float(m[3]) <= 1.5:      # skip whole-run summary rows and the short last interval
            continue
        direction = m[2] or ('RX' if reverse else 'TX')
        if m[1] == 'SUM':
            sums.setdefault(direction, {})[m[3]] = float(m[5])
        else:
            rows = streams.setdefault(direction, {})
            rows[m[3]] = rows.get(m[3], 0.0) + float(m[5])
    # With several streams iperf3 prints a [SUM] row per interval: use those alone (the streams'
    # own rows can carry slightly different interval bounds). One stream: its rows.
    out = {}
    for direction in set(sums) | set(streams):
        rows = sums.get(direction) or streams[direction]
        out[direction] = [value for _, value in sorted(rows.items(), key=lambda kv: float(kv[0]))]
    return out


def figures(values):
    if len(values) < 20:
        return None
    tenth = max(10, len(values) // 10)
    windows = [sum(values[i:i + 10]) / 10 for i in range(0, len(values) - 9, 10)]
    return dict(seconds=len(values), mean=sum(values) / len(values), median=statistics.median(values), lowest_10s=min(windows),
                first_tenth=sum(values[:tenth]) / tenth, last_tenth=sum(values[-tenth:]) / tenth)


def summarise(logs):
    out = {}
    for name in TESTS:
        path = pathlib.Path(logs) / f'iperf-{name}.log'
        if path.exists():
            out[name] = {direction: figures(values) for direction, values in series(path).items()}
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='command', required=True)
    s = sub.add_parser('server')
    s.add_argument('bind')
    s.add_argument('--port', type=int, default=5201)
    c = sub.add_parser('client')
    c.add_argument('peer')
    c.add_argument('--bind', default='')
    c.add_argument('--port', type=int, default=5201)
    c.add_argument('--seconds', type=int, default=1800)
    c.add_argument('--tests', default=','.join(TESTS))
    c.add_argument('--logs', default='logs')
    r = sub.add_parser('summary')
    r.add_argument('logs')
    args = p.parse_args()
    if args.command == 'server':
        sys.exit(subprocess.call(['iperf3', '-s', '-B', args.bind, '-p', str(args.port)]))
    if args.command == 'client':
        pathlib.Path(args.logs).mkdir(parents=True, exist_ok=True)
        for name in args.tests.split(','):
            log = pathlib.Path(args.logs) / f'iperf-{name}.log'
            log.unlink(missing_ok=True)
            command = ['iperf3', '-c', args.peer, '-p', str(args.port), '-t', str(args.seconds), '-i', '1', '-f', 'm', '--forceflush', '--logfile', str(log)] + TESTS[name]
            if args.bind:
                command += ['-B', args.bind]
            print(f'{name}: {args.seconds} s ...', flush=True)
            code = subprocess.call(command)
            if code != 0:
                print(f'{name}: iperf3 exited with {code}; see {log}', flush=True)
    for name, directions in summarise(args.logs).items():
        for direction, f in directions.items():
            if f:
                print(f'{name:9} {direction}: mean {f["mean"]:8.0f} Mbit/s, lowest 10 s {f["lowest_10s"]:8.0f}, first tenth {f["first_tenth"]:8.0f}, last tenth {f["last_tenth"]:8.0f}  ({f["seconds"]} s)')


if __name__ == '__main__':
    main()
