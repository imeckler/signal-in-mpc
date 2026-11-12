#!/usr/bin/env python3
"""Round-trip time to the other machine over hours: one ping every INTERVAL seconds, each logged.

    python3 rtt_log.py run 10.77.0.2 --hours 24 --out logs/rtt.csv     (run it under nohup or tmux)
    python3 rtt_log.py summary logs/rtt.csv

The log has one row per probe: unix time, sequence number, round trip in ms (empty: no answer).
The summary gives, per hour and overall: probes, lost, median, 95th and 99th percentile, maximum.
Needs only `ping` (iputils). Run it from one machine; the other needs nothing.
"""
import argparse, csv, re, subprocess, sys, time


def percentile(sorted_values, q):
    if not sorted_values:
        return float('nan')
    return sorted_values[min(len(sorted_values) - 1, int(q * len(sorted_values)))]


def run(args):
    deadline = time.time() + args.hours * 3600
    with open(args.out, 'a', newline='') as f:
        out = csv.writer(f)
        if f.tell() == 0:
            out.writerow(['unix_time', 'seq', 'rtt_ms'])
        base = 0
        while time.time() < deadline:
            # -D: timestamps; -O: report a missing answer as soon as the next probe goes out.
            count = max(1, int(min(3600, deadline - time.time()) / args.interval))
            ping = subprocess.Popen(['ping', '-D', '-O', '-n', '-i', str(args.interval), '-c', str(count), args.peer],
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            for line in ping.stdout:
                stamp = re.match(r'\[(\d+\.\d+)\]', line)
                when = float(stamp[1]) if stamp else time.time()
                answer = re.search(r'icmp_seq=(\d+) .*time=([\d.]+) ms', line)
                missing = re.search(r'no answer yet for icmp_seq=(\d+)', line)
                if answer:
                    out.writerow([f'{when:.3f}', base + int(answer[1]), answer[2]])
                elif missing:
                    out.writerow([f'{when:.3f}', base + int(missing[1]), ''])
                f.flush()
            ping.wait()
            base += count
            if ping.returncode not in (0, 1):
                time.sleep(5)             # unreachable or name failure: keep trying, the gap shows in the log


def summarise(path):
    """{'hours': [row...], 'all': row} with row = dict(start, probes, lost, median, p95, p99, max)."""
    buckets = {}
    with open(path) as f:
        for row in csv.DictReader(f):
            hour = int(float(row['unix_time']) // 3600)
            buckets.setdefault(hour, []).append(float(row['rtt_ms']) if row['rtt_ms'] else None)

    def row(start, values):
        got = sorted(v for v in values if v is not None)
        return dict(start=start, probes=len(values), lost=len(values) - len(got), median=percentile(got, 0.5),
                    p95=percentile(got, 0.95), p99=percentile(got, 0.99), max=got[-1] if got else float('nan'))
    hours = [row(time.strftime('%Y-%m-%d %H:00Z', time.gmtime(h * 3600)), v) for h, v in sorted(buckets.items())]
    everything = [v for _, values in sorted(buckets.items()) for v in values]
    return dict(hours=hours, all=row('all', everything))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='command', required=True)
    r = sub.add_parser('run')
    r.add_argument('peer')
    r.add_argument('--hours', type=float, default=24)
    r.add_argument('--interval', type=float, default=0.5, help='seconds between probes (0.2 or more without root)')
    r.add_argument('--out', default='rtt.csv')
    s = sub.add_parser('summary')
    s.add_argument('log')
    args = p.parse_args()
    if args.command == 'run':
        run(args)
    else:
        result = summarise(args.log)
        print(f'{"hour":17} {"probes":>7} {"lost":>5} {"median":>8} {"p95":>8} {"p99":>8} {"max":>8}   (ms)')
        for h in result['hours'] + [result['all']]:
            print(f'{h["start"]:17} {h["probes"]:7} {h["lost"]:5} {h["median"]:8.3f} {h["p95"]:8.3f} {h["p99"]:8.3f} {h["max"]:8.3f}')


if __name__ == '__main__':
    main()
