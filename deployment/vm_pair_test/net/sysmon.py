#!/usr/bin/env python3
"""Background record of the machine while the benchmark runs: every 10 seconds the CPU shares
(steal, user, system, idle), memory still available, and the tunnel's byte counters.

    nohup python3 sysmon.py --out logs/sysmon.csv &        (stop it with kill when the benchmark is done)

Columns: unix_time, steal_percent, user_percent, system_percent, idle_percent, mem_available_gb,
mem_used_gb, rx_bytes, tx_bytes (of --interface, default vmpair; empty if it does not exist).
Python standard library only; Linux only.
"""
import argparse, csv, time


def cpu_times():
    with open('/proc/stat') as f:
        fields = [int(x) for x in f.readline().split()[1:]]
    names = ['user', 'nice', 'system', 'idle', 'iowait', 'irq', 'softirq', 'steal']
    return dict(zip(names, fields))


def memory():
    values = {}
    with open('/proc/meminfo') as f:
        for line in f:
            parts = line.split()
            values[parts[0].rstrip(':')] = int(parts[1])
    return values['MemAvailable'] / 2 ** 20, (values['MemTotal'] - values['MemAvailable']) / 2 ** 20


def counter(interface, name):
    try:
        with open(f'/sys/class/net/{interface}/statistics/{name}') as f:
            return int(f.read())
    except OSError:
        return ''


def summarise(path):
    rows = list(csv.DictReader(open(path)))
    if not rows:
        return None
    steal = sorted(float(r['steal_percent']) for r in rows)
    out = dict(samples=len(rows), steal_median=steal[len(steal) // 2], steal_p95=steal[min(len(steal) - 1, int(0.95 * len(steal)))], steal_max=steal[-1],
               mem_available_min_gb=min(float(r['mem_available_gb']) for r in rows), mem_used_max_gb=max(float(r['mem_used_gb']) for r in rows))
    counted = [r for r in rows if r['rx_bytes'] != '']
    if len(counted) > 1:
        out['tunnel_rx_gb'] = (int(counted[-1]['rx_bytes']) - int(counted[0]['rx_bytes'])) / 1e9
        out['tunnel_tx_gb'] = (int(counted[-1]['tx_bytes']) - int(counted[0]['tx_bytes'])) / 1e9
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', default='sysmon.csv')
    p.add_argument('--period', type=float, default=10)
    p.add_argument('--interface', default='vmpair')
    args = p.parse_args()
    with open(args.out, 'a', newline='') as f:
        out = csv.writer(f)
        if f.tell() == 0:
            out.writerow(['unix_time', 'steal_percent', 'user_percent', 'system_percent', 'idle_percent', 'mem_available_gb', 'mem_used_gb', 'rx_bytes', 'tx_bytes'])
        previous = cpu_times()
        while True:
            time.sleep(args.period)
            now = cpu_times()
            delta = {k: now[k] - previous[k] for k in now}
            total = sum(delta.values()) or 1
            available, used = memory()
            out.writerow([f'{time.time():.0f}', f'{100 * delta["steal"] / total:.2f}', f'{100 * (delta["user"] + delta["nice"]) / total:.1f}',
                          f'{100 * delta["system"] / total:.1f}', f'{100 * delta["idle"] / total:.1f}', f'{available:.2f}', f'{used:.2f}',
                          counter(args.interface, 'rx_bytes'), counter(args.interface, 'tx_bytes')])
            f.flush()
            previous = now


if __name__ == '__main__':
    main()
