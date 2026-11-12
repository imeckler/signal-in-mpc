#!/usr/bin/env python3
"""What the machine is, and whether its CPU keeps its speed under a sustained all-core load.

    python3 machine_check.py info --out logs/machine.json
    python3 machine_check.py load --minutes 30 --out logs/cpu-load.csv

info: CPU model, cores, the flags the engines care about (aes, pclmulqdq, avx2, bmi2, adx, sha_ni,
vaes; on arm64: aes, pmull, sha2), the hypervisor, memory, and the disk under the current
directory with a 2 GB write-and-read timing.

load: one process per core, each hashing a fixed 1 MiB buffer with SHA-256 in a loop (a fixed
benchmark: the same work every time). Once a minute it records the rate (MiB hashed per second,
all processes together), and from /proc/stat the share of time the hypervisor took away (steal),
plus user/system/idle. A provider that throttles shared cores shows as steal going up or the
rate going down while the load stays the same. Python standard library only; Linux only.
"""
import argparse, csv, hashlib, json, multiprocessing, os, platform, shutil, subprocess, sys, time

FLAGS = ['aes', 'pclmulqdq', 'sse4_2', 'avx', 'avx2', 'bmi2', 'adx', 'sha_ni', 'vaes', 'vpclmulqdq', 'avx512f', 'pmull', 'sha2', 'hypervisor']


def cpu_times():
    with open('/proc/stat') as f:
        fields = f.readline().split()[1:]
    names = ['user', 'nice', 'system', 'idle', 'iowait', 'irq', 'softirq', 'steal', 'guest', 'guest_nice']
    return dict(zip(names, (int(x) for x in fields)))


def info(args):
    cpu = open('/proc/cpuinfo').read()
    def field(*names):
        for line in cpu.split('\n'):
            if ':' in line and line.split(':')[0].strip() in names:
                return line.split(':', 1)[1].strip()
        return ''
    flags = set((field('flags') or field('Features')).split())
    mem = {l.split(':')[0]: int(l.split()[1]) for l in open('/proc/meminfo') if l.split()[1].isdigit()}
    out = dict(hostname_hash=hashlib.sha256(platform.node().encode()).hexdigest()[:8], kernel=platform.release(), machine=platform.machine(),
               cpu_model=field('model name', 'Model', 'CPU part'), logical_cpus=os.cpu_count(),
               flags={name: name in flags for name in FLAGS}, memory_total_gb=mem.get('MemTotal', 0) / 2 ** 20, memory_available_gb=mem.get('MemAvailable', 0) / 2 ** 20,
               swap_total_gb=mem.get('SwapTotal', 0) / 2 ** 20)
    try:
        out['virtualisation'] = subprocess.run(['systemd-detect-virt'], capture_output=True, text=True, timeout=10).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        out['virtualisation'] = 'unknown'
    usage = shutil.disk_usage('.')
    out['disk_total_gb'] = usage.total / 1e9
    out['disk_free_gb'] = usage.free / 1e9
    if usage.free > 6e9 and not args.no_disk_test:
        path = 'machine-check-disk.tmp'
        block = os.urandom(1 << 20)
        started = time.time()
        with open(path, 'wb') as f:
            for _ in range(2048):
                f.write(block)
            f.flush()
            os.fsync(f.fileno())
        out['disk_write_mb_per_s'] = 2048 / (time.time() - started)
        started = time.time()
        with open(path, 'rb') as f:
            while f.read(1 << 20):
                pass
        out['disk_read_mb_per_s_cached'] = 2048 / (time.time() - started)      # mostly the page cache; the write figure is the honest one
        os.unlink(path)
    text = json.dumps(out, indent=1)
    if args.out:
        open(args.out, 'w').write(text + '\n')
    print(text)


def worker(counter, stop):
    block = bytes(1 << 20)
    while not stop.value:
        for _ in range(64):
            hashlib.sha256(block).digest()
        with counter.get_lock():
            counter.value += 64


def load(args):
    n = args.processes or os.cpu_count()
    counter = multiprocessing.Value('Q', 0)
    stop = multiprocessing.Value('b', 0)
    children = [multiprocessing.Process(target=worker, args=(counter, stop), daemon=True) for _ in range(n)]
    for c in children:
        c.start()
    with open(args.out, 'w', newline='') as f:
        out = csv.writer(f)
        out.writerow(['minute', 'mib_per_second', 'steal_percent', 'user_percent', 'system_percent', 'idle_percent', 'processes'])
        previous_count, previous_times, previous_at = 0, cpu_times(), time.time()
        for minute in range(1, int(args.minutes) + 1):
            time.sleep(args.period)
            count, times, at = counter.value, cpu_times(), time.time()
            delta = {k: times[k] - previous_times[k] for k in times}
            total = sum(delta[k] for k in ('user', 'nice', 'system', 'idle', 'iowait', 'irq', 'softirq', 'steal')) or 1
            row = [minute, f'{(count - previous_count) / (at - previous_at):.1f}', f'{100 * delta["steal"] / total:.2f}', f'{100 * (delta["user"] + delta["nice"]) / total:.1f}',
                   f'{100 * delta["system"] / total:.1f}', f'{100 * delta["idle"] / total:.1f}', n]
            out.writerow(row)
            f.flush()
            print(f'minute {minute}: {row[1]} MiB/s, steal {row[2]} %', flush=True)
            previous_count, previous_times, previous_at = count, times, at
    stop.value = 1
    for c in children:
        c.join(timeout=10)


def summarise(path):
    rows = list(csv.DictReader(open(path)))
    rates = [float(r['mib_per_second']) for r in rows]
    steal = sorted(float(r['steal_percent']) for r in rows)
    return dict(minutes=len(rows), processes=int(rows[0]['processes']), first_rate=rates[0], lowest_rate=min(rates), last_rate=rates[-1],
                lowest_over_first=min(rates) / rates[0] if rates[0] else 0.0, steal_median=steal[len(steal) // 2], steal_max=steal[-1])


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='command', required=True)
    i = sub.add_parser('info')
    i.add_argument('--out', default='')
    i.add_argument('--no-disk-test', action='store_true')
    l = sub.add_parser('load')
    l.add_argument('--minutes', type=float, default=30)
    l.add_argument('--period', type=float, default=60, help='seconds per reported interval')
    l.add_argument('--processes', type=int, default=0, help='default: one per logical CPU')
    l.add_argument('--out', default='cpu-load.csv')
    s = sub.add_parser('summary')
    s.add_argument('log')
    args = p.parse_args()
    if not sys.platform.startswith('linux'):
        sys.exit('Linux only (reads /proc)')
    if args.command == 'info':
        info(args)
    elif args.command == 'load':
        load(args)
        print(json.dumps(summarise(args.out)))
    else:
        print(json.dumps(summarise(args.log), indent=1))


if __name__ == '__main__':
    main()
