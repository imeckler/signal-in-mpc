#!/usr/bin/env python3
"""Turn the logs of both machines into one report with pass/fail against the criteria of README.md.

Copy each machine's vm-pair/logs/ directory here (for example to logs-a/ and logs-b/), then:

    python3 collect.py --a logs-a --b logs-b --eur-month-a 59.49 --eur-month-b 36.99 --out report.md

Machine a is the one that ran party 0, the ping log, the iperf3 client and the volume test.
Anything that was not run is reported as "not run" and counts as not passed. Prices are only
used for the cost arithmetic: monthly price of each machine, and a price per TB sent beyond the
allowance if a provider meters traffic (--eur-per-tb-a/-b, default 0).
The thresholds are the constants below; README.md explains each.
"""
import argparse, json, math, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE / 'net'))
import iperf_run, machine_check, rtt_log, sysmon, volume_test          # noqa: E402
from run_bench import summarise as bench_summary                        # noqa: E402

# ---- Criteria (README.md, "Pass criteria").
STEAL_MEDIAN_MAX = 2.0          # percent, during the 30-minute all-core load and during the benchmark
STEAL_PEAK_MAX = 5.0            # percent, any one minute of the load test
LOAD_RATE_FLOOR = 0.90          # lowest minute of the fixed benchmark / its first minute
RTT_P99_OVER_MEDIAN = 1.5       # per hour
RTT_GOOD_HOURS = 0.95           # share of hours that must meet it
RTT_LOSS_MAX = 0.0001           # 0.01 %
RATE_KEEP = 0.80                # last tenth of a long transfer / first tenth
RATE_DIP = 0.50                 # lowest 10 s (iperf3) or minute (volume) / mean
MODES = {
    # seconds per message for one pair (median), Mbit/s needed, which directions carry it
    'malicious': dict(max_seconds=15.0, min_mbit=400.0, both_ways=True),
    'semi-honest': dict(max_seconds=3.0, min_mbit=250.0, both_ways=False),
}
DRIFT_MAX = 1.25                # late median / early median of the per-message time
ROUND_BOUND_MAX = 60.0          # seconds for a contact's first-send preparation, and for the receive sequence
MEMORY_HEADROOM_GB = 2.0
HOURS_PER_MONTH = 730.0


def load_json(path):
    return json.loads(path.read_text()) if path.exists() else None


def fmt(x, digits=2):
    return 'n/a' if x is None or (isinstance(x, float) and math.isnan(x)) else f'{x:.{digits}f}'


class Report:
    def __init__(self):
        self.lines, self.checks = [], []

    def h(self, text):
        self.lines += ['', '## ' + text, '']

    def p(self, text=''):
        self.lines.append(text)

    def table(self, header, rows):
        self.lines.append('| ' + ' | '.join(header) + ' |')
        self.lines.append('|' + '---|' * len(header))
        for row in rows:
            self.lines.append('| ' + ' | '.join(str(c) for c in row) + ' |')
        self.lines.append('')

    def check(self, scope, name, passed, detail):
        """scope: 'both', 'malicious' or 'semi-honest'. passed None = not run."""
        self.checks.append((scope, name, passed, detail))
        mark = 'not run' if passed is None else ('pass' if passed else 'FAIL')
        self.lines.append(f'- **{mark}**: {name}: {detail}')


def machines(r, dirs):
    r.h('Machines')
    rows, infos = [], {}
    for side, d in dirs.items():
        info = load_json(d / 'machine.json')
        infos[side] = info
        if not info:
            rows.append([side, 'not run', '', '', '', '', ''])
            continue
        flags = ' '.join(k for k, v in info['flags'].items() if v and k != 'hypervisor')
        rows.append([side, info['cpu_model'], info['logical_cpus'], fmt(info['memory_total_gb'], 1), info.get('virtualisation', ''), flags,
                     fmt(info.get('disk_write_mb_per_s'), 0)])
    r.table(['machine', 'CPU', 'logical CPUs', 'memory GB', 'virtualisation', 'flags', 'disk write MB/s'], rows)
    for side, info in infos.items():
        if not info:
            r.check('both', f'machine {side}: CPU features', None, 'machine_check.py info was not run')
        elif info['machine'] == 'x86_64':
            need = [f for f in ('aes', 'pclmulqdq', 'avx2') if not info['flags'].get(f)]
            r.check('both', f'machine {side}: CPU features', not need, 'aes, pclmulqdq and avx2 present' if not need else 'missing ' + ', '.join(need))
        else:
            need = [f for f in ('aes', 'pmull') if not info['flags'].get(f)]
            r.check('both', f'machine {side}: CPU features', not need, 'aes and pmull present' if not need else 'missing ' + ', '.join(need))
    return infos


def cpu_load(r, dirs):
    r.h('CPU under a sustained all-core load')
    rows = []
    results = {}
    for side, d in dirs.items():
        path = d / 'cpu-load.csv'
        results[side] = machine_check.summarise(path) if path.exists() else None
        s = results[side]
        rows.append([side] + (['not run'] * 6 if not s else [s['minutes'], s['processes'], fmt(s['first_rate'], 0), fmt(s['lowest_rate'], 0), fmt(s['steal_median']), fmt(s['steal_max'])]))
    r.table(['machine', 'minutes', 'processes', 'first minute MiB/s', 'lowest minute MiB/s', 'steal median %', 'steal max %'], rows)
    for side, s in results.items():
        if not s:
            r.check('both', f'machine {side}: keeps its speed under load', None, 'machine_check.py load was not run')
            continue
        ok = s['lowest_over_first'] >= LOAD_RATE_FLOOR and s['steal_median'] <= STEAL_MEDIAN_MAX and s['steal_max'] <= STEAL_PEAK_MAX and s['minutes'] >= 25
        r.check('both', f'machine {side}: keeps its speed under load', ok,
                f'lowest minute is {100 * s["lowest_over_first"]:.0f} % of the first (need {100 * LOAD_RATE_FLOOR:.0f} %), steal median {s["steal_median"]:.2f} % (max {STEAL_MEDIAN_MAX}), '
                f'worst minute {s["steal_max"]:.2f} % (max {STEAL_PEAK_MAX}), {s["minutes"]} minutes (need 25)')


def rtt(r, a):
    r.h('Round-trip time inside the tunnel')
    path = a / 'rtt.csv'
    if not path.exists():
        r.check('both', 'round-trip time', None, 'rtt_log.py was not run')
        return None
    s = rtt_log.summarise(path)
    r.table(['hour (UTC)', 'probes', 'lost', 'median ms', 'p95 ms', 'p99 ms', 'max ms'],
            [[h['start'], h['probes'], h['lost'], fmt(h['median'], 3), fmt(h['p95'], 3), fmt(h['p99'], 3), fmt(h['max'], 3)] for h in s['hours'] + [s['all']]])
    full = [h for h in s['hours'] if h['probes'] >= 600]
    good = [h for h in full if h['p99'] <= RTT_P99_OVER_MEDIAN * h['median']]
    loss = s['all']['lost'] / max(1, s['all']['probes'])
    ok = bool(full) and len(good) >= RTT_GOOD_HOURS * len(full) and loss <= RTT_LOSS_MAX
    r.check('both', 'round-trip time is steady', ok if full else None,
            f'{len(good)} of {len(full)} hours have a 99th percentile within {RTT_P99_OVER_MEDIAN} x the median (need {100 * RTT_GOOD_HOURS:.0f} %); '
            f'loss {100 * loss:.4f} % (max {100 * RTT_LOSS_MAX:.2f} %); overall median {s["all"]["median"]:.3f} ms, 99th {s["all"]["p99"]:.3f} ms')
    return s['all']


def throughput(r, a):
    r.h('Throughput inside the tunnel (iperf3)')
    s = iperf_run.summarise(a)
    rows = []
    for name, directions in s.items():
        for direction, f in directions.items():
            if f:
                rows.append([name, 'a sends' if direction == 'TX' else 'b sends', f['seconds'], fmt(f['mean'], 0), fmt(f['lowest_10s'], 0), fmt(f['first_tenth'], 0), fmt(f['last_tenth'], 0)])
    if rows:
        r.table(['test', 'direction', 'seconds', 'mean Mbit/s', 'lowest 10 s', 'first tenth', 'last tenth'], rows)

    def steady(f):
        return f and f['last_tenth'] >= RATE_KEEP * f['first_tenth'] and f['lowest_10s'] >= RATE_DIP * f['mean']

    def shape(f):
        return (f'last tenth at {100 * f["last_tenth"] / max(1e-9, f["first_tenth"]):.0f} % of the first (need {100 * RATE_KEEP:.0f} %), '
                f'lowest 10 s at {100 * f["lowest_10s"] / max(1e-9, f["mean"]):.0f} % of the mean (need {100 * RATE_DIP:.0f} %)')
    both = s.get('both-4', {})
    two = [both.get('TX'), both.get('RX')]
    for mode, c in MODES.items():
        if c['both_ways']:
            if not all(two):
                r.check(mode, f'{mode}: sustained throughput both ways at once', None, 'the both-4 test was not run')
                continue
            ok = all(f['mean'] >= c['min_mbit'] and steady(f) for f in two)
            r.check(mode, f'{mode}: sustained throughput both ways at once', ok,
                    f'{two[0]["mean"]:.0f} and {two[1]["mean"]:.0f} Mbit/s (need {c["min_mbit"]:.0f} each way); a sends: {shape(two[0])}; b sends: {shape(two[1])}')
        else:
            best = [f for name in ('a-to-b-8', 'b-to-a-8', 'a-to-b-1', 'b-to-a-1') for f in s.get(name, {}).values() if f]
            if not best:
                r.check(mode, f'{mode}: sustained throughput one way', None, 'no one-way iperf3 test was run')
                continue
            top = max(best, key=lambda f: f['mean'])
            r.check(mode, f'{mode}: sustained throughput one way', top['mean'] >= c['min_mbit'] and bool(steady(top)),
                    f'best direction {top["mean"]:.0f} Mbit/s (need {c["min_mbit"]:.0f}); {shape(top)}; put the garbling party (party 0) on the sending end of it')
    return s


def volume(r, a):
    r.h('Volume test')
    path = a / 'volume.csv'
    if not path.exists():
        r.check('both', 'no slowdown after a large volume', None, 'volume_test.py was not run')
        return
    s = volume_test.summarise(path)
    r.table(['direction', 'GB', 'seconds', 'mean Mbit/s', 'slowest minute', 'first tenth', 'last tenth'],
            [[('a sends' if k == 'sent' else 'b sends'), fmt(f['gb'], 1), fmt(f['seconds'], 0), fmt(f['mean_mbit'], 0), fmt(f['slowest_minute_mbit'], 0),
              fmt(f['first_tenth_mbit'], 0), fmt(f['last_tenth_mbit'], 0)] for k, f in s.items()])
    ok = all(f['last_tenth_mbit'] >= RATE_KEEP * f['first_tenth_mbit'] and f['slowest_minute_mbit'] >= RATE_DIP * f['mean_mbit'] for f in s.values())
    r.check('both', 'no slowdown after a large volume', ok,
            '; '.join(f'{"a" if k == "sent" else "b"} sent {f["gb"]:.0f} GB, last tenth at {100 * f["last_tenth_mbit"] / max(1e-9, f["first_tenth_mbit"]):.0f} % of the first' for k, f in s.items())
            + f' (need {100 * RATE_KEEP:.0f} %); slowest minute at '
            + ' and '.join(f'{100 * f["slowest_minute_mbit"] / max(1e-9, f["mean_mbit"]):.0f} %' for f in s.values())
            + f' of the mean (need {100 * RATE_DIP:.0f} %). Also check both providers\' traffic graphs and mailboxes by hand.')


def results_of(d, stage, party):
    s = load_json(d / stage / f'summary-p{party}.json')
    return s


def benchmark(r, dirs, infos, args):
    r.h('Our software: one worker pair')
    sides = {'a': results_of(dirs['a'], 'one-pair', 0), 'b': results_of(dirs['b'], 'one-pair', 1)}
    two = {'a': results_of(dirs['a'], 'two-pairs', 0), 'b': results_of(dirs['b'], 'two-pairs', 1)}
    monitors = {side: (sysmon.summarise(d / 'sysmon.csv') if (d / 'sysmon.csv').exists() else None) for side, d in dirs.items()}

    def row(summary, step, mode, pair=0):
        if not summary:
            return None
        for x in summary['results']:
            if x['step'] == step and x['mode'] == mode and x['pair'] == pair and x['exit_code'] == 0 and x['passed']:
                return x
        return None
    figures = {}
    table = []
    for mode, c in MODES.items():
        a, b = row(sides['a'], 'bench', mode), row(sides['b'], 'bench', mode)
        if not (a and b):
            r.check(mode, f'{mode}: per-message time', None, 'the benchmark did not complete on both machines')
            continue
        gb = (a['boolean_sent_bytes_per_iteration'] + a['field_sent_bytes_per_iteration'], b['boolean_sent_bytes_per_iteration'] + b['field_sent_bytes_per_iteration'])
        figures[mode] = dict(seconds=a['seconds_median'], gb_a=gb[0] / 1e9, gb_b=gb[1] / 1e9)
        table.append([mode, a['iterations'], fmt(a['seconds_median'], 3), fmt(a['seconds_p95'], 3), fmt(a['seconds_early_median'], 3), fmt(a['seconds_late_median'], 3),
                      fmt(a['and_gates_per_iteration'] / 1e6, 2), fmt(a['field_products_per_iteration'], 0), fmt(gb[0] / 1e9, 3), fmt(gb[1] / 1e9, 3)])
    if table:
        r.table(['mode', 'messages', 'median s', 'p95 s', 'early median s', 'late median s', 'M AND', 'field products', 'GB sent by a', 'GB sent by b'], table)
    for mode, c in MODES.items():
        a = row(sides['a'], 'bench', mode)
        if mode not in figures:
            continue
        r.check(mode, f'{mode}: per-message time', a['seconds_median'] <= c['max_seconds'],
                f'{a["seconds_median"]:.2f} s median, {3600 / a["seconds_median"]:.0f} messages an hour for one pair (need at most {c["max_seconds"]:.0f} s)')
        drift = a['seconds_late_median'] / a['seconds_early_median']
        enough = a['iterations'] >= 50
        r.check(mode, f'{mode}: per-message time does not drift upward', (drift <= DRIFT_MAX) if enough else None,
                f'late median is {drift:.2f} x the early median (max {DRIFT_MAX}) over {a["iterations"]} messages' + ('' if enough else ' (need at least 50 messages to judge)'))
    # Round-bound operations.
    r.p('Round-bound operations (seconds, with the sequential field rounds they took):')
    r.p()
    rows = []
    for mode in MODES:
        a = row(sides['a'], 'bench', mode)
        receive = row(sides['a'], 'receive', mode)
        prepare = row(sides['a'], 'prepare', mode)
        first = a['stages'].get('BENCH first-send-total') if a else None
        if first:
            rows.append([mode, "a contact's first send (table and long-term agreement)", fmt(first['seconds'], 1), int(first['field_mul_rounds'] + first['field_openings'])])
        if receive:
            earlier = [v for k, v in receive['stages'].items() if k.startswith('RESULT earlier: unseal') or k.startswith('RESULT earlier: base key')]
            hinted = [v for k, v in receive['stages'].items() if k.startswith('RESULT hinted:')]
            lift = [v for k, v in receive['stages'].items() if k.startswith('RESULT earlier: server key')]
            if earlier:
                rows.append([mode, 'first message received, field programs (default programs)', fmt(sum(v['seconds'] for v in earlier), 1), int(sum(v['mul_rounds'] + v['openings'] for v in earlier))])
            if lift:
                rows.append([mode, 'server key lift (once per worker process)', fmt(sum(v['seconds'] for v in lift), 1), int(sum(v['mul_rounds'] + v['openings'] for v in lift))])
            if hinted:
                rows.append([mode, 'first message received, field programs (constant-depth programs, TLS_WORKER_HINTED=1)', fmt(sum(v['seconds'] for v in hinted), 1),
                             int(sum(v['mul_rounds'] + v['openings'] for v in hinted))])
        if prepare:
            hint = [v for k, v in prepare['stages'].items() if k.startswith('RESULT prepare, hinted') or k.startswith('RESULT long-term agreements from the tables')]
            if hint:
                rows.append([mode, "a contact's first send (constant-depth programs)", fmt(sum(v['seconds'] for v in hint), 1), int(sum(v['mul_rounds'] + v['openings'] for v in hint))])
    if rows:
        r.table(['mode', 'operation', 'seconds', 'sequential rounds'], rows)
    for mode in MODES:
        a = row(sides['a'], 'bench', mode)
        receive = row(sides['a'], 'receive', mode)
        first = a['stages'].get('BENCH first-send-total') if a else None
        earlier = [v for k, v in receive['stages'].items() if k.startswith('RESULT earlier: unseal') or k.startswith('RESULT earlier: base key')] if receive else []
        if not first or not earlier:
            r.check(mode, f'{mode}: round-bound operations fit the time limit', None, 'the benchmark or the receive step did not complete')
            continue
        worst = max(first['seconds'], sum(v['seconds'] for v in earlier))
        r.check(mode, f'{mode}: round-bound operations fit the time limit', worst <= ROUND_BOUND_MAX,
                f'first send {first["seconds"]:.1f} s, receive sequence {sum(v["seconds"] for v in earlier):.1f} s (each at most {ROUND_BOUND_MAX:.0f} s; the Signal server drops an idle connection after 90 s)')
    # Memory and steal during the benchmark.
    r.h('Memory and CPU while the benchmark ran')
    rows = []
    for side in ('a', 'b'):
        s, m, info = sides[side], monitors[side], infos.get(side)
        rows.append([side, fmt(s['largest_child_peak_rss_gb']) if s else 'not run', fmt(m['mem_used_max_gb']) if m else 'not run', fmt(m['mem_available_min_gb']) if m else 'not run',
                     fmt(info['memory_total_gb'], 1) if info else 'not run', fmt(m['steal_median']) if m else 'not run', fmt(m['steal_p95']) if m else 'not run', fmt(m['steal_max']) if m else 'not run'])
    r.table(['machine', 'largest process GB (one pair)', 'most memory in use GB (whole run)', 'least available GB', 'installed GB', 'steal median %', 'steal p95 %', 'steal max %'], rows)
    for side in ('a', 'b'):
        s, m, info = sides[side], monitors[side], infos.get(side)
        if not (s and m and info):
            r.check('both', f'machine {side}: memory', None, 'summary, sysmon.csv or machine.json missing')
            r.check('both', f'machine {side}: no steal while the benchmark ran', None, 'sysmon.csv missing')
            continue
        r.check('both', f'machine {side}: memory', m['mem_available_min_gb'] >= MEMORY_HEADROOM_GB,
                f'at least {m["mem_available_min_gb"]:.1f} GB stayed available (need {MEMORY_HEADROOM_GB:.0f}); one pair\'s largest process {s["largest_child_peak_rss_gb"]:.1f} GB of {info["memory_total_gb"]:.0f} GB')
        r.check('both', f'machine {side}: no steal while the benchmark ran', m['steal_median'] <= STEAL_MEDIAN_MAX and m['steal_p95'] <= STEAL_PEAK_MAX,
                f'steal median {m["steal_median"]:.2f} % (max {STEAL_MEDIAN_MAX}), 95th percentile {m["steal_p95"]:.2f} % (max {STEAL_PEAK_MAX})')
    # Two pairs.
    r.h('Two worker pairs on the same machines')
    rows = []
    scaling = {}
    for mode in MODES:
        one = row(sides['a'], 'bench', mode)
        pairs = [row(two['a'], 'bench', mode, pair) for pair in (0, 1)]
        if not one or not all(pairs):
            rows.append([mode, 'not run', '', '', ''])
            continue
        single = 3600 / one['seconds_median']
        together = sum(3600 / p['seconds_median'] for p in pairs)
        scaling[mode] = together / single
        rows.append([mode, fmt(single, 0), fmt(together, 0), fmt(together / single, 2), ' / '.join(fmt(p['seconds_median'], 2) for p in pairs)])
    r.table(['mode', 'one pair, messages/hour', 'two pairs together', 'ratio', 'seconds per message of each pair'], rows)
    r.p('A ratio near 2 means the machines and the link had room for the second pair; near 1 means one pair already used what there is (information, not a criterion).')
    return figures, scaling


def cost(r, figures, scaling, args):
    r.h('Messages per hour and cost per 1,000 messages')
    hourly = (args.eur_month_a + args.eur_month_b) / HOURS_PER_MONTH
    if not figures:
        r.p('No benchmark figures.')
        return
    if not (args.eur_month_a and args.eur_month_b):
        r.p('Prices were not given (--eur-month-a, --eur-month-b): the machine part of the cost is shown as 0.')
        r.p()
    rows = []
    for mode, f in figures.items():
        for pairs, factor in ((1, 1.0), (2, scaling.get(mode))):
            if factor is None:
                continue
            per_hour = factor * 3600 / f['seconds']
            machine = 1000 * hourly / per_hour
            traffic = (f['gb_a'] * args.eur_per_tb_a + f['gb_b'] * args.eur_per_tb_b)        # GB x EUR/TB = EUR per 1,000 messages
            month = per_hour * HOURS_PER_MONTH
            rows.append([mode, pairs, fmt(per_hour, 0), fmt(month / 1000, 0), fmt(machine, 3), fmt(traffic, 3), fmt(machine + traffic, 3),
                         fmt(month * f['gb_a'] / 1000, 1), fmt(month * f['gb_b'] / 1000, 1)])
    r.table(['mode', 'pairs', 'messages/hour', 'thousand messages/month at full use', 'machines EUR per 1,000', 'metered traffic EUR per 1,000', 'total EUR per 1,000',
             'TB/month sent by a at full use', 'TB/month sent by b at full use'], rows)
    r.p(f'Arithmetic: messages/hour = 3600 / median seconds per message (x the measured two-pair ratio). Machines: ({args.eur_month_a:.2f} + {args.eur_month_b:.2f}) EUR / {HOURS_PER_MONTH:.0f} h '
        f'= {hourly:.4f} EUR/hour, divided by messages/hour, times 1,000. Metered traffic: GB sent per message x EUR per TB (1,000 messages x GB = TB). '
        'These are the engines alone at full use: the real application adds the Signal server\'s response time and the controllers per message (README, "What this does not tell you"), '
        'and a pair that is idle most of the month costs proportionally more per message. Compare the TB/month columns with each provider\'s allowance or fair-use limit.')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--a', required=True, help="logs directory of machine a (party 0)")
    p.add_argument('--b', required=True, help="logs directory of machine b (party 1)")
    p.add_argument('--eur-month-a', type=float, default=0.0)
    p.add_argument('--eur-month-b', type=float, default=0.0)
    p.add_argument('--eur-per-tb-a', type=float, default=0.0)
    p.add_argument('--eur-per-tb-b', type=float, default=0.0)
    p.add_argument('--out', default='report.md')
    args = p.parse_args()
    dirs = {'a': pathlib.Path(args.a), 'b': pathlib.Path(args.b)}
    r = Report()
    r.lines.append('# Two-machine test report')
    r.p()
    r.p('Machine a ran party 0 and the network tests; machine b ran party 1. Criteria and what they mean: README.md.')
    infos = machines(r, dirs)
    cpu_load(r, dirs)
    rtt(r, dirs['a'])
    throughput(r, dirs['a'])
    volume(r, dirs['a'])
    figures, scaling = benchmark(r, dirs, infos, args)
    cost(r, figures, scaling, args)
    r.h('Verdict')
    for mode in MODES:
        mine = [c for c in r.checks if c[0] in ('both', mode)]
        failed = [c for c in mine if c[2] is False]
        missing = [c for c in mine if c[2] is None]
        if failed:
            verdict = 'NOT good enough: ' + '; '.join(c[1] for c in failed)
        elif missing:
            verdict = 'incomplete (nothing failed, not run: ' + '; '.join(c[1] for c in missing) + ')'
        else:
            verdict = 'good enough: every criterion passed'
        r.p(f'- **{mode}**: {verdict}')
    pathlib.Path(args.out).write_text('\n'.join(r.lines) + '\n')
    print('\n'.join(r.lines[-(len(MODES) + 1):]))
    print(f'report written to {args.out}')


if __name__ == '__main__':
    main()
