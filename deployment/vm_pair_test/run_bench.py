#!/usr/bin/env python3
"""One party's side of the two-machine benchmark (README.md, part 3).

Run the same command on both machines, party 0 first (it listens), party 1 within a minute:

    python3 run_bench.py --party 0 --peer 10.77.0.2 --listen 10.77.0.1
    python3 run_bench.py --party 1 --peer 10.77.0.1

For each security mode it runs, in this order, each as its own two-process session:
    bench     pair-bench: one contact's first-send preparation, then ITERATIONS messages
    prepare   rounds fixture `prepare 1`: a contact's first-send preparation, both program families
    receive   rounds fixture `receive 1`: the field programs of a first message received
Both sides must pass the same --modes, --steps, --iterations, --pairs and --port-base.

Ports (all TCP, party 0 listens, party 1 dials; party 1 also binds PORT+11 for itself):
    PORT = port-base + 200*pair + 100*mode + 20*step,  and PORT+10
    so pair 0 uses port-base .. port-base+199 and pair 1 the next 200.

Logs: LOGS/STEP-MODE-pPARTY-pairN.log, and LOGS/summary-pPARTY.json. Nothing here needs root.
"""
import argparse, json, os, pathlib, re, resource, statistics, subprocess, sys, threading, time

MODES = {'malicious': (0, ''), 'semi-honest': (1, '-sh')}
STEPS = {'bench': 0, 'prepare': 1, 'receive': 2}


def numbers(line):
    out = {}
    for key, value in re.findall(r'(\w+)=(\S+)', line):
        try:
            out[key] = float(value)
        except ValueError:
            pass                      # an address, a mode name, a list
    return out


def summarise(log):
    """What a finished step's log says, as numbers."""
    text = log.read_text(errors='replace')
    out = {'passed': 'pair bench passed' in text or 'rounds fixture passed' in text}
    iters = [numbers(l) for l in text.split('\n') if l.startswith('ITER ')]
    if iters:
        def col(name):
            return [r[name] for r in iters if name in r]
        seconds = col('seconds')
        steady = seconds[len(seconds) // 5:] or seconds           # drop the first fifth: stocks filling
        out['iterations'] = len(iters)
        out['seconds_median'] = statistics.median(steady)
        out['seconds_mean_all'] = sum(seconds) / len(seconds)
        out['seconds_p95'] = sorted(steady)[max(0, int(0.95 * len(steady)) - 1)]
        # Drift: the second fifth against the last fifth (the first fifth runs on the stocks' initial reserve).
        fifth = max(1, len(seconds) // 5)
        out['seconds_early_median'] = statistics.median(seconds[fifth:2 * fifth] or seconds)
        out['seconds_late_median'] = statistics.median(seconds[-fifth:])
        out['seconds_total'] = sum(seconds)
        out['and_gates_per_iteration'] = statistics.median(col('and_gates'))
        out['field_products_per_iteration'] = statistics.median(col('field_products'))
        out['field_rounds_per_iteration'] = statistics.median(col('field_mul_rounds')) + statistics.median(col('field_openings'))
        out['boolean_sent_bytes_per_iteration'] = sum(col('boolean_sent_bytes')) / len(iters)
        out['field_sent_bytes_per_iteration'] = sum(col('field_sent_bytes')) / len(iters)
    stages = {}
    for l in text.split('\n'):
        if l.startswith('BENCH ') or l.startswith('RESULT ') or l.startswith('CIRCUIT '):
            head = re.split(r'\s+\w+=', l, maxsplit=1)[0]
            stages[head] = numbers(l)
    out['stages'] = stages
    return out


def run_pair(args, pair, results):
    root = pathlib.Path(args.root).resolve()
    bins = pathlib.Path(args.bin_dir).resolve() if args.bin_dir else root / 'bin'
    circuits = pathlib.Path(args.circuits).resolve() if args.circuits else root / 'circuits' / 'circuits.list'
    work = pathlib.Path(args.work).resolve()
    logs = pathlib.Path(args.logs).resolve()
    env = dict(os.environ, TLS_WORKER_PEER=args.peer)
    if args.listen:
        env['TLS_WORKER_LISTEN'] = args.listen
    if args.lib_dir:
        env['LD_LIBRARY_PATH'] = args.lib_dir
        env['DYLD_LIBRARY_PATH'] = args.lib_dir
    for name, value in (('PAIR_BENCH_TRIPLE_STOCK', args.triple_stock), ('PAIR_BENCH_FIELD_STOCK', args.field_stock)):
        if value:
            env[name] = value
    if args.field_stock:
        env['ROUNDS_FIXTURE_STOCK'] = args.field_stock
    for mode in args.modes.split(','):
        index, suffix = MODES[mode]
        for step in args.steps.split(','):
            port = args.port_base + 200 * pair + 100 * index + 20 * STEPS[step]
            if step == 'bench':
                binary = bins / args.bin_pattern.format(name='pair-bench' + suffix)
                command = [str(binary), str(args.party + 1), str(port), args.peer, args.listen or '-', str(circuits), str(args.iterations)]
            else:
                binary = bins / args.bin_pattern.format(name='rounds' + suffix)
                command = [str(binary), str(args.party + 1), str(port), step, '1']
            log = logs / f'{step}-{mode}-p{args.party}-pair{pair}.log'
            started = time.time()
            with open(log, 'w') as out:
                out.write(f'# {" ".join(command)}\n# started {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(started))} port {port}\n')
                out.flush()
                child = subprocess.Popen(command, cwd=work, env=env, stdout=out, stderr=subprocess.STDOUT)
                try:
                    code = child.wait(timeout=args.step_timeout)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.wait()
                    code = -9
            row = summarise(log)
            row.update(step=step, mode=mode, pair=pair, port=port, exit_code=code, wall_seconds=time.time() - started)
            results.append(row)
            verdict = 'ok' if code == 0 and row['passed'] else 'FAILED'
            extra = ''
            if 'seconds_median' in row:
                extra = (f"  {row['seconds_median']:.3f} s/message (median), {row['and_gates_per_iteration'] / 1e6:.2f}M AND, "
                         f"{row['field_products_per_iteration']:.0f} products, sent {(row['boolean_sent_bytes_per_iteration'] + row['field_sent_bytes_per_iteration']) / 1e9:.3f} GB/message")
            print(f'[pair {pair}] {step} {mode}: {verdict} in {row["wall_seconds"]:.1f} s{extra}', flush=True)
            if verdict != 'ok':
                print(f'[pair {pair}] stopping; see {log}', flush=True)
                return
            time.sleep(args.pause)      # let the peer finish closing before the next session


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--party', type=int, choices=(0, 1), required=True)
    p.add_argument('--peer', required=True, help="the other machine's address (its WireGuard address)")
    p.add_argument('--listen', default='', help="party 0: address the Boolean listener binds (this machine's WireGuard address); default all")
    p.add_argument('--port-base', type=int, default=26000)
    p.add_argument('--modes', default='malicious,semi-honest')
    p.add_argument('--steps', default='bench,prepare,receive')
    p.add_argument('--iterations', type=int, default=50)
    p.add_argument('--pairs', type=int, default=1, help='worker pairs run at the same time (1 or 2)')
    p.add_argument('--root', default=str(pathlib.Path(__file__).resolve().parent.parent), help='bundle root (holds bin/ and circuits/)')
    p.add_argument('--bin-dir', default='')
    p.add_argument('--bin-pattern', default='{name}')
    p.add_argument('--circuits', default='')
    p.add_argument('--work', default='work', help='working directory holding Player-Data/ (bench_certs.sh)')
    p.add_argument('--logs', default='logs')
    p.add_argument('--lib-dir', default='', help="directory of the field engine's shared library, if not found by rpath")
    p.add_argument('--triple-stock', default='', help='FACTORIES,BATCH,RESERVE for the Boolean engine (default 2,524288,4194304; 0 = none)')
    p.add_argument('--field-stock', default='', help='RESERVE,LINES for the field engine (default 24000,2; 0 = none)')
    p.add_argument('--step-timeout', type=float, default=6 * 3600)
    p.add_argument('--pause', type=float, default=3.0)
    args = p.parse_args()
    if not 1024 <= args.port_base <= 64000 or args.pairs not in (1, 2):
        p.error('port base or pair count')
    if any(m not in MODES for m in args.modes.split(',')) or any(s not in STEPS for s in args.steps.split(',')):
        p.error('unknown mode or step')
    for directory in (args.work, args.logs):
        pathlib.Path(directory).mkdir(parents=True, exist_ok=True)
    key = pathlib.Path(args.work) / 'Player-Data' / f'P{args.party}.key'
    if not key.exists():
        sys.exit(f'{key} is missing: run bench_certs.sh init {args.party} {args.work} and exchange certificates first')
    results, threads = [], []
    for pair in range(args.pairs):
        t = threading.Thread(target=run_pair, args=(args, pair, results))
        t.start()
        threads.append(t)
    for t in threads:
        t.join()
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    peak = usage.ru_maxrss / (2 ** 30 if sys.platform == 'darwin' else 2 ** 20)
    summary = dict(party=args.party, peer=args.peer, pairs=args.pairs, iterations=args.iterations, largest_child_peak_rss_gb=peak, results=results)
    out = pathlib.Path(args.logs) / f'summary-p{args.party}.json'
    out.write_text(json.dumps(summary, indent=1) + '\n')
    print(f'largest single process: {peak:.2f} GB resident; summary in {out}')
    expected = args.pairs * len(args.modes.split(',')) * len(args.steps.split(','))
    sys.exit(0 if len(results) == expected and all(r['exit_code'] == 0 and r['passed'] for r in results) else 1)


if __name__ == '__main__':
    main()
