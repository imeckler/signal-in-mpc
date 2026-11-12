#!/usr/bin/env python3
"""Produce every circuit a deployment can need, before it starts, and pin them in a manifest.

    produce_circuits.py DEPLOYMENT.json OUT_DIRECTORY [--max-gb 16] [--list]

DEPLOYMENT.json is {"settings": {KEY: VALUE, ...}}: the settings of the Lean executable
`circuit_inventory` (handshake_backend/EmpHybridWork/CircuitInventory.lean lists them;
CIRCUIT_SHAPES.md explains them). A value may be a number, a string or a list (joined by commas).

The names come from Lean, not from a list kept here:
  1. `circuit_inventory KEY=VALUE ...` prints every kernel whose parameters follow from the settings;
  2. the request frames' kernels take frame offsets, which depend on the size of the envelope a
     seal kernel opens: once those kernels exist, their layouts give the envelope sizes and
     `public_service_controller request-shape ...` (the controller's own frame builder) names
     the request kernels.

Kernels are produced STRICTLY ONE AT A TIME (several at once exhausted this machine's memory), each
by `circuit_cache.py kernel ...` under the memory cap; a kernel already in the cache is not produced
again, so an interrupted run resumes where it stopped. Written to OUT_DIRECTORY:

  manifest.txt    what a worker in strict mode reads (CIRCUIT_MANIFEST=OUT_DIRECTORY/manifest.txt): a
                  first line, then `SHA256 LAYOUT_SHA256 NAME [PARAMETERS]` per kernel, sorted. Both
                  parties compare the hash of this file before the first kernel is used.
  manifest.json   the same with the deployment, the emitter's hash, each kernel's AND-gate count,
                  gate count, input and output bits, and the totals (time, peak memory).
  kernel-*.flat, kernel-*.layout   the gate lists and layouts (hard links into the cache).

The manifest is tied to the emitter binary that produced it: after any change to the Lean kernels,
run this again (only what changed in the cache key is produced: everything, as the key is the binary).
"""
import argparse, hashlib, itertools, json, os, pathlib, signal, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parents[1]
CACHE = ROOT / 'handshake_backend/EmpHybridWork/circuit_cache.py'
BIN = ROOT / '.lake/build/bin'
sys.path.insert(0, str(ROOT / 'scripts'))
from guarded import tree_rss_gb


def lean(binary, *args, profile=None):
    # `request-shape` builds frames as the sessions will: with the deployment's SIGNAL_CLIENT_PROFILE.
    env = dict(os.environ, SIGNAL_CLIENT_PROFILE=profile) if profile else None
    r = subprocess.run([str(BIN / binary), *map(str, args)], capture_output=True, text=True, cwd=ROOT, env=env)
    if r.returncode:
        raise SystemExit(f'{binary} {" ".join(map(str, args))}: {r.stderr.strip()}')
    return [line.split()[1:] for line in r.stdout.splitlines() if line.startswith('kernel ')]


def produce(name, cap_gb):
    """One kernel through the cache script, alone, under the cap. Returns (flat path, record, seconds, peak GB)."""
    started, peak = time.monotonic(), 0.0
    child = subprocess.Popen([sys.executable, str(CACHE), 'kernel', *name], cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, start_new_session=True, env=dict(os.environ, CIRCUIT_CACHE_MAX_GB=str(cap_gb), CIRCUIT_CACHE_LOG=''))
    while child.poll() is None:
        now = tree_rss_gb(child.pid)
        peak = max(peak, now)
        if now > cap_gb:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
            raise SystemExit(f'kernel {" ".join(name)}: memory {now:.1f} GB is over the cap of {cap_gb} GB')
        time.sleep(0.25)
    out, err = child.communicate()
    if child.returncode:
        raise SystemExit(f'kernel {" ".join(name)}: not produced ({err.strip()[-300:]})')
    path = pathlib.Path(out.split()[0])
    return path, json.loads(path.with_suffix('.json').read_text()), time.monotonic() - started, peak


def output_bytes(flat, field):
    for row in flat.with_suffix('.layout').read_text().splitlines():
        parts = row.split()
        if parts[:2] == ['O', field]:
            return int(parts[2]) // 8
    raise SystemExit(f'{flat.name}: no output {field}')


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('deployment')
    p.add_argument('out')
    p.add_argument('--max-gb', type=float, default=16.0, help='memory cap for producing one kernel')
    p.add_argument('--list', action='store_true', help='print the names known before any kernel exists and stop')
    a = p.parse_args()
    deployment = json.loads(pathlib.Path(a.deployment).read_text())
    settings = {key: ','.join(map(str, value)) if isinstance(value, list) else str(value) for key, value in deployment['settings'].items()}
    built = subprocess.run(['lake', 'build', 'flat_kernel_emitter', 'bundle_slot_emitter', 'circuit_inventory', 'public_service_controller'],
                           cwd=ROOT, capture_output=True, text=True)
    if built.returncode:
        raise SystemExit('lake build failed: ' + (built.stdout + built.stderr)[-600:])
    names = lean('circuit_inventory', *[f'{key}={value}' for key, value in settings.items()])
    if a.list:
        for name in names:
            print('kernel', *name)
        return
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    started, produced = time.monotonic(), {}
    emitter = hashlib.sha256((BIN / 'flat_kernel_emitter').read_bytes()).hexdigest()
    cache = ROOT / '.deps/emp-hybrid-word-v1/cache' / ('lean-' + emitter[:16])
    # What producing each kernel cost, kept across interrupted runs (a kernel found in the cache costs nothing now).
    log_path = out / 'production.json'
    log = json.loads(log_path.read_text()) if log_path.exists() else {}
    if log.get('emitter_sha256') != emitter:
        log = dict(emitter_sha256=emitter, kernels={})

    def ensure(name):
        key = ' '.join(name)
        if key in produced:
            return produced[key]
        fresh = not (cache / ('kernel-' + '-'.join(name) + '.json')).exists()
        flat, record, seconds, peak = produce(name, a.max_gb)
        if fresh:
            log['kernels'][key] = dict(seconds=round(seconds, 2), peak_gb=round(peak, 2))
            log_path.write_text(json.dumps(log, indent=1) + '\n')
        for source in (flat, flat.with_suffix('.layout')):
            target = out / source.name
            if target.exists() or target.is_symlink():
                target.unlink()
            try:
                os.link(source, target)
            except OSError:
                target.symlink_to(source)
        produced[key] = dict(name=name[0], parameters=name[1:], sha256=record['sha256'], layout_sha256=record['layout_sha256'],
                             and_gates=record.get('and_gates'), gates=record.get('gates'), input_bits=record['input_bits'],
                             output_bits=record['output_bits'], bytes=flat.stat().st_size, flat=flat,
                             **({'production': log['kernels'][key]} if key in log['kernels'] else {}))
        print(f'[{len(produced)}] {key}: {record.get("and_gates")} AND, {seconds:.1f} s, {peak:.1f} GB' + ('' if fresh else ' (cached)'), flush=True)
        return produced[key]

    for name in names:
        ensure(name)
    # The request frames, from the envelope sizes the seal kernels declare (see the top of this file).
    certificate = settings.get('certificate', '244')
    profile = settings.get('profile', 'legacy')
    rows = {}   # (class, widths) -> envelope bytes of [an established device, a pending one without / with a one-time prekey]
    for name in names:
        if name[0] in ('signal-seal-built', 'signal-seal-official'):
            rows.setdefault((int(name[2]), tuple(name[3:])), {})[0] = output_bytes(ensure(name)['flat'], 'envelope')
        if name[0] == 'bundle-seal':
            # 80c padded bytes, or 80c - 1 under the libsignal profile.
            rows.setdefault(((int(name[3]) + 1) // 80, tuple(name[4:])), {})[1 + int(name[2])] = output_bytes(ensure(name)['flat'], 'envelope')
    requests = []
    for sizes in rows.values():
        requests += lean('public_service_controller', 'request-shape', 'send', certificate, sizes[0], profile=profile)
    if any(len(sizes) > 1 for sizes in rows.values()):
        requests += lean('public_service_controller', 'request-shape', 'fetch', profile=profile)
        # One message per device; the devices of a contact may be at different counters (a new device
        # beside an old one), so every combination of the covered rows of one size class.
        # `device_lists: pending` (setting): only devices that have not answered (kinds 1 and 2), the
        # only entries a device list holds while replies are not processed (MULTI_DEVICE.md section 4);
        # 2^n instead of 3^n combinations for n devices. Default `mixed`: established ones too.
        pending_only = settings.get('device_lists', 'mixed') == 'pending'
        for size_class in sorted({key[0] for key in rows}):
            choices = sorted({size for key, sizes in rows.items() if key[0] == size_class
                              for kind, size in sizes.items() if not (pending_only and kind == 0)})
            for count in range(1, int(settings.get('devices', '1')) + 1):
                for envelopes in itertools.product(choices, repeat=count):
                    requests += lean('public_service_controller', 'request-shape', 'devices', *envelopes, profile=profile)
    for name in requests:
        ensure(name)
    kernels = [dict((k, v) for k, v in row.items() if k != 'flat') for _, row in sorted(produced.items())]
    text = 'EMP_HYBRID_CIRCUIT_MANIFEST_V1\n' + ''.join(
        f'{row["sha256"]} {row["layout_sha256"]} {" ".join([row["name"], *row["parameters"]])}\n' for row in kernels)
    (out / 'manifest.txt').write_text(text)
    families = {}
    for row in kernels:
        family = families.setdefault(row['name'], dict(kernels=0, and_gates=0))
        family['kernels'] += 1
        family['and_gates'] += row['and_gates'] or 0
    summary = dict(kernels=len(kernels), and_gates=sum(row['and_gates'] or 0 for row in kernels), gates=sum(row['gates'] or 0 for row in kernels),
                   bytes=sum(row['bytes'] for row in kernels), this_run_seconds=round(time.monotonic() - started, 1), max_gb=a.max_gb)
    costs = [(row['production']['seconds'], row['production']['peak_gb'], ' '.join([row['name'], *row['parameters']])) for row in kernels if 'production' in row]
    if costs:
        # Totals over the kernels this directory saw produced (all of them after a run on an empty cache).
        summary.update(production_seconds=round(sum(c[0] for c in costs), 1), production_peak_gb=max(c[1] for c in costs),
                       produced_here=len(costs), slowest=dict(kernel=max(costs)[2], seconds=max(costs)[0]))
    (out / 'manifest.json').write_text(json.dumps(dict(format='EMP_HYBRID_CIRCUIT_MANIFEST_V1', manifest_sha256=hashlib.sha256(text.encode()).hexdigest(),
                                                       emitter_sha256=emitter, deployment=deployment, summary=summary, families=families,
                                                       kernels=kernels), indent=1) + '\n')
    print(json.dumps(dict(manifest=str(out / 'manifest.txt'), **summary)))


if __name__ == '__main__':
    main()
