#!/usr/bin/env python3
"""Run a command under a memory and time limit: guarded.py MAX_GB MAX_SECONDS COMMAND...

The whole process tree's resident memory is sampled twice a second; the tree is killed when it
exceeds MAX_GB or MAX_SECONDS. Prints the peak and exits with the command's status (or 99 when
killed). For anything that could use a lot of memory: a circuit lowering, an emitter run, a
harness run. (Unbounded jobs exhausted this machine's memory twice.)

Several people run guarded jobs on this machine at once. A job whose limit is above 12 GB first
reserves its limit against a machine-wide budget (GUARDED_TOTAL_GB, default 48) and waits, without
its clock running, until the reservations of the big jobs already running leave room. So the big
jobs together can never be allowed more than the budget, however many are started.

guarded.py --heavy MAX_GB MAX_SECONDS COMMAND... (or scripts/heavy.sh MAX_GB MAX_SECONDS COMMAND...):
the same, but first takes the machine-wide heavy-job lock (REORGANIZATION_PLAN.md section 1, rule
3). The lock is only for jobs that genuinely conflict with each other:
  - harness runs (they share the local server, its ports, the database nodes, local_signal_server/state);
  - builds that replace binaries a harness run uses: `lake build` of an executable or of the
    TlsMpc library, build_hybrid_v3.py, cargo builds of node_daemon or the provision tool;
  - circuit lowering and manifest production.
Light jobs never take it and run any time as plain guarded.py with a cap of at most 12 GB:
`lake env lean ONE_FILE` (reads .olean files, writes nothing shared), the lints, read-only
scripts, `cargo check` in a separate target directory, unit-level kernel checks that start no
server. Declare a realistic cap (harness runs peak around 10 GB: 16-20, not 40) and keep each
--heavy invocation short (one harness stage set, under about 8 minutes) so the lock turns over.
A second --heavy job waits, without its clock running, until the first ends; it says who holds
the lock and for how long when it starts waiting and then every minute. The lock is an flock on
.deps/heavy.lock (GUARDED_HEAVY_LOCK overrides the path), released when the holding guarded.py
exits for any reason, a crash or a kill included (a child of a killed holder may outlive it).
Without --heavy nothing changes: such a job neither takes nor waits for the lock.
"""
import fcntl, json, os, signal, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, '.deps', 'guarded-reservations.json')
HEAVY_LOCK = os.environ.get('GUARDED_HEAVY_LOCK') or os.path.join(ROOT, '.deps', 'heavy.lock')
BIG_GB = 12.0


def take_heavy_lock(command):
    """Wait until no other heavy job holds the lock, then hold it (the returned file) until exit."""
    os.makedirs(os.path.dirname(HEAVY_LOCK), exist_ok=True)
    lock = open(HEAVY_LOCK, 'a+')
    said = None   # when the holder was last named (every minute while waiting)
    while True:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            if said is None or time.monotonic() - said >= 60:
                try:
                    with open(HEAVY_LOCK) as f:
                        holder = json.loads(f.read() or '{}')
                except (OSError, ValueError):
                    holder = {}
                held = f", for {(time.time() - holder['at']) / 60:.0f} min" if isinstance(holder.get('at'), (int, float)) else ''
                print(f"guarded: waiting for the heavy-job lock (held by pid {holder.get('pid', '?')}{held}: "
                      f"{' '.join(holder.get('command', []))[:160]})", file=sys.stderr, flush=True)
                said = time.monotonic()
            time.sleep(2)
    lock.seek(0)
    lock.truncate()
    lock.write(json.dumps(dict(pid=os.getpid(), command=command, since=time.strftime('%Y-%m-%d %H:%M:%S'), at=time.time())))
    lock.flush()
    return lock


def reserve(limit_gb):
    """Wait until this job's limit fits in the budget, then record it. Returns once reserved."""
    if limit_gb <= BIG_GB:
        return False
    budget = float(os.environ.get('GUARDED_TOTAL_GB', '48'))
    os.makedirs(os.path.dirname(REGISTRY), exist_ok=True)
    announced = False
    while True:
        with open(REGISTRY, 'a+') as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            f.seek(0)
            try:
                rows = json.loads(f.read() or '[]')
            except ValueError:
                rows = []
            alive = []
            for pid, gb in rows:
                try:
                    os.kill(pid, 0)
                    alive.append([pid, gb])
                except OSError:
                    pass
            if sum(gb for _, gb in alive) + limit_gb <= budget or not alive:
                alive.append([os.getpid(), limit_gb])
                f.seek(0); f.truncate(); f.write(json.dumps(alive))
                return True
            f.seek(0); f.truncate(); f.write(json.dumps(alive))
        if not announced:
            print(f'guarded: waiting for room in the {budget:g} GB budget', file=sys.stderr)
            announced = True
        time.sleep(2)


def release():
    try:
        with open(REGISTRY, 'a+') as f:
            fcntl.flock(f, fcntl.LOCK_EX)
            f.seek(0)
            rows = [row for row in json.loads(f.read() or '[]') if row[0] != os.getpid()]
            f.seek(0); f.truncate(); f.write(json.dumps(rows))
    except (OSError, ValueError):
        pass


def tree_rss_gb(root):
    rows = subprocess.run(['ps', '-axo', 'pid=,ppid=,rss='], capture_output=True, text=True).stdout.split('\n')
    table = [tuple(int(x) for x in row.split()) for row in rows if len(row.split()) == 3]
    children = {}
    for pid, ppid, _ in table:
        children.setdefault(ppid, []).append(pid)
    rss = {pid: kb for pid, _, kb in table}
    seen, stack, total = set(), [root], 0
    while stack:
        pid = stack.pop()
        if pid in seen:
            continue
        seen.add(pid)
        total += rss.get(pid, 0)
        stack += children.get(pid, [])
    return total / 1048576


def main():
    arguments = sys.argv[1:]
    heavy = arguments[:1] == ['--heavy']
    if heavy:
        arguments = arguments[1:]
    limit_gb, limit_seconds, command = float(arguments[0]), float(arguments[1]), arguments[2:]
    lock = take_heavy_lock(command) if heavy else None
    reserved = reserve(limit_gb)
    child = subprocess.Popen(command, start_new_session=True)
    started, peak, killed = time.monotonic(), 0.0, None
    while child.poll() is None:
        now = tree_rss_gb(child.pid)
        peak = max(peak, now)
        if now > limit_gb:
            killed = f'memory {now:.1f} GB > {limit_gb} GB'
        elif time.monotonic() - started > limit_seconds:
            killed = f'time > {limit_seconds} s'
        if killed:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
            break
        time.sleep(0.5)
    if reserved:
        release()
    if lock:
        lock.close()   # releases the heavy-job lock
    print(f'guarded: peak {peak:.2f} GB, {time.monotonic() - started:.1f} s' + (f', KILLED ({killed})' if killed else ''), file=sys.stderr)
    sys.exit(99 if killed else child.returncode)


if __name__ == '__main__':
    main()
