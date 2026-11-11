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
"""
import fcntl, json, os, signal, subprocess, sys, time

REGISTRY = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), '.deps', 'guarded-reservations.json')
BIG_GB = 12.0


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
    limit_gb, limit_seconds, command = float(sys.argv[1]), float(sys.argv[2]), sys.argv[3:]
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
    print(f'guarded: peak {peak:.2f} GB, {time.monotonic() - started:.1f} s' + (f', KILLED ({killed})' if killed else ''), file=sys.stderr)
    sys.exit(99 if killed else child.returncode)


if __name__ == '__main__':
    main()
