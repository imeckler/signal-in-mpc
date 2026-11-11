#!/usr/bin/env python3
"""Run a command under a memory and time limit: guarded.py MAX_GB MAX_SECONDS COMMAND...

The whole process tree's resident memory is sampled twice a second; the tree is killed when it
exceeds MAX_GB or MAX_SECONDS. Prints the peak and exits with the command's status (or 99 when
killed). For anything that could use a lot of memory: a circuit lowering, an emitter run, a
harness run. (Unbounded jobs exhausted this machine's memory twice.)
"""
import os, signal, subprocess, sys, time


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
    print(f'guarded: peak {peak:.2f} GB, {time.monotonic() - started:.1f} s' + (f', KILLED ({killed})' if killed else ''), file=sys.stderr)
    sys.exit(99 if killed else child.returncode)


if __name__ == '__main__':
    main()
