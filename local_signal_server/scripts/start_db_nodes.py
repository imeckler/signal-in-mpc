#!/usr/bin/env python3
"""Five REAL database nodes of secret-shared-db on this machine, without Docker.

  start_db_nodes.py DIR [--bin BIN] [--port-base 25400] [--epoch-secs 20] [--max-malicious 1]
                        [--no-wait-epoch] [--pg-bin PGBIN]
      Generates the network config (BIN/pki), starts one private Postgres instance with a
      database per node (data, logs and pid files all under DIR; nothing system-wide), applies
      the nodes' schema (server/init.sql of the database checkout), starts the five BIN/server
      processes, waits until their compute ports answer and, unless --no-wait-epoch, until every
      node has applied its first epoch. Prints `network <path of the network config>` last.
      Everything is stopped again if any step fails.
  start_db_nodes.py DIR --wait-epoch
      Returns once rows dealt before the call are readable: when four of the five nodes have
      applied an epoch that could include them (see `wait_epoch`). Prints the seconds waited.
  start_db_nodes.py DIR --stop-node J      stop one node (its database stays)
  start_db_nodes.py DIR --start-node J     start it again and wait for its compute port
  stop_db_nodes.py DIR                     stop the nodes and Postgres

Ports (BASE = --port-base): Postgres BASE; node i: peers BASE+10+i, sync BASE+20+i, relay
BASE+30+i, compute BASE+40+i. A port in use is an error before anything is started.

BIN defaults to .deps/ssdb-agent-target/debug of this repository; it must hold `pki` and `server`
built from one revision of the database checkout (and `handoff_client` of the same revision is
what talks to the nodes).

--max-malicious is the network's max_malicious_parties: an epoch needs threshold + that many
signatures. The generator's own default (2) needs all five nodes at every epoch; 1 (the default
here) lets epochs go on with one node down.

TEST SET-UP: Postgres trusts every local connection and the keys are generated on the spot.
"""
import argparse, json, os, re, shutil, signal, socket, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]            # tls-mpc/
DEFAULT_BIN = ROOT / '.deps/ssdb-agent-target/debug'
INIT_SQL = ROOT / '.deps/secret-shared-db-handoff/server/init.sql'
N = 5
APPLIED = re.compile(r'Successfully updated database secrets for epoch (\d+)')


def state_path(directory):
    return Path(directory) / 'nodes.json'


def load(directory):
    return json.loads(state_path(directory).read_text())


def save(directory, state):
    state_path(directory).write_text(json.dumps(state, indent=2) + '\n')


def ports(base):
    return [base] + [base + block + i for block in (10, 20, 30, 40) for i in range(N)]


def port_free(port):
    with socket.socket() as s:
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            s.bind(('0.0.0.0', port))
            return True
        except OSError:
            return False


def accepts(port):
    try:
        socket.create_connection(('127.0.0.1', port), timeout=1).close()
        return True
    except OSError:
        return False


def alive(pid, word):
    """Is `pid` running and still the process we started (its command line contains `word`)?"""
    if not pid:
        return False
    out = subprocess.run(['ps', '-p', str(pid), '-o', 'command='], capture_output=True, text=True).stdout
    return word in out


def pg(tool, pg_bin):
    path = shutil.which(tool, path=pg_bin) if pg_bin else shutil.which(tool)
    if not path:
        raise RuntimeError(f'{tool} not found (Postgres binaries must be on PATH, or give --pg-bin)')
    return path


def quiet(command, log):
    with open(log, 'a') as f:
        f.write('+ ' + ' '.join(map(str, command)) + '\n')
        f.flush()
        code = subprocess.run([str(c) for c in command], stdout=f, stderr=subprocess.STDOUT).returncode
    if code != 0:
        raise RuntimeError(f'{Path(str(command[0])).name} failed with status {code}; see {log}')


def start_node(directory, state, j):
    directory = Path(directory)
    log = open(directory / 'logs' / f'node-{j}.log', 'a')
    env = dict(os.environ, RUST_LOG='info,sqlx=warn', RAYON_NUM_THREADS='2')
    node = subprocess.Popen([str(Path(state['bin']) / 'server'), '--config-dir', str(directory / 'config/share-dbs' / str(j))],
                            stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True)
    state['pids'][j] = node.pid
    save(directory, state)


def wait_compute(directory, state, nodes, seconds=60):
    deadline = time.time() + seconds
    while True:
        dead = [j for j in nodes if not alive(state['pids'][j], '/server')]
        if dead:
            raise RuntimeError(f'node(s) {dead} exited; see {Path(directory) / "logs"}')
        if all(accepts(state['base'] + 40 + j) for j in nodes):
            return
        if time.time() > deadline:
            raise RuntimeError(f'the compute ports of nodes {nodes} did not open within {seconds} s')
        time.sleep(0.5)


def applied_epochs(directory, j):
    """The epochs node j has applied, from its log."""
    try:
        text = (Path(directory) / 'logs' / f'node-{j}.log').read_text(errors='replace')
    except OSError:
        return []
    return [int(e) for e in APPLIED.findall(text)]


def wait_epoch(directory, since=None, need=N - 1, seconds=None):
    """Wait until rows dealt up to `since` (default: now) are readable.

    A row dealt during epoch e (e = time // epoch length) is proposed in epoch e + 2 and applied at
    that epoch's deadline, half an epoch after its start; an epoch that fails (a node down that
    was needed, or the leader) leaves it to the next. So: wait until `need` nodes have logged that
    they applied an epoch >= e + 2. Returns the seconds waited."""
    state = load(directory)
    length = state['epoch_secs']
    since = time.time() if since is None else since
    target = int(since // length) + 2
    started = time.time()
    seconds = seconds or 8 * length + 30
    while True:
        done = [j for j in range(N) if any(e >= target for e in applied_epochs(directory, j))]
        if len(done) >= need:
            time.sleep(0.3)   # the log line is written just after the database update
            return time.time() - started
        if time.time() - started > seconds:
            raise RuntimeError(f'only nodes {done} applied epoch {target} or later within {seconds} s')
        time.sleep(0.5)


def stop_node(directory, state, j):
    pid = state['pids'][j]
    if alive(pid, '/server'):
        os.kill(pid, signal.SIGTERM)
        for _ in range(20):
            if not alive(pid, '/server'):
                break
            time.sleep(0.1)
        else:
            os.kill(pid, signal.SIGKILL)
    state['pids'][j] = None
    save(directory, state)


def stop(directory):
    """Stop the nodes and the Postgres instance recorded in DIR. Safe to call repeatedly."""
    directory = Path(directory)
    if not state_path(directory).exists():
        return
    state = load(directory)
    for j in range(N):
        stop_node(directory, state, j)
    data = directory / 'pg'
    if (data / 'postmaster.pid').exists():
        subprocess.run([pg('pg_ctl', state.get('pg_bin')), '-D', str(data), '-m', 'fast', '-w', 'stop'],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def restart(directory):
    """Start again the Postgres instance and the five nodes of a cluster that `stop` stopped, with
    their data (real_signal/run_real_test.py --resume). Returns the cluster's state."""
    directory = Path(directory).resolve()
    state = load(directory)
    if any(alive(pid, '/server') for pid in state['pids']):
        raise RuntimeError(f'{directory}: nodes are running')
    taken = [p for p in ports(state['base']) if not port_free(p)]
    if taken:
        raise RuntimeError(f'port(s) {taken} are in use')
    setup_log = directory / 'logs' / 'setup.log'
    options = f"-p {state['base']} -c listen_addresses=127.0.0.1 -c unix_socket_directories='' -c max_connections=120"
    quiet([pg('pg_ctl', state.get('pg_bin')), '-D', directory / 'pg', '-l', directory / 'logs' / 'postgres.log', '-o', options, '-w', 'start'], setup_log)
    try:
        for j in range(N):
            start_node(directory, state, j)
        wait_compute(directory, state, list(range(N)))
    except BaseException:
        stop(directory)
        raise
    return state


def start(directory, binaries, base, epoch_secs, max_malicious, wait_first_epoch, pg_bin):
    directory = Path(directory).resolve()
    if state_path(directory).exists():
        raise RuntimeError(f'{directory} already holds a cluster; run stop_db_nodes.py and remove it first')
    for tool in ('pki', 'server'):
        if not (Path(binaries) / tool).exists():
            raise RuntimeError(f'{Path(binaries) / tool} does not exist (build the database checkout, or give --bin)')
    taken = [p for p in ports(base) if not port_free(p)]
    if taken:
        raise RuntimeError(f'port(s) {taken} are in use; choose another --port-base')
    (directory / 'logs').mkdir(parents=True, exist_ok=True)
    setup_log = directory / 'logs' / 'setup.log'
    state = dict(base=base, epoch_secs=epoch_secs, max_malicious=max_malicious, bin=str(binaries), pg_bin=pg_bin, pids=[None] * N,
                 network=str(directory / 'config/relay/network-config.json'))
    save(directory, state)
    started = time.time()
    try:
        url = f'postgresql://dbuser@127.0.0.1:{base}/node{{node}}'
        quiet([Path(binaries) / 'pki', '-n', N, '-o', directory / 'config', '-d', url, '-t', 3, '-l', '--max-malicious', max_malicious,
               '--epoch-secs', epoch_secs, '--port-base', base], setup_log)
        quiet([pg('initdb', pg_bin), '-D', directory / 'pg', '-U', 'dbuser', '--auth=trust', '-E', 'UTF8'], setup_log)
        # TCP on localhost only; no unix socket (its path would have to be short).
        options = f"-p {base} -c listen_addresses=127.0.0.1 -c unix_socket_directories='' -c max_connections=120"
        quiet([pg('pg_ctl', pg_bin), '-D', directory / 'pg', '-l', directory / 'logs' / 'postgres.log', '-o', options, '-w', 'start'], setup_log)
        for j in range(N):
            quiet([pg('createdb', pg_bin), '-h', '127.0.0.1', '-p', base, '-U', 'dbuser', f'node{j}'], setup_log)
            if INIT_SQL.exists():
                quiet([pg('psql', pg_bin), '-h', '127.0.0.1', '-p', base, '-U', 'dbuser', '-d', f'node{j}', '-v', 'ON_ERROR_STOP=1',
                       '-q', '-f', INIT_SQL], setup_log)
        for j in range(N):
            start_node(directory, state, j)
        wait_compute(directory, state, list(range(N)))
        print(f'compute ports open after {time.time() - started:.1f} s', flush=True)
        if wait_first_epoch:
            # No rows yet: any applied epoch shows that the five nodes reach consensus.
            deadline = time.time() + 4 * epoch_secs + 60
            while not all(applied_epochs(directory, j) for j in range(N)):
                if time.time() > deadline:
                    raise RuntimeError('the nodes did not apply an epoch; see ' + str(directory / 'logs'))
                time.sleep(0.5)
            print(f'first epoch applied by all nodes after {time.time() - started:.1f} s', flush=True)
    except BaseException:
        stop(directory)
        raise
    print('network', state['network'], flush=True)
    return state


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('directory')
    p.add_argument('--bin', default=str(DEFAULT_BIN))
    p.add_argument('--port-base', type=int, default=25400)
    p.add_argument('--epoch-secs', type=int, default=20)
    p.add_argument('--max-malicious', type=int, default=1)
    p.add_argument('--no-wait-epoch', action='store_true')
    p.add_argument('--pg-bin', default=None)
    p.add_argument('--wait-epoch', action='store_true')
    p.add_argument('--stop-node', type=int, default=None)
    p.add_argument('--start-node', type=int, default=None)
    a = p.parse_args()
    try:
        if a.wait_epoch:
            print(f'waited {wait_epoch(a.directory):.1f} s')
        elif a.stop_node is not None:
            stop_node(a.directory, load(a.directory), a.stop_node)
        elif a.start_node is not None:
            state = load(a.directory)
            if alive(state['pids'][a.start_node], '/server'):
                raise RuntimeError(f'node {a.start_node} is running')
            start_node(a.directory, state, a.start_node)
            wait_compute(a.directory, state, [a.start_node])
        else:
            start(a.directory, a.bin, a.port_base, a.epoch_secs, a.max_malicious, not a.no_wait_epoch, a.pg_bin)
    except RuntimeError as e:
        print(f'start_db_nodes: {e}', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
