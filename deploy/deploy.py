#!/usr/bin/env python3
"""Deploy the two-party Signal client: two computation nodes, the database nodes, monitoring.

Several operators (the normal case):            One person, every node:
  coordinator  deploy.py init                     deploy.py init
  builder      deploy.py build                    deploy.py build --record (images already built)
  everyone     deploy.py join                     deploy.py up
  everyone     deploy.py collect bundles/
  everyone     (compare the fingerprint by voice)
  everyone     deploy.py start bundles/ --fingerprint F
  MPC ops      deploy.py account install DIR      deploy.py account local-test (local test only)

Then: status, monitor, logs, upgrade, destroy. `deploy.py` alone (or `next`) says what to do next.
Files: deploy/deployment.toml (shared, public) and deploy/operator.toml (yours, private); state in
deploy/.state/NAME/OPERATOR/. Prerequisites: Docker, Python 3.11+, ssh. DEPLOYMENT.md explains.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pushbutton import config as C  # noqa: E402
from pushbutton import flow as F  # noqa: E402
from pushbutton.tools import ToolError  # noqa: E402


def main(argv=None):
    p = argparse.ArgumentParser(prog='deploy.py', description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--operator', help='your private operator file (default deploy/operator.toml)')
    p.add_argument('--deployment', help='the shared deployment file (default: what operator.toml names)')
    p.add_argument('--state', help='state directory (default deploy/.state/NAME/OPERATOR)')
    sub = p.add_subparsers(dest='command')
    sub.add_parser('next', help='what to do next (the default)')
    sub.add_parser('init', help='the coordinator: deployment.toml and operator.toml from the examples')
    b = sub.add_parser('build', help='the builder: images for the target machines, digests into deployment.toml')
    b.add_argument('--platform', default='linux/amd64')
    b.add_argument('--record', action='store_true', help='do not build: record images already built (by tag)')
    b.add_argument('--node-tag')
    b.add_argument('--db-tag')
    b.add_argument('--context', help='build context directory (default .deps/deploy-ctx)')
    b.add_argument('--out', help='also write the image files the operators load (docker save) here')
    b.add_argument('--circuits', help='record this circuit set\'s manifest digest')
    b.add_argument('--word-dir', help='record this word dir\'s digest')
    pl = sub.add_parser('plan', help='what join would create, and the monthly cost where known; creates nothing')
    pl.add_argument('--tofu', action='store_true', help='also run `tofu plan` with your credentials')
    for name, text in (('join', 'make your machines, install, make keys on the nodes, write your public bundles'),
                       ('up', 'one person, every node: join + collect + start')):
        j = sub.add_parser(name, help=text)
        j.add_argument('--images', choices=['prebuilt', 'build-here'], help='override operator.toml [software] images')
        j.add_argument('--i-have-the-go-ahead', action='store_true', help='required with [signal] endpoint = "production" (owner only)')
        if name == 'up':
            j.add_argument('--with-account', action='store_true', help='local-test: also make the test account and start the daemons')
    c = sub.add_parser('collect', help='check the bundles and print the deployment fingerprint')
    c.add_argument('dirs', nargs='+')
    s = sub.add_parser('start', help='after comparing the fingerprint: tunnels, firewall, services')
    s.add_argument('dirs', nargs='+')
    s.add_argument('--fingerprint', required=True)
    s.add_argument('--i-have-the-go-ahead', action='store_true')
    a = sub.add_parser('account', help='the account step')
    a.add_argument('what', choices=['install', 'local-test'])
    a.add_argument('dir', nargs='?')
    sub.add_parser('status', help='your nodes\' state (and a copy of the monitoring page)')
    m = sub.add_parser('monitor', help='open an ssh tunnel to your monitoring page')
    m.add_argument('--seconds', type=int, default=0, help=argparse.SUPPRESS)
    lg = sub.add_parser('logs', help='fetch redacted logs of your nodes')
    lg.add_argument('node', nargs='?')
    lg.add_argument('--lines', type=int, default=400)
    u = sub.add_parser('upgrade', help='install new software from an updated deployment.toml (keys kept)')
    u.add_argument('dirs', nargs='*', help='bundles received so far: shows who is still on the old version')
    u.add_argument('--images', choices=['prebuilt', 'build-here'])
    u.add_argument('--i-have-the-go-ahead', action='store_true')
    d = sub.add_parser('destroy', help='remove your machines (data disks kept unless --delete-data)')
    d.add_argument('--delete-data', action='store_true')
    d.add_argument('--yes-i-typed-it', action='store_true', help=argparse.SUPPRESS)
    t = sub.add_parser('testapp', help='local-test only: a TEST application server on this computer')
    t.add_argument('action', choices=['up', 'start', 'send'])
    t.add_argument('dirs', nargs='*')
    args = p.parse_args(argv)
    command = args.command or 'next'
    handlers = {'next': F.cmd_next, 'init': F.cmd_init, 'build': F.cmd_build, 'plan': F.cmd_plan, 'join': F.cmd_join, 'up': F.cmd_up,
                'collect': F.cmd_collect, 'start': F.cmd_start, 'status': F.cmd_status, 'monitor': F.cmd_monitor, 'logs': F.cmd_logs,
                'upgrade': F.cmd_upgrade, 'destroy': F.cmd_destroy, 'testapp': F.cmd_testapp,
                'account': lambda a: F.cmd_account_install(a) if a.what == 'install' else F.cmd_account_local(a)}
    if command == 'account' and args.what == 'install' and not args.dir:
        p.error('account install needs the account directory')
    try:
        return handlers[command](args)
    except C.ConfigError as e:
        print(f'configuration: {e}', file=sys.stderr)
        return 2
    except (F.Fail, ToolError) as e:
        print(f'stopped: {e}', file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print('\ninterrupted; run the same command again to resume', file=sys.stderr)
        return 130


if __name__ == '__main__':
    sys.exit(main())
