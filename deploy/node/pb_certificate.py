#!/usr/bin/env python3
"""The Signal sender-certificate check and refresh trigger, run hourly (with jitter) by
pb-certificate.timer on each computation node. Standard library only.

    pb_certificate.py /etc/pb/certificate.json

It reads the certificate's expiry (public: the server hands the certificate to every recipient)
from the account material, writes DATA/pb/status/certificate.json for the health endpoint and the
monitoring page, and when less than `margin_hours` remain it calls the refresh entry point.

THE REFRESH ITSELF DOES NOT EXIST YET (DEPLOYMENT.md "Proposed changes", P-CERT). What exists is
the ceremony's `certificate` stage, which is NOT a safe refresh: it re-uploads the one-time
prekeys, it needs the registration's credentials share (absent after the account step), its
port block overlaps the daemon's send sessions, the server closes the daemon's receive socket
(4409), and the certificate it fetches goes to a side file no session reads (sessions take the
certificate from the account's row on the database nodes, which nothing rewrites). So the entry
point below only records "refresh due" and never contacts any Signal host. When the daemon gains
the joint job, `refresh()` becomes one request to the local daemon (party 0 leads; party 1's
timer only reports), and nothing else here changes.
"""
import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pb_node import sender_certificate_expiry  # noqa: E402


def refresh(config):
    """TODO(P-CERT): ask the local daemon for the joint certificate refresh, e.g.
    {"op": "refresh-certificate"} on the application port, led by party 0. Not implemented in the
    daemon: report that, do nothing else."""
    if config.get('party') != 0:
        return False, 'party 1 waits for party 0 to lead the joint refresh'
    return False, ('refresh due, but the two-party refresh job does not exist yet (proposed change P-CERT): '
                   'the owner refreshes by the documented manual procedure')


def main():
    config = json.loads(Path(sys.argv[1]).read_text())
    data = Path(config['data_root'])
    out = data / 'pb/status/certificate.json'
    old = json.loads(out.read_text()) if out.exists() else {}
    now = time.time()
    status = dict(checked_at=int(now), margin_hours=config['margin_hours'], attempts=old.get('attempts', 0),
                  last_attempt=old.get('last_attempt'))
    export = data / 'tls-mpc/scaffold/mpc-export.json'
    if config.get('endpoint') == 'none':
        status.update(state='no-endpoint', message='no Signal endpoint configured')
    elif not export.exists():
        status.update(state='no-account', message='no account installed yet')
    else:
        try:
            expires = sender_certificate_expiry(export)
        except (KeyError, ValueError, IndexError) as e:
            status.update(state='unreadable', message=f'cannot read the certificate: {type(e).__name__}')
            expires = None
        if expires:
            left = (expires / 1000 - now) / 3600
            status.update(expires_ms=expires, hours_left=round(left, 1))
            if left <= 0:
                status.update(state='expired', message='EXPIRED: sealed sends fail until it is refreshed')
            elif left < config['margin_hours']:
                ok, message = refresh(config)
                status.update(state='refreshed' if ok else 'refresh-due', message=f'{left:.0f} h left; {message}',
                              attempts=status['attempts'] + 1, last_attempt=int(now))
            else:
                status.update(state='ok', message=f'{left:.0f} h left (refresh below {config["margin_hours"]} h)')
    tmp = out.with_suffix('.tmp')
    tmp.write_text(json.dumps(status, indent=1, sort_keys=True) + '\n')
    os.chmod(tmp, 0o644)
    tmp.replace(out)
    print(json.dumps(status))
    return 0


if __name__ == '__main__':
    sys.exit(main())
