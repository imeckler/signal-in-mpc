#!/usr/bin/env python3
"""Regression checks for the single-operator command flow."""
import contextlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from pushbutton import flow as F


class Up(unittest.TestCase):
    def run_up(self, start_result, account_result, with_account=True):
        ctx = MagicMock()
        ctx.mine = ['mpc-node-0', 'mpc-node-1']
        ctx.d = dict(nodes=dict.fromkeys(ctx.mine), signal=dict(endpoint='local-test'),
                     app=dict(wireguard_public_key='set'))
        with contextlib.ExitStack() as stack:
            for name, value in [('Ctx', ctx), ('cmd_join', 0), ('load_set', ({}, [], [], [])),
                                ('cmd_start', start_result), ('cmd_account_local', account_result)]:
                stack.enter_context(patch.object(F, name, return_value=value))
            stack.enter_context(patch.object(F, 'say'))
            stack.enter_context(patch.object(F.B, 'fingerprint', return_value='test'))
            result = F.cmd_up(SimpleNamespace(with_account=with_account))
            return result, F.cmd_account_local.call_count

    def test_successful_account_supersedes_waiting_start_status(self):
        self.assertEqual(self.run_up(1, 0), (0, 1))

    def test_account_failure_is_returned(self):
        self.assertEqual(self.run_up(0, 1), (1, 1))

    def test_without_account_keeps_start_status(self):
        self.assertEqual(self.run_up(1, 0, with_account=False), (1, 0))


class Account(unittest.TestCase):
    def test_timeout_covers_readiness_ceremony_and_epoch_settling(self):
        for epoch_seconds in (20, 120, 3600):
            with self.subTest(epoch_seconds=epoch_seconds), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / 'common/tokens').mkdir(parents=True)
                (root / 'common/mpc-export.json').write_text('{}')
                ctx = MagicMock()
                ctx.mine = ['mpc-node-0', 'mpc-node-1']
                ctx.d = dict(name='test', database=dict(epoch_seconds=epoch_seconds))
                ctx.outbox = root
                for party, node in enumerate(ctx.mine):
                    (root / f'party-{party}').mkdir()
                    (root / f'party-{party}/credentials.share').write_text('test')
                    (root / f'{node}.bundle.json').write_text(json.dumps(dict(software=dict(image_id='test'))))
                with patch.object(F, 'Ctx', return_value=ctx), patch.object(F, 'inventory'), \
                     patch.object(F, 'step'), patch.object(F, 'say'), patch.object(F, 'play') as play:
                    self.assertEqual(F.cmd_account_install(SimpleNamespace(dir=str(root))), 0)
                variables = play.call_args.args[2]
                self.assertEqual(variables['settle_seconds'], 3 * epoch_seconds)
                self.assertGreaterEqual(variables['readiness_seconds'], max(600, 3 * epoch_seconds))
                self.assertGreater(play.call_args.kwargs['timeout'],
                                   variables['readiness_seconds'] + 900 + variables['settle_seconds'])


if __name__ == '__main__':
    unittest.main()
