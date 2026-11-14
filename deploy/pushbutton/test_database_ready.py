#!/usr/bin/env python3
"""Account startup regression checks; no Docker or network required."""
import contextlib
import importlib.util
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

spec = importlib.util.spec_from_file_location('pb_health', Path(__file__).resolve().parents[1] / 'node/pb_health.py')
health = importlib.util.module_from_spec(spec)
spec.loader.exec_module(health)


class DatabaseReady(unittest.TestCase):
    def run_check(self, reports, reachable=True):
        with tempfile.TemporaryDirectory() as tmp:
            network = Path(tmp) / 'network.json'
            network.write_text(json.dumps(dict(compute_addresses=[f'10.77.0.{i}:11001' for i in range(5)],
                                               threshold=3, max_malicious_parties=1)))
            responses = []
            for report in reports:
                if isinstance(report, Exception):
                    responses.append(report)
                else:
                    response = MagicMock()
                    response.__enter__.return_value.read.return_value = json.dumps(report).encode()
                    responses.append(response)
            with patch.object(health.urllib.request, 'urlopen', side_effect=responses), \
                 patch.object(health.socket, 'create_connection', side_effect=None if reachable else OSError('refused')) as connect, \
                 patch.object(health.time, 'monotonic', side_effect=[0, 0, 601]), \
                 patch.object(health.time, 'sleep'), contextlib.redirect_stdout(io.StringIO()):
                return health.db_ready(network, 600), connect.call_count

    @staticmethod
    def ready(epoch=123):
        return dict(database=dict(last_epoch=epoch), containers={'ssdb-node': dict(state='running')})

    def test_quorum_with_one_unavailable_node(self):
        self.assertEqual(self.run_check([self.ready()] * 4 + [OSError('offline')]), (0, 4))

    def test_running_ports_without_consensus_do_not_start_ceremony(self):
        self.assertEqual(self.run_check([self.ready(None)] * 5), (1, 0))

    def test_waiting_barrier_cannot_reuse_old_epoch(self):
        report = dict(self.ready(), database_waiting=True)
        self.assertEqual(self.run_check([report] * 5), (1, 0))

    def test_insufficient_quorum_times_out(self):
        self.assertEqual(self.run_check([self.ready()] * 3 + [OSError('offline')] * 2), (1, 3))

    def test_health_without_compute_listener_does_not_start_ceremony(self):
        self.assertEqual(self.run_check([self.ready()] * 5, reachable=False), (1, 5))

    def test_stopped_container_cannot_reuse_old_epoch(self):
        report = self.ready()
        report['containers']['ssdb-node']['state'] = 'exited'
        self.assertEqual(self.run_check([report] * 5), (1, 0))


if __name__ == '__main__':
    unittest.main()
