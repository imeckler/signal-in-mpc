#!/usr/bin/env python3
"""Unit checks of the configuration validation, the bundles and the fingerprint. No Docker, no
network: python3 deploy/pushbutton/test_pushbutton.py"""
import base64
import copy
import os
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from pushbutton import bundles as B  # noqa: E402
from pushbutton import config as C  # noqa: E402

DEPLOY = Path(__file__).resolve().parents[1]


def key(seed):
    return base64.b64encode(bytes([seed]) * 32).decode()


def good_deployment():
    raw = tomllib.loads((DEPLOY / 'deployment.example.toml').read_text())
    raw['application-server'].update(notify_public_key=key(1), signup_public_key=key(2))
    return raw


def good_operator():
    return {'operator': 'alice', 'admin_ips': ['auto'],
            'software': {'circuits_dir': '/tmp/c', 'word_dir': '/tmp/w'},
            'nodes': {'mpc-node-0': {'provider': 'hetzner', 'region': 'hel1', 'size': 'ccx43'},
                      'db-node-0': {'provider': 'upcloud', 'region': 'fi-hel1'},
                      'db-node-1': {'provider': 'existing', 'ssh': 'root@203.0.113.10', 'data_device': '/dev/sdb'}},
            'credentials': {'hetzner': {'token': 'env:HCLOUD_TOKEN'},
                            'upcloud': {'username': 'env:U', 'password': 'file:/x'}}}


class Deployment(unittest.TestCase):
    def bad(self, mutate, fragment):
        raw = good_deployment()
        mutate(raw)
        with self.assertRaises(C.ConfigError) as e:
            C.validate_deployment(raw)
        message = str(e.exception)
        self.assertIn(fragment, message)
        self.assertNotIn('\n', message, 'errors are one line')
        return message

    def test_example_validates_once_keys_are_filled(self):
        d = C.validate_deployment(good_deployment())
        self.assertEqual(d['db_count'], 5)
        self.assertEqual(d['security'], 'malicious')

    def test_example_as_shipped_asks_for_the_keys(self):
        raw = tomllib.loads((DEPLOY / 'deployment.example.toml').read_text())
        with self.assertRaises(C.ConfigError) as e:
            C.validate_deployment(raw)
        self.assertIn('notify_public_key', str(e.exception))

    def test_bad_values(self):
        self.bad(lambda r: r.update(security='paranoid'), "security must be one of 'malicious', 'semi-honest'")
        self.bad(lambda r: r.update(worker_logic='python'), "worker_logic must be one of")
        self.bad(lambda r: r.update(name='Bad Name'), 'name must be')
        self.bad(lambda r: r.update(colour='blue'), 'unknown setting "colour"')
        self.bad(lambda r: r['signal'].update(endpoint='staging'), 'endpoint must be one of')
        self.bad(lambda r: r['application-server'].update(notify_public_key='abc'), 'notify_public_key must be')
        self.bad(lambda r: r['nodes'].pop('mpc-node-1'), '[nodes.mpc-node-1] is missing')
        self.bad(lambda r: r['nodes'].pop('db-node-2'), 'without gaps')
        self.bad(lambda r: r['nodes'].update({'web-1': {'operator': 'x'}}), 'is not a node name')
        self.bad(lambda r: r['database'].update(threshold=5, max_malicious=1), 'exceeds the 5 database nodes')
        self.bad(lambda r: r['database'].update(threshold=6), 'more than the 5 database nodes')
        self.bad(lambda r: r['database'].update(epoch_seconds=2), 'epoch_seconds must be a whole number from 4')
        self.bad(lambda r: [r['nodes'].pop(f'db-node-{i}') for i in (2, 3, 4)], 'too few')
        self.bad(lambda r: r['software'].update(node_image='latest'), 'node_image must be a 64-hex-digit digest')
        self.bad(lambda r: r['monitoring'].update(combined_page_on='db-node-9'), 'is not one of the nodes')

    def test_six_database_nodes_validate_with_a_warning(self):
        raw = good_deployment()
        raw['nodes']['db-node-5'] = {'operator': 'carol'}
        d = C.validate_deployment(raw)
        self.assertEqual(d['db_count'], 6)
        self.assertTrue(any('only 5 have ever been run' in w for w in C.deployment_warnings(d)))

    def test_trust_warnings(self):
        raw = good_deployment()
        raw['nodes']['mpc-node-1']['operator'] = 'alice'
        for i in range(3):
            raw['nodes'][f'db-node-{i}']['operator'] = 'alice'
        warnings = C.deployment_warnings(C.validate_deployment(raw))
        self.assertTrue(any('BOTH computation nodes' in w for w in warnings))
        self.assertTrue(any('reconstruct every contact' in w for w in warnings))


class Operator(unittest.TestCase):
    def setUp(self):
        self.d = C.validate_deployment(good_deployment())

    def bad(self, mutate, fragment, deployment=None):
        raw = good_operator()
        mutate(raw)
        with self.assertRaises(C.ConfigError) as e:
            o = C.validate_operator(raw)
            C.check_pair(deployment or self.d, o)
        self.assertIn(fragment, str(e.exception))
        self.assertNotIn('\n', str(e.exception))

    def test_good(self):
        o = C.validate_operator(good_operator())
        d = C.validate_deployment(dict(good_deployment(), signal={'endpoint': 'none'}))
        self.assertEqual(C.check_pair(d, o), ['db-node-0', 'db-node-1', 'mpc-node-0'])

    def test_local_test_needs_local_machines(self):
        self.bad(lambda r: None, 'endpoint = "local-test" uses the test Signal server on this computer')

    def test_bad(self):
        none = C.validate_deployment(dict(good_deployment(), signal={'endpoint': 'none'}))
        self.bad(lambda r: r['nodes']['mpc-node-0'].update(provider='aws'), 'provider must be one of')
        self.bad(lambda r: r['nodes']['mpc-node-0'].update(region='mars1'), "region 'mars1' is not one")
        self.bad(lambda r: r['nodes']['db-node-1'].update(ssh='203.0.113.10'), 'ssh must be "user@address"')
        self.bad(lambda r: r['nodes']['db-node-1'].update(data_path='/srv/data'), 'give exactly one of data_device')
        self.bad(lambda r: r['nodes'].pop('db-node-1'), 'add [nodes.db-node-1]', none)
        self.bad(lambda r: r['nodes'].update({'mpc-node-1': {'provider': 'local'}}), 'says "bob" operates it', none)
        self.bad(lambda r: r['credentials'].pop('hetzner'), '[credentials.hetzner] is missing')
        self.bad(lambda r: r.update(operator='mallory'), 'names no node for operator "mallory"', none)
        self.bad(lambda r: r['software'].pop('circuits_dir'), 'set [software] circuits_dir', none)
        self.bad(lambda r: r.update(admin_ips=['not-an-ip']), "admin_ips entry 'not-an-ip'")
        self.bad(lambda r: r['nodes']['mpc-node-0'].update(colour='red'), 'unknown setting "colour"')

    def test_inline_secret_is_warned(self):
        raw = good_operator()
        raw['credentials']['hetzner']['token'] = 'abc123'
        o = C.validate_operator(raw)
        self.assertTrue(any('holds a secret inline' in w for w in C.operator_warnings(self.d, o)))

    def test_same_provider_for_both_computation_nodes(self):
        raw = good_deployment()
        raw['nodes']['mpc-node-1']['operator'] = 'alice'
        raw['signal'] = {'endpoint': 'none'}
        d = C.validate_deployment(raw)
        op = good_operator()
        op['nodes']['mpc-node-1'] = {'provider': 'hetzner', 'region': 'fsn1'}
        with self.assertRaises(C.ConfigError) as e:
            C.check_pair(d, C.validate_operator(op))
        self.assertIn('allow_same_provider', str(e.exception))
        raw['allow_same_provider'] = True
        C.check_pair(C.validate_deployment(raw), C.validate_operator(op))

    def test_secret_reference(self):
        os.environ['PB_TEST_SECRET'] = 'v'
        self.assertEqual(C.resolve_secret('env:PB_TEST_SECRET'), 'v')
        with tempfile.NamedTemporaryFile('w', delete=False) as f:
            f.write('w\n')
        self.assertEqual(C.resolve_secret(f'file:{f.name}'), 'w')
        with self.assertRaises(C.ConfigError):
            C.resolve_secret('env:PB_TEST_NOT_SET_ANYWHERE')


def bundle_set(d):
    out = {}
    for i, node in enumerate(sorted(d['nodes'])):
        b = dict(format=B.FORMAT, deployment=d['name'], deployment_sha256=B.deployment_digest(d), node=node,
                 operator=d['nodes'][node]['operator'], role=C.role(node), provider='local',
                 wireguard=dict(public_key=key(10 + i), endpoint=f'192.0.2.{i + 1}:51820', address=C.wg_address(node)),
                 software=dict(tool_commit='a' * 40, tool_digest='7' * 64, images='prebuilt', image_id='b' * 64))
        if node in C.MPC_NODES:
            b['mpc'] = dict(link_public_key='-----BEGIN PUBLIC KEY-----x', db_client_public_key=key(40 + i), field_certificate='-----BEGIN CERTIFICATE-----')
            b['software'].update(mode=d['security'], worker_logic='legacy', manifest_sha256='c' * 64, word_dir_sha256='d' * 64,
                                 pins_sha256='e' * 64, settings={'serve': '1', 'receive': '2', 'notify': '3', 'worker_session': '4'})
        else:
            b['db'] = dict(public_key=key(60 + i), signing_public_key=key(80 + i), monitor_public_key=key(99))
            b['software']['image_id'] = 'f' * 64
        out[node] = b
    return out


class Bundles(unittest.TestCase):
    def setUp(self):
        self.d = C.validate_deployment(good_deployment())
        self.b = bundle_set(self.d)

    def test_complete_set_has_a_stable_fingerprint(self):
        errors, warnings, rows = B.check(self.d, self.b)
        self.assertEqual(errors, [])
        fp = B.fingerprint(self.d, self.b)
        self.assertRegex(fp, r'^\d{5}(-\d{5}){5}$')
        self.assertEqual(fp, B.fingerprint(copy.deepcopy(self.d), copy.deepcopy(self.b)))

    def test_swapped_wireguard_key_changes_the_fingerprint(self):
        fp = B.fingerprint(self.d, self.b)
        tampered = copy.deepcopy(self.b)
        tampered['db-node-3']['wireguard']['public_key'] = key(200)
        self.assertNotEqual(fp, B.fingerprint(self.d, tampered))
        self.assertEqual(B.check(self.d, tampered)[0], [])   # still consistent: only the fingerprint catches it

    def test_software_and_deployment_are_covered(self):
        fp = B.fingerprint(self.d, self.b)
        other = copy.deepcopy(self.b)
        other['mpc-node-1']['software']['tool_commit'] = '9' * 40
        self.assertNotEqual(fp, B.fingerprint(self.d, other))
        errors, warnings, _ = B.check(self.d, other)
        self.assertEqual(errors, [])                       # same tool files, another commit: a warning
        self.assertTrue(any('commit' in w for w in warnings))
        other['mpc-node-1']['software']['tool_digest'] = '8' * 64
        self.assertTrue(any('deploy tool itself' in e for e in B.check(self.d, other)[0]))
        d2 = copy.deepcopy(self.d)
        d2['security'] = 'semi-honest'
        self.assertNotEqual(fp, B.fingerprint(d2, self.b))

    def test_inconsistencies(self):
        b = copy.deepcopy(self.b)
        del b['db-node-4']
        self.assertTrue(any('missing: db-node-4' in e for e in B.check(self.d, b)[0]))
        b = copy.deepcopy(self.b)
        b['db-node-1']['wireguard']['public_key'] = b['db-node-0']['wireguard']['public_key']
        self.assertTrue(any('same WireGuard public key' in e for e in B.check(self.d, b)[0]))
        b = copy.deepcopy(self.b)
        b['mpc-node-1']['software']['manifest_sha256'] = '0' * 64
        self.assertTrue(any('circuit manifest differs' in e for e in B.check(self.d, b)[0]))
        b = copy.deepcopy(self.b)
        b['mpc-node-1']['software']['image_id'] = '1' * 64
        self.assertTrue(any('computation image differs' in e for e in B.check(self.d, b)[0]))
        b = copy.deepcopy(self.b)
        b['db-node-2']['operator'] = 'mallory'
        self.assertTrue(any('made by "mallory"' in e for e in B.check(self.d, b)[0]))

    def test_independent_builds_are_reported_not_refused(self):
        raw = good_deployment()
        raw['software']['builds'] = 'each-operator'
        d = C.validate_deployment(raw)
        b = bundle_set(d)
        for n in C.MPC_NODES:
            b[n]['software']['images'] = 'build-here'
        b['mpc-node-1']['software']['image_id'] = '1' * 64
        errors, warnings, _ = B.check(d, b)
        self.assertEqual(errors, [])
        self.assertTrue(any('built independently' in w for w in warnings))

    def test_nothing_secret_is_written(self):
        b = copy.deepcopy(self.b['db-node-0'])
        b['db']['secret_seed'] = 'x'
        with self.assertRaises(ValueError):
            B.assert_public(b)
        with self.assertRaises(ValueError):
            B.assert_public(dict(self.b['mpc-node-0'], extra='-----BEGIN PRIVATE KEY-----'))

    def test_network_config_from_public_parts(self):
        net = B.network_config(self.d, self.b)
        self.assertEqual(len(net['public_keys']), 5)
        self.assertEqual(net['compute_addresses'][0], '10.77.0.10:11001')
        self.assertEqual(net['notify_public_key'], key(1))
        self.assertEqual(net['threshold'], 3)


if __name__ == '__main__':
    unittest.main(verbosity=1)
