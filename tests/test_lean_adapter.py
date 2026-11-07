"""Reject malformed artifacts at the unverified execution boundary."""

import unittest
import copy
from pathlib import Path
import subprocess
import random

from backend_adapter.boolean import execute, validate
from backend_adapter import aig


class LeanAdapter(unittest.TestCase):
    def image(self, block, size=1):
        return {'format': 'tls-mpc-boolean-v1', 'input_bits': size, 'outputs': [block]}

    def test_malformed_artifacts_are_rejected(self):
        malformed = [[], [[0, 1]], [[0, -1]], [[0, True]], [[1, 2]], [[1, 0, 1]],
                     [[2]], [[3]], [[4]], [[5]], [[6]], [[1, 0], [1, 1]]]
        for block in malformed:
            with self.subTest(block=block), self.assertRaises(ValueError):
                validate(self.image(block))

    def test_input_size_is_checked(self):
        with self.assertRaises(ValueError):
            execute(self.image([[0, 0]]), [], False, True)

    def test_dag_rejects_forward_edges_and_inconsistent_inputs(self):
        good = {'format': 'tls-mpc-aig-v1', 'input_bits': 8, 'input_widths': [8],
                'nodes': [[0], [1, 0, 8, 7], [2, 1, 0, 0, 1]], 'outputs': [[2, 0]]}
        self.assertEqual(execute(good, [1] * 8, 0, 1), [1])
        for node in ([2, 2, 0, 0, 1], [2, 1, 2, 0, 0], [1, 1, 8, 0],
                     [1, 0, 7, 0], [1, 0, 8, 8], [0, 0], [True], [9]):
            image = copy.deepcopy(good)
            image['nodes'][2] = node
            with self.subTest(node=node), self.assertRaises(ValueError):
                validate(image)
        for ref in ([3, 0], [1, 2], [True, 0], [], [-1, 0]):
            image = copy.deepcopy(good)
            image['outputs'] = [ref]
            with self.subTest(ref=ref), self.assertRaises(ValueError):
                validate(image)

    def test_export_rejects_invalid_public_lengths(self):
        executable = Path(__file__).resolve().parents[1] / '.lake/build/bin/emit_mpc'
        if not executable.exists():
            self.skipTest('run lake build emit_mpc first')
        cases = [('sha256', '4097'), ('sha256', '-1'), ('hmac-sha256', '4097', '1'),
                 ('hkdf-sha256', '0', '0', '0', '129'), ('tls-expand-label', '', '0', '16'),
                 ('tls-expand-label', 'x' * 250, '0', '16'), ('tls-expand-label', 'key', '256', '16'),
                 ('tls-expand-label', 'kéy', '0', '16'), ('tls-inner', '16385', '0')]
        for args in cases:
            result = subprocess.run([str(executable), *args], capture_output=True, text=True, timeout=10)
            with self.subTest(args=args):
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, '')

    def test_xor_rewrite_preserves_polarity_and_shared_children(self):
        for ai in (0, 1):
            for bi in (0, 1):
                for swap in (False, True):
                    for keep_child in (False, True):
                        right = [2, 2, 1 - bi, 1, 1 - ai] if swap else [2, 1, 1 - ai, 2, 1 - bi]
                        image = {'format': 'tls-mpc-aig-v1', 'input_bits': 2, 'input_widths': [1, 1],
                                 'nodes': [[0], [1, 0, 1, 0], [1, 1, 1, 0],
                                           [2, 1, ai, 2, bi], right, [2, 3, 1, 4, 1]],
                                 'outputs': [[5, 0], [5, 1]] + ([[3, 0]] if keep_child else [])}
                        # Four packed lanes exhaust both Boolean inputs.
                        self.assertEqual(aig.execute(image, [0b1010, 0b1100], 0, 15),
                                         aig.execute(image, [0b1010, 0b1100], 0, 15, optimize=False))
                        self.assertEqual(aig.statistics(image)['executed_and_gates'], int(keep_child))
                        self.assertEqual(aig.statistics(image)['executed_xor_gates'], 1)

    def test_dag_rewrite_matches_unoptimized_semantics_exhaustively(self):
        rng = random.Random(42019)
        for _ in range(30):
            nodes = [[0]] + [[1, i, 1, 0] for i in range(3)]
            for _ in range(50):
                a, b = rng.randrange(len(nodes)), rng.randrange(len(nodes))
                ai, bi = rng.randrange(2), rng.randrange(2)
                if rng.randrange(2):
                    left = len(nodes)
                    nodes.extend([[2, a, ai, b, bi], [2, b, 1 - bi, a, 1 - ai],
                                  [2, left, 1, left + 1, 1]])
                else:
                    nodes.append([2, a, ai, b, bi])
            image = {'format': 'tls-mpc-aig-v1', 'input_bits': 3, 'input_widths': [1] * 3,
                     'nodes': nodes,
                     'outputs': [[rng.randrange(len(nodes)), rng.randrange(2)] for _ in range(12)]}
            # Eight packed lanes exhaust all assignments, including complement edges.
            inputs = [0b10101010, 0b11001100, 0b11110000]
            self.assertEqual(aig.execute(image, inputs, 0, 255),
                             aig.execute(image, inputs, 0, 255, optimize=False))


if __name__ == '__main__':
    unittest.main()
