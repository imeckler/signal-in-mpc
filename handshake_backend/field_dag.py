"""Validate and execute tls-mpc-field-dag-v1, without reveal instructions.

The generic evaluator is outside the Lean proof. Values can be MP-SPDZ sint
registers or the clear modular test type below. Only public artifact metadata
and instruction indexes control Python branches.
"""

import json
from pathlib import Path
import re

MODULUS = 2**255 - 19
MAX_BYTES = 32 * 1024 * 1024
MAX_NODES = 250_000
MAX_INPUTS = 4096
MAX_OUTPUTS = 256


def _index(value, bound, what):
    if type(value) is not int or not 0 <= value < bound:
        raise ValueError(f'invalid {what}')
    return value


def _canonical(value):
    if (not isinstance(value, str) or len(value) > 77
            or re.fullmatch(r'0|[1-9][0-9]*', value) is None
            or int(value) >= MODULUS):
        raise ValueError('noncanonical field constant')
    return int(value)


def validate(image):
    if not isinstance(image, dict) or image.get('format') != 'tls-mpc-field-dag-v1':
        raise ValueError('unsupported field DAG format')
    if image.get('modulus') != str(MODULUS):
        raise ValueError('field DAG modulus must be 2^255-19')
    size = image.get('input_count')
    if type(size) is not int or not 0 <= size <= MAX_INPUTS:
        raise ValueError('invalid field input count')
    bits = image.get('bit_inputs')
    if not isinstance(bits, list) or len(bits) > size:
        raise ValueError('invalid bit input list')
    for bit in bits:
        _index(bit, size, 'bit input')
    if len(set(bits)) != len(bits):
        raise ValueError('duplicate bit input')
    nodes = image.get('nodes')
    if not isinstance(nodes, list) or not 0 < len(nodes) <= MAX_NODES:
        raise ValueError('invalid field node count')
    for position, node in enumerate(nodes):
        if not isinstance(node, dict):
            raise ValueError('field node must be an object')
        op = node.get('op')
        if op == 'input' and set(node) == {'op', 'index'}:
            _index(node['index'], size, 'input index')
        elif op == 'const' and set(node) == {'op', 'value'}:
            _canonical(node['value'])
        elif op in ('add', 'sub', 'mul') and set(node) == {'op', 'left', 'right'}:
            _index(node['left'], position, 'left backward reference')
            _index(node['right'], position, 'right backward reference')
        else:
            raise ValueError('invalid field node or unknown operation')
    outputs = image.get('outputs')
    if not isinstance(outputs, list) or not 0 < len(outputs) <= MAX_OUTPUTS:
        raise ValueError('invalid field output count')
    for output in outputs:
        _index(output, len(nodes), 'output index')
    return image


def load(path):
    path = Path(path)
    if path.stat().st_size > MAX_BYTES:
        raise ValueError('field artifact exceeds size bound')
    # Duplicate keys must not admit two conflicting interpretations of the ABI.
    def object_pairs(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('duplicate JSON object key')
            result[key] = value
        return result
    return validate(json.loads(path.read_text(), object_pairs_hook=object_pairs))


def execute(image, inputs, constant):
    """Return field registers; the caller must establish bit input validity.

    Use mixed.execute_secret for arbitrary MPC input registers. Passing scalar
    bits from an established binary-to-field conversion is also sufficient.
    """
    validate(image)
    if len(inputs) != image['input_count']:
        raise ValueError('incorrect field input count')
    values = []
    for node in image['nodes']:
        op = node['op']
        if op == 'input':
            value = inputs[node['index']]
        elif op == 'const':
            value = constant(int(node['value']))
        else:
            left, right = values[node['left']], values[node['right']]
            value = left + right if op == 'add' else left - right if op == 'sub' else left * right
        values.append(value)
    return [values[index] for index in image['outputs']]


class ClearField:
    """Test oracle values, never an MPC backend or key import path."""

    def __init__(self, value):
        self.value = int(value) % MODULUS

    def __add__(self, other):
        return type(self)(self.value + other.value)

    def __sub__(self, other):
        return type(self)(self.value - other.value)

    def __mul__(self, other):
        return type(self)(self.value * other.value)


def evaluate_clear(image, inputs):
    validate(image)
    if len(inputs) != image['input_count']:
        raise ValueError('incorrect clear input count')
    if any(type(x) is not int or not 0 <= x < MODULUS for x in inputs):
        raise ValueError('clear inputs must be canonical field integers')
    if any(inputs[index] not in (0, 1) for index in image['bit_inputs']):
        raise ValueError('invalid clear bit input')
    return [value.value for value in execute(image, list(map(ClearField, inputs)), ClearField)]
