"""Generic shared-bit executor for Lean's numeric Boolean instruction ABI.

No TLS/Signal algorithms, cryptographic primitives, or reveal operations live
here. This adapter and MP-SPDZ's compiler/runtime are outside the Lean proof.
The artifact's mathematical execution is defined by TlsMpc/Artifact.lean.
"""

import json
from pathlib import Path


def validate(image):
    if isinstance(image, dict) and image.get('format') == 'tls-mpc-aig-v1':
        from .aig import validate as validate_dag
        return validate_dag(image)
    if not isinstance(image, dict) or image.get('format') != 'tls-mpc-boolean-v1':
        raise ValueError('unsupported Lean circuit format')
    size, outputs = image.get('input_bits'), image.get('outputs')
    if type(size) is not int or size < 0 or not isinstance(outputs, list):
        raise ValueError('invalid circuit dimensions')
    for block in outputs:
        if not isinstance(block, list):
            raise ValueError('output must be an instruction block')
        height = 0
        for instruction in block:
            if (not isinstance(instruction, list) or not instruction
                    or any(type(x) is not int or x < 0 for x in instruction)):
                raise ValueError('malformed numeric instruction')
            op = instruction[0]
            if op == 0:
                if len(instruction) != 2 or instruction[1] >= size:
                    raise ValueError('load index outside declared inputs')
                height += 1
            elif op == 1:
                if len(instruction) != 2 or instruction[1] not in (0, 1):
                    raise ValueError('invalid literal')
                height += 1
            elif op in (2, 3, 4, 5):
                if len(instruction) != 1 or height < (2 if op in (3, 4) else 1):
                    raise ValueError('invalid stack operation')
                height += 1 if op == 2 else -1 if op in (3, 4) else 0
            else:
                raise ValueError('unknown opcode')
        if height != 1:
            raise ValueError('each output block must leave exactly one bit')
    return image


def load(path):
    return validate(json.loads(Path(path).read_text()))


def execute(image, inputs, zero, one):
    """Interpret public instructions over shared bits; return shared outputs."""
    if isinstance(image, dict) and image.get('format') == 'tls-mpc-aig-v1':
        from .aig import execute as execute_dag
        return execute_dag(image, inputs, zero, one)
    validate(image)
    if len(inputs) != image['input_bits']:
        raise ValueError('incorrect input bit count')
    outputs = []
    for block in image['outputs']:
        stack = []
        for instruction in block:
            op = instruction[0]
            if op == 0:
                stack.append(inputs[instruction[1]])
            elif op == 1:
                stack.append(one if instruction[1] else zero)
            elif op == 2:
                stack.append(stack[-1])
            elif op in (3, 4):
                b, a = stack.pop(), stack.pop()
                stack.append(a ^ b if op == 3 else a & b)
            else:
                stack[-1] = stack[-1] ^ one
        outputs.append(stack[0])
    return outputs
