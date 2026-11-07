"""Unverified executor for Lean's proved bit-vector/AIG numeric export.

This module contains only public DAG traversal and shared AND/XOR. In particular,
it contains no SHA, HMAC, TLS, Signal, field conversion, or reveal implementation.

The executor recognizes a generic XOR pattern and skips gates made unreachable
by that rewrite. This remains part of the unverified execution boundary. The
local Boolean identity is proved in AigExport.lean; this Python traversal is not.
"""


def validate(image):
    if not isinstance(image, dict) or image.get('format') != 'tls-mpc-aig-v1':
        raise ValueError('unsupported Lean DAG format')
    size, widths = image.get('input_bits'), image.get('input_widths')
    nodes, outputs = image.get('nodes'), image.get('outputs')
    if (type(size) is not int or size < 0 or not isinstance(widths, list)
            or any(type(w) is not int or w <= 0 for w in widths)
            or sum(widths) != size or not isinstance(nodes, list) or not isinstance(outputs, list)):
        raise ValueError('invalid DAG dimensions')
    for index, node in enumerate(nodes):
        if not isinstance(node, list) or any(type(n) is not int or n < 0 for n in node):
            raise ValueError('invalid numeric node')
        if node == [0]:
            continue
        if len(node) == 4 and node[0] == 1:
            _, var, width, bit = node
            if var >= len(widths) or width != widths[var] or bit >= width:
                raise ValueError('invalid input reference')
        elif len(node) == 5 and node[0] == 2:
            _, left, linv, right, rinv = node
            if left >= index or right >= index or linv not in (0, 1) or rinv not in (0, 1):
                raise ValueError('invalid DAG edge or inversion')
        else:
            raise ValueError('unknown DAG node')
    for ref in outputs:
        if (not isinstance(ref, list) or len(ref) != 2
                or any(type(n) is not int or n < 0 for n in ref)
                or ref[0] >= len(nodes) or ref[1] not in (0, 1)):
            raise ValueError('invalid output reference')
    return image


def _xor_sources(nodes, node):
    if node[0] != 2 or node[2] != 1 or node[4] != 1:
        return None
    left, right = nodes[node[1]], nodes[node[3]]
    if left[0] != 2 or right[0] != 2:
        return None
    _, a, ai, b, bi = left
    _, c, ci, d, di = right
    if ((a == c and b == d and ai != ci and bi != di)
            or (a == d and b == c and ai != di and bi != ci)):
        return a, ai, b, bi
    return None


def _plan(nodes, outputs, optimize):
    # 0: unreachable, 1: original node, 2: XOR replacing an AND pattern.
    kinds = bytearray(len(nodes))
    pending = [wire for wire, _ in outputs]
    while pending:
        index = pending.pop()
        if kinds[index]:
            continue
        node = nodes[index]
        sources = _xor_sources(nodes, node) if optimize else None
        kinds[index] = 2 if sources is not None else 1
        if sources is not None:
            pending.extend((sources[0], sources[2]))
        elif node[0] == 2:
            pending.extend((node[1], node[3]))
    return kinds


def statistics(image):
    validate(image)
    kinds = _plan(image['nodes'], image['outputs'], True)
    return {'raw_and_gates': sum(node[0] == 2 for node in image['nodes']),
            'executed_and_gates': sum(kind == 1 and node[0] == 2
                                      for kind, node in zip(kinds, image['nodes'])),
            'executed_xor_gates': kinds.count(2),
            'unreachable_nodes': kinds.count(0)}


def execute(image, inputs, zero, one, *, optimize=True):
    validate(image)
    if len(inputs) != image['input_bits']:
        raise ValueError('incorrect input bit count')
    offsets, offset = [], 0
    for width in image['input_widths']:
        offsets.append(offset)
        offset += width
    nodes = image['nodes']
    kinds = _plan(nodes, image['outputs'], optimize)
    wires = [None] * len(nodes)
    for index, node in enumerate(nodes):
        if kinds[index] == 0:
            continue
        if node[0] == 0:
            value = zero
        elif node[0] == 1:
            _, var, width, bit = node
            value = inputs[offsets[var] + width - 1 - bit]
        else:
            left, linv, right, rinv = (_xor_sources(nodes, node)
                                       if kinds[index] == 2 else node[1:])
            lhs = wires[left] ^ one if linv else wires[left]
            rhs = wires[right] ^ one if rinv else wires[right]
            value = lhs ^ rhs if kinds[index] == 2 else lhs & rhs
        wires[index] = value
    return [wires[wire] ^ one if invert else wires[wire] for wire, invert in image['outputs']]
