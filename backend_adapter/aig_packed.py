"""Public DAG scheduling and lane packing; an unverified execution adapter.

Same numeric Lean AIG and XOR recovery as aig.py. Gates are grouped by AND
depth, then local XOR depth, so packing cannot introduce an extra AND round.
No protocol algorithm, secret-dependent control flow, or release operation.
"""
from collections import defaultdict
from .aig import validate, _plan, _xor_sources


def plan(image):
    validate(image)
    nodes = image['nodes']
    kinds = _plan(nodes, image['outputs'], True)
    depths, local = [0] * len(nodes), [0] * len(nodes)
    groups = defaultdict(list)
    roots = []
    for index, node in enumerate(nodes):
        if not kinds[index]:
            continue
        if node[0] != 2:
            roots.append(index)
            continue
        sources = _xor_sources(nodes, node) if kinds[index] == 2 else node[1:]
        left, _, right, _ = sources
        depth = max(depths[left], depths[right])
        if kinds[index] == 1:
            depths[index] = depth + 1
        else:
            depths[index] = depth
            local[index] = max(local[left] if depths[left] == depth else 0,
                               local[right] if depths[right] == depth else 0) + 1
        groups[depths[index], local[index], kinds[index]].append((index, sources))
    return roots, [(key, groups[key]) for key in sorted(groups)]


def execute(image, inputs, zero, one, pack, unpack, constant, *, lanes=64, begin_depth=None):
    """pack/unpack preserve little-endian lane order; constant(n,x) is public.

    Each input/output is still ONE shared bit; packed values exist only inside
    this adapter. Constant masks flip individual lanes without per-bit opcodes.
    """
    if type(lanes) is not int or not 1 <= lanes <= 64:
        raise ValueError('packing width must be 1..64')
    roots, groups = plan(image)
    if len(inputs) != image['input_bits']:
        raise ValueError('incorrect input bit count')
    offsets, offset = [], 0
    for width in image['input_widths']:
        offsets.append(offset)
        offset += width
    wires = [None] * len(image['nodes'])
    for index in roots:
        node = image['nodes'][index]
        if node[0] == 0:
            wires[index] = zero
        else:
            _, var, width, bit = node
            wires[index] = inputs[offsets[var] + width - 1 - bit]
    previous_depth = None
    for (depth, _, kind), gates in groups:
        if depth != previous_depth:
            if begin_depth is not None:
                begin_depth(depth)
            previous_depth = depth
        for start in range(0, len(gates), lanes):
            batch = gates[start:start + lanes]
            lhs = pack([wires[src[0]] for _, src in batch])
            rhs = pack([wires[src[2]] for _, src in batch])
            left_mask = sum(src[1] << i for i, (_, src) in enumerate(batch))
            right_mask = sum(src[3] << i for i, (_, src) in enumerate(batch))
            if left_mask:
                lhs = lhs ^ constant(len(batch), left_mask)
            if right_mask:
                rhs = rhs ^ constant(len(batch), right_mask)
            value = lhs ^ rhs if kind == 2 else lhs & rhs
            results = unpack(value, len(batch))
            if len(results) != len(batch):
                raise ValueError('incorrect unpacked lane count')
            for (index, _), bit in zip(batch, results):
                wires[index] = bit
    return [wires[index] ^ one if inverted else wires[index] for index, inverted in image['outputs']]


def execute_mpc(image, inputs):
    from Compiler.GC.types import sbit, sbits
    from Compiler.program import Program
    if any(not isinstance(value, sbit) or value.n != 1 for value in inputs):
        raise TypeError('expected single-lane secret input bits')
    def pack_bits(bits):
        # Upstream sbits.bit_compose([sbit]) widens to default sbits.n (40).
        # A singleton is already the complete one-lane representation.
        return bits[0] if len(bits) == 1 else sbits.bit_compose(bits)
    return execute(image, inputs, sbit(0), sbit(1), pack_bits,
                   lambda value, size: value.bit_decompose(size),
                   lambda size, value: sbits.get_type(size)(value),
                   begin_depth=lambda depth: Program.prog.curr_tape.start_new_basicblock(
                       name='aig-and-depth-' + str(depth)))
