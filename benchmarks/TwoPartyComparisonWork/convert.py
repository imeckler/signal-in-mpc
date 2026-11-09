"""Lean AIG -> identical Bristol gate stream, with private input/output sharing.

Unverified adapter boundary. Bit order matches backend_adapter.aig.execute.
Alice owns output pads and one XOR input share; Bob owns the other input share
and receives only padded outputs. Repetitions must supply fresh pads/preprocessing.
"""
import argparse
import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from backend_adapter.aig import validate, _plan, _xor_sources, execute


def convert(image):
    validate(image)
    n, m = image['input_bits'], len(image['outputs'])
    if n == 0:
        raise ValueError('at least one input required for constant construction')
    # Bristol n1 is Bob's input, n2 Alice's (legacy C2PC online ownership).
    gates, next_wire = [], 2*n+m
    def gate(op, a, b=0):
        nonlocal next_wire
        out = next_wire
        next_wire += 1
        gates.append((op, a, b, out))
        return out
    inputs = [gate('XOR', i, n+i) for i in range(n)]
    zero = gate('XOR', 0, 0)
    negated = {}
    def inv(w):
        if w not in negated:
            negated[w] = gate('INV', w)
        return negated[w]
    offsets, offset = [], 0
    for width in image['input_widths']:
        offsets.append(offset)
        offset += width
    nodes, wires = image['nodes'], {}
    kinds = _plan(nodes, image['outputs'], True)
    for i, node in enumerate(nodes):
        if not kinds[i]:
            continue
        if node == [0]:
            wires[i] = zero
        elif node[0] == 1:
            _, var, width, bit = node
            wires[i] = inputs[offsets[var]+width-1-bit]
        else:
            a, ai, b, bi = _xor_sources(nodes, node) if kinds[i] == 2 else node[1:]
            a, b = wires[a], wires[b]
            wires[i] = gate('XOR' if kinds[i] == 2 else 'AND', inv(a) if ai else a, inv(b) if bi else b)
    # Make outputs contiguous and last. Bob receives y XOR Alice-private pad.
    outputs = [inv(wires[w]) if flip else wires[w] for w, flip in image['outputs']]
    for j, w in enumerate(outputs):
        gate('XOR', w, 2*n+j)
    return {'n1': n, 'n2': n+m, 'n3': m, 'wires': next_wire, 'gates': gates}


def evaluate(circuit, inputs):
    wires = list(inputs) + [False]*(circuit['wires']-len(inputs))
    for op, a, b, out in circuit['gates']:
        wires[out] = not wires[a] if op == 'INV' else (wires[a] ^ wires[b] if op == 'XOR' else wires[a] & wires[b])
    return wires[-circuit['n3']:]


def write(circuit, path):
    with open(path, 'w') as f:
        f.write(f"{len(circuit['gates'])} {circuit['wires']}\n{circuit['n1']} {circuit['n2']} {circuit['n3']}\n\n")
        for op, a, b, out in circuit['gates']:
            f.write(f'1 1 {a} {out} INV\n' if op == 'INV' else f'2 1 {a} {b} {out} {op}\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('image', type=pathlib.Path)
    p.add_argument('output', type=pathlib.Path)
    args = p.parse_args()
    circuit = convert(json.loads(args.image.read_text()))
    write(circuit, args.output)
    print(json.dumps({'source_sha256': hashlib.sha256(args.image.read_bytes()).hexdigest(),
                      'bristol_sha256': hashlib.sha256(args.output.read_bytes()).hexdigest(),
                      **{k:v for k,v in circuit.items() if k != 'gates'},
                      'and': sum(g[0] == 'AND' for g in circuit['gates']),
                      'xor': sum(g[0] == 'XOR' for g in circuit['gates'])}))
