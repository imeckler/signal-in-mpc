import json
import pathlib
import random
from convert import convert, evaluate, execute

root = pathlib.Path(__file__).resolve().parents[2]
paths = [root/'.deps/reference-fixslice-cost-v1/reference-1x1.json',
         root/'.deps/sha-backend-profiles/reference-block.json']
rng = random.Random(71812)
cases = 0
for path in paths:
    image = json.loads(path.read_text())
    circuit = convert(image)
    n, m = image['input_bits'], len(image['outputs'])
    for _ in range(8):
        logical = [bool(rng.getrandbits(1)) for _ in range(n)]
        bob = [bool(rng.getrandbits(1)) for _ in range(n)]
        alice = [a ^ b for a,b in zip(logical,bob)]
        pads = [bool(rng.getrandbits(1)) for _ in range(m)]
        expected = execute(image, logical, False, True)
        actual = [a ^ b for a,b in zip(evaluate(circuit,bob+alice+pads),pads)]
        assert actual == expected, path
        cases += 1
print(json.dumps({'passed': True, 'random_share_cases': cases, 'graphs': [str(p.relative_to(root)) for p in paths]}))
