"""Shared lowering of Lean bit-vector circuit exports to the flat gate format.

Unverified adapter boundary: DAG traversal and XOR recognition are
`backend_adapter.aig`; this module only fixes one bit order. Variable v, bit b
(weight 2^b) is wire offset(v)+b; outputs are taken in the order the Lean
emitter lists them (EmitHybridKdf.lean lists bit b of output byte j at 8*j+b).
"""
import pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from backend_adapter.aig import validate,_plan,_xor_sources
def lower(image,msb_first=False):
    """msb_first selects the convention of the project's standard exports
    (Main.lean / backend_adapter): variable v, bit b is wire
    offset(v)+width-1-b, outputs already listed most significant bit first."""
    validate(image)
    offsets=[];n=0
    for w in image['input_widths']:offsets.append(n);n+=w
    gates=[]
    def gate(op,a,b=0):gates.append((op,a,b));return n+len(gates)-1
    zero=None;negated={}
    def inv(w):
        if w not in negated:negated[w]=gate('N',w)
        return negated[w]
    nodes=image['nodes'];kinds=_plan(nodes,image['outputs'],True);wires={}
    for i,node in enumerate(nodes):
        if not kinds[i]:continue
        if node==[0]:
            if zero is None:zero=gate('X',0,0)
            wires[i]=zero
        elif node[0]==1:wires[i]=offsets[node[1]]+(node[2]-1-node[3] if msb_first else node[3])
        else:
            a,ai,b,bi=_xor_sources(nodes,node) if kinds[i]==2 else node[1:]
            a,b=wires[a],wires[b];wires[i]=gate('X' if kinds[i]==2 else 'A',inv(a) if ai else a,inv(b) if bi else b)
    return n,gates,[inv(wires[w]) if flip else wires[w] for w,flip in image['outputs']]
def flat_text(n,gates,outputs):
    return 'EMP_HYBRID_BOOL_V1\n%d %d %d\n'%(n,len(gates),len(outputs))+''.join(('N %d\n'%a) if op=='N' else '%s %d %d\n'%(op,a,b) for op,a,b in gates)+'O '+' '.join(map(str,outputs))+'\n'
def byte_bits(data,msb_first=False):return [(byte>>((7-b) if msb_first else b))&1 for byte in data for b in range(8)]
def evaluate_bytes(gates,outputs,input_bits,msb_first=False):
    wires=list(input_bits)
    for op,a,b in gates:wires.append(1-wires[a] if op=='N' else (wires[a]^wires[b] if op=='X' else wires[a]&wires[b]))
    out=[wires[w] for w in outputs];return bytes(sum(out[8*j+b]<<((7-b) if msb_first else b) for b in range(8)) for j in range(len(out)//8))
