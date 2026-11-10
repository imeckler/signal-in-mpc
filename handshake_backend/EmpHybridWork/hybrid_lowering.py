"""Shared lowering of Lean bit-vector circuit exports to the flat gate format.

Unverified adapter boundary. Besides DAG traversal and the XOR recognition of
`backend_adapter.aig`, this module recognises the full-adder carry that the
bit-vector compiler emits as three AND nodes,

    carry = (a AND b) OR (c AND (a XOR b))        [stored as NOT(carry)]

and emits the equivalent one-AND form  a XOR ((a XOR b) AND (a XOR c)).
Additions dominate SHA-256, so this roughly halves hash-heavy circuits.
`circuit_cache.py` checks every export by evaluating it with and without this
rewrite on random inputs.

Bit order: variable v, bit b (weight 2^b) is wire offset(v)+b; outputs are
taken in the order the Lean emitter lists them (bit b of output byte j at 8*j+b).
"""
import pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from backend_adapter.aig import validate,_xor_sources
def _carry_sources(nodes,node):
    """For node = AND(NOT P, NOT Q) with P = AND(a', b') and Q = AND(c', x') where x' is
    the literal a' XOR b': return (a, a_inverted, x, x_inverted, c, c_inverted)."""
    if node[0]!=2 or node[2]!=1 or node[4]!=1:return None
    for p,q in ((node[1],node[3]),(node[3],node[1])):
        P,Q=nodes[p],nodes[q]
        if P[0]!=2 or Q[0]!=2:continue
        _,pa,pai,pb,pbi=P
        if pa==pb:continue
        for x,xi,c,ci in ((Q[1],Q[2],Q[3],Q[4]),(Q[3],Q[4],Q[1],Q[2])):
            source=_xor_sources(nodes,nodes[x])
            if source is None:continue
            xa,xai,xb,xbi=source
            if {xa,xb}=={pa,pb} and (xai^xbi^xi)==(pai^pbi):return pa,pai,x,xi,c,ci
    return None
def _plan(nodes,outputs,majority):
    # 0: unreachable, 1: AND node, 2: XOR replacing an AND pattern, 3: one-AND carry.
    kinds=bytearray(len(nodes));pending=[wire for wire,_ in outputs]
    while pending:
        index=pending.pop()
        if kinds[index]:continue
        node=nodes[index];sources=_xor_sources(nodes,node)
        if sources is not None:kinds[index]=2;pending.extend((sources[0],sources[2]));continue
        carry=_carry_sources(nodes,node) if majority else None
        if carry is not None:kinds[index]=3;pending.extend((carry[0],carry[2],carry[4]));continue
        kinds[index]=1
        if node[0]==2:pending.extend((node[1],node[3]))
    return kinds
def lower(image,msb_first=False,majority=True):
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
    nodes=image['nodes'];kinds=_plan(nodes,image['outputs'],majority);wires={}
    lit=lambda index,flip:inv(wires[index]) if flip else wires[index]
    for i,node in enumerate(nodes):
        if not kinds[i]:continue
        if node==[0]:
            if zero is None:zero=gate('X',0,0)
            wires[i]=zero
        elif node[0]==1:wires[i]=offsets[node[1]]+(node[2]-1-node[3] if msb_first else node[3])
        elif kinds[i]==3:
            a,ai,x,xi,c,ci=_carry_sources(nodes,node);first=lit(a,ai)
            wires[i]=inv(gate('X',first,gate('A',lit(x,xi),gate('X',first,lit(c,ci)))))   # node stores NOT(carry)
        else:
            a,ai,b,bi=_xor_sources(nodes,node) if kinds[i]==2 else node[1:]
            wires[i]=gate('X' if kinds[i]==2 else 'A',lit(a,ai),lit(b,bi))
    return n,gates,[inv(wires[w]) if flip else wires[w] for w,flip in image['outputs']]
def flat_text(n,gates,outputs):
    return 'EMP_HYBRID_BOOL_V1\n%d %d %d\n'%(n,len(gates),len(outputs))+''.join(('N %d\n'%a) if op=='N' else '%s %d %d\n'%(op,a,b) for op,a,b in gates)+'O '+' '.join(map(str,outputs))+'\n'
def byte_bits(data,msb_first=False):return [(byte>>((7-b) if msb_first else b))&1 for byte in data for b in range(8)]
def evaluate_bits(gates,outputs,input_bits):
    wires=list(input_bits)
    for op,a,b in gates:wires.append(1-wires[a] if op=='N' else (wires[a]^wires[b] if op=='X' else wires[a]&wires[b]))
    return [wires[w] for w in outputs]
def evaluate_bytes(gates,outputs,input_bits,msb_first=False):
    out=evaluate_bits(gates,outputs,input_bits);return bytes(sum(out[8*j+b]<<((7-b) if msb_first else b) for b in range(8)) for j in range(len(out)//8))
