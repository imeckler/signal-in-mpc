"""Bounded independent-instance packing; candidate, no default dispatch change.

One VM caller owns the complete batch. No threads, reconstruction, share import,
ratchet commit, TLS sequence allocation, or preprocessing lifetime changes occur
here. The caller must supply independently reserved conversation inputs and keep
all results quarantined until the complete transaction commits.
"""
from itertools import islice
from .aig_packed import plan


def execute_batch(image, input_batches, zero, one, pack, unpack, constant,
                  *, lanes=64, begin_depth=None):
    if type(lanes) is not int or not 1 <= lanes <= 64:
        raise ValueError('packing width must be 1..64')
    count=len(input_batches)
    if not 1 <= count <= 64:
        raise ValueError('public batch size must be 1..64')
    if any(len(values)!=image['input_bits'] for values in input_batches):
        raise ValueError('incorrect batched input dimensions')
    roots,groups=plan(image)
    offsets=[];offset=0
    for width in image['input_widths']:
        offsets.append(offset);offset+=width
    wires=[None]*len(image['nodes'])
    for index in roots:
        node=image['nodes'][index]
        if node[0]==0:wires[index]=[zero]*count
        else:
            _,var,width,bit=node
            wires[index]=[values[offsets[var]+width-1-bit] for values in input_batches]
    previous_depth=None
    for (depth,_,kind),gates in groups:
        if depth!=previous_depth:
            if begin_depth is not None:begin_depth(depth)
            previous_depth=depth
        # No expanded duplicate DAG or whole-group Cartesian-product allocation.
        # Group order guarantees that dependencies belong to earlier groups.
        entries=((index,src,instance) for index,src in gates for instance in range(count))
        while True:
            batch=list(islice(entries,lanes))
            if not batch:break
            lhs=pack([wires[src[0]][instance] for _,src,instance in batch])
            rhs=pack([wires[src[2]][instance] for _,src,instance in batch])
            left_mask=sum(src[1]<<i for i,(_,src,_) in enumerate(batch))
            right_mask=sum(src[3]<<i for i,(_,src,_) in enumerate(batch))
            if left_mask:lhs=lhs^constant(len(batch),left_mask)
            if right_mask:rhs=rhs^constant(len(batch),right_mask)
            value=lhs^rhs if kind==2 else lhs&rhs
            values=unpack(value,len(batch))
            if len(values)!=len(batch):raise ValueError('incorrect batched unpack size')
            for (index,_,instance),value in zip(batch,values):
                if wires[index] is None:wires[index]=[None]*count
                wires[index][instance]=value
    return [[wires[index][instance]^one if inverted else wires[index][instance]
             for index,inverted in image['outputs']] for instance in range(count)]


def execute_mpc_batch(image,input_batches):
    from Compiler.GC.types import sbit,sbits
    from Compiler.program import Program
    if any(not isinstance(value,sbit) or value.n!=1 for values in input_batches for value in values):
        raise TypeError('expected independent single-lane shared input bits')
    return execute_batch(image,input_batches,sbit(0),sbit(1),
        lambda bits:bits[0] if len(bits)==1 else sbits.bit_compose(bits),
        lambda value,size:value.bit_decompose(size),
        lambda size,value:sbits.get_type(size)(value),
        begin_depth=lambda depth:Program.prog.curr_tape.start_new_basicblock(
            name='batch-aig-and-depth-'+str(depth)))
