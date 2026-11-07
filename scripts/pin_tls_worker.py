#!/usr/bin/env python3
"""Pin exact exported function descriptors and their schedule/bytecode closure.

Inputs are public compiler outputs. A manifest does not prove MPC security,
Lean/backend equivalence or that a selected program is the intended circuit.
"""
from pathlib import Path
import argparse,hashlib,re

def build(backend,functions,public_files=()):
    selected=set()
    def add(relative):
        path=backend/relative
        if path.is_symlink() or not path.is_file() or path.resolve().parent!=path.parent.resolve():
            raise ValueError('missing or symbolic pinned file: '+relative)
        selected.add(relative);return path.read_bytes()
    for name in functions:
        if not re.fullmatch(r'[a-zA-Z0-9_\-.:\[\]]+',name) or '..' in name:
            raise ValueError('invalid function descriptor name')
        descriptor=add('Programs/Functions/'+name).decode().split()
        if not descriptor or not re.fullmatch(r'[a-zA-Z0-9_.-]+',descriptor[0]) or '..' in descriptor[0]:
            raise ValueError('invalid function program')
        program=descriptor[0]
        schedule=add('Programs/Schedules/'+program+'.sch').decode().split()
        tapes=int(schedule[1])
        if not 1<=tapes<=4096 or len(schedule)<2+tapes:raise ValueError('invalid schedule')
        for token in schedule[2:2+tapes]:
            tape,sep,count=token.partition(':')
            if not sep or not count.isdigit() or not re.fullmatch(r'[a-zA-Z0-9_.-]+',tape) or '..' in tape:
                raise ValueError('invalid bytecode entry')
            add('Programs/Bytecode/'+tape+'.bc')
    for name in public_files:
        if not re.fullmatch(r'Worker-Public/[a-zA-Z0-9_.-]+',name) or '..' in name:
            raise ValueError('public configuration must be in Worker-Public')
        add(name)
    return 'tls-mpc-pinned-files-v1\n'+''.join(hashlib.sha256((backend/name).read_bytes()).hexdigest()+' '+name+'\n' for name in sorted(selected))

def main():
    p=argparse.ArgumentParser();p.add_argument('--backend',type=Path,default=Path('.deps/sharing-refresh/MP-SPDZ'))
    p.add_argument('--function',action='append',required=True);p.add_argument('--public',action='append',default=[]);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();text=build(a.backend.resolve(),a.function,a.public);a.output.write_text(text)
    print(hashlib.sha256(text.encode()).hexdigest())
if __name__=='__main__':main()
