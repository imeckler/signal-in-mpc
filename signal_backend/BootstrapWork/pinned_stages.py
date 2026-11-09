"""Immutable public component closure for private KEM VM composition.

No algorithm input/secret is serialized or opened. The host selects only fixed
public shapes. Source/compiler/backend equivalence remains a separate boundary.
"""
import hashlib,json,pathlib,re
from backend_adapter.boolean import load

class PinnedStages:
    def __init__(self,path):
        self.path=pathlib.Path(path).resolve()
        self.entries=json.loads(self.path.read_text())
        if self.entries.get('format')!='signal-bootstrap-kem-stages-v1':
            raise ValueError('KEM component manifest format')
        if self.entries.get('variant')!='kyber1024':raise ValueError('KEM variant')
        self.table={}
        for item in self.entries['stages']:
            key=tuple(item['key']);relative=pathlib.PurePosixPath(item['path'])
            if key in self.table or relative.is_absolute()or'..'in relative.parts:
                raise ValueError('KEM component path/key')
            if not re.fullmatch(r'[a-z0-9_]+',item['function']):
                raise ValueError('KEM component function')
            if min(item['input_bits'],item['output_bits'])<1:raise ValueError('KEM component dimensions')
            self.table[key]=item

    def image(self,key):
        item=self.table[key];path=self.path.parent/item['path']
        if path.is_symlink()or not path.is_file():raise ValueError('KEM component file')
        if hashlib.sha256(path.read_bytes()).hexdigest()!=item['sha256']:
            raise ValueError('changed KEM component')
        image=load(path)
        if image['input_bits']!=item['input_bits']or len(image['outputs'])!=item['output_bits']:
            raise ValueError('KEM component artifact dimensions')
        return image

    def compiler_executor(self):
        from Compiler.library import export
        from Compiler.GC.types import sbitvec
        from handshake_backend import binary_io
        from backend_adapter.aig_packed import execute_mpc
        Array=sbitvec.get_type(1).Array
        functions={}
        def invoke(key,bits):
            item=self.table[key]
            if len(bits)!=item['input_bits']:raise ValueError('KEM component input dimensions')
            if key not in functions:
                state={'image':self.image(key)}
                def body(inputs,outputs):
                    binary_io.write_bits(outputs,execute_mpc(state['image'],binary_io.read_bits(inputs)))
                body.__name__=item['function']
                functions[key]=(export(body),state)
            function,state=functions[key]
            inputs=Array(item['input_bits']);outputs=Array(item['output_bits'])
            binary_io.write_bits(inputs,bits);function(inputs,outputs)
            # ExportFunction retains compiled public tapes keyed by exact shape.
            # Subsequent calls reuse them; no public DAG needs to remain resident.
            state.clear()
            return binary_io.read_bits(outputs)
        return invoke
