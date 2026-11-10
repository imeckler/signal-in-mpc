"""Same-VM frozen XEdDSA adapter instantiated with checked private conversion.
Public component identities/shapes only select code. No value is reconstructed.
The original frozen mathematical/backend refinement obligations remain explicit.
"""
import hashlib,json,pathlib
from handshake_backend.field_dag import load as load_field
from handshake_backend.mixed import execute_secret,field_to_wire_bits,wire_bits_to_field,wire_bits_to_scalar_fields
from signal_backend.BootstrapWork.pinned_stages import PinnedStages

def flatten(raw):return [bit for byte in raw for bit in byte]
def as_bytes(bits):
 if len(bits)%8:raise ValueError('XEdDSA byte dimensions')
 return [bits[i:i+8]for i in range(0,len(bits),8)]
class PrivateConversions:
 def decode_u(self,raw):return wire_bits_to_field(flatten(raw),mask_high_bit=True)
 def encode_field(self,value):return as_bytes(field_to_wire_bits(value))
 def bits_to_field(self,raw,count):
  from Compiler.GC.types import sbit
  if count<1 or count>256 or len(raw)*8<count:raise ValueError('XEdDSA field-bit dimensions')
  bits=flatten(raw)+[sbit(0)]*(256-len(raw)*8)
  return wire_bits_to_scalar_fields(bits)[:count]
class PrivateStages:
 def __init__(self,path):
  self.path=pathlib.Path(path).resolve();data=json.loads(self.path.read_text())
  if data.get('format')!='signal-bootstrap-xeddsa-v1':raise ValueError('XEdDSA manifest format')
  self.fields={}
  for item in data['fields']:
   key=tuple(item['key']);relative=pathlib.PurePosixPath(item['path'])
   if key in self.fields or relative.is_absolute()or'..'in relative.parts:raise ValueError('XEdDSA field path/key')
   p=self.path.parent/item['path']
   if p.is_symlink()or not p.is_file()or hashlib.sha256(p.read_bytes()).hexdigest()!=item['sha256']:raise ValueError('XEdDSA field identity')
   self.fields[key]=load_field(p)
  if set(self.fields)!={('recover',i)for i in range(3)}|{('signed',i)for i in range(2)}:raise ValueError('XEdDSA field closure')
  registry=PinnedStages(self.path.parent/data['boolean_manifest'],expected_variant='xeddsa-prekey')
  if set(registry.table)!={('xeddsa','binding',128),('xeddsa','hash',97),('xeddsa','hash',1633),('xeddsa','reduce',64),('xeddsa','finish',160)}:raise ValueError('XEdDSA Boolean closure')
  self.runner=registry.compiler_executor()
 def field(self,mode,index,inputs):return execute_secret(self.fields[mode,index],inputs)
 def boolean(self,mode,size,inputs):
  return as_bytes(self.runner(('xeddsa',mode,size),flatten(inputs)))
