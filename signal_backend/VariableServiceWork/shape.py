"""Public bounded dimensions only; no canonical varint width selectors."""
class VariableShape:
 def __init__(self,certificate,plaintext,chunk,addresses):
  if not (1<=certificate<=1024 and 0<=plaintext<=1024 and chunk in [0,1] and addresses in [0,1]):raise ValueError('invalid variable conversation dimensions')
  self.values=[certificate,plaintext,chunk,addresses];self.certificate=certificate;self.plaintext=plaintext;self.chunk=chunk;self.addresses=addresses
  self.spqr_bytes=182+34*chunk+plaintext+36*addresses
  self.spqr_offset=32+certificate;self.metadata_offset=self.spqr_offset+self.spqr_bytes
  self.input_bytes=self.metadata_offset+57;self.boolean_input_bytes=self.input_bytes+96
  pq=52 if chunk else 17;cipher=(plaintext//16+1)*16
  self.inner_capacity=cipher+32+36*addresses+pq+64
  width=max(1,(certificate.bit_length()+6)//7)
  cert_field=certificate+width+1;usmc=2+cert_field+self.inner_capacity+4
  sealed=81+usmc+10+4
  self.frame_capacity=4*((sealed+2)//3)+256+256+4+2+8
  if self.frame_capacity>16384:raise ValueError('conversation payload exceeds private TLS bound')
  self.output_bytes=83+self.frame_capacity
  self.name='signal_private_variable_conversation_'+'_'.join(map(str,self.values))
  self.descriptor=f'{self.name}-sbv:[{8*self.input_bytes}x1]-sbv:[{8*self.output_bytes}x1]'
