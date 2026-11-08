class ServiceShape:
    def __init__(self,cert,inner,dw,rw,tw,iw):
        if not(1<=cert<=1024 and 1<=inner<=4096 and 1<=dw<=3 and 1<=rw<=10 and 1<=tw<=20 and 1<=iw<=10):
            raise ValueError('invalid private service shape')
        self.cert,self.inner=cert,inner
        self.values=[cert,inner,dw,rw,tw,iw]
        def width(n):return max(1,(n.bit_length()+6)//7)
        def field(n):return 1+width(n)+n
        usmc=4+width(cert)+cert+width(inner)+inner
        wire=92+width(usmc+10)+usmc
        body=132+4*((wire+2)//3)+dw+rw+tw
        request=field(3)+field(61)+field(body)+1+iw+field(30)+field(49)
        self.input_bytes=96+cert+inner+57
        self.boolean_input_bytes=249+cert+inner
        self.output_bytes=1+8+2+field(request)
        self.name='signal_private_sealed_relay_'+'_'.join(map(str,self.values))
        self.descriptor=f'{self.name}-sbv:[{8*self.input_bytes}x1]-sbv:[{8*self.output_bytes}x1]'
