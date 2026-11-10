"""Fixed private bit-gate profile. Signature callback is bound by the compiler,
never supplied through the native/worker API. Only public dimensions branch.
"""
def flatten(raw):return [bit for byte in raw for bit in byte]
def canonical_pair(b0,b1,b2,one):
    def all_bits(values):
        values=list(values)
        if not values:return one
        while len(values)>1:values=[values[i]&values[i+1]if i+1<len(values)else values[i]for i in range(0,len(values),2)]
        return values[0]
    def equal_byte(byte,value):return all_bits(bit if(value>>(7-i))&1 else bit^one for i,bit in enumerate(byte))
    def either(a,b):return a^b^(a&b)
    low_ok=(b1[4]&b1[5]&either(b1[6],b1[7]))^one
    high_ok=(b2[0]&b2[1]&either(b2[2],b2[3]))^one
    exact_low=all_bits([b1[4],b1[5],b1[6]^one,b1[7],equal_byte(b0,0)])
    exact_high=equal_byte(b2,208)&all_bits(bit^one for bit in b1[:4])
    return either(low_ok,exact_low),either(high_ok,exact_high)
def validate_profile(raw,verify_signature,one):
    if len(raw)!=1857 or any(len(byte)!=8 for byte in raw):raise ValueError('prekey profile dimensions')
    def all_bits(values):
        values=list(values)
        if not values:return one
        while len(values)>1:
            values=[values[i]&values[i+1]if i+1<len(values)else values[i]for i in range(0,len(values),2)]
        return values[0]
    def equal_byte(byte,value):return all_bits(bit if(value>>(7-i))&1 else bit^one for i,bit in enumerate(byte))
    def same(left,right):return all_bits(a^b^one for a,b in zip(flatten(left),flatten(right)))
    def either(a,b):return a^b^(a&b)
    trusted=raw[:33];identity=raw[33:66];signed=raw[66:99];ec_signature=raw[99:163]
    pq=raw[163:1732];pq_signature=raw[1732:1796];otp=raw[1796:1829]
    metadata=raw[1829:1846];flags=raw[1846:1857]
    ec=verify_signature(identity[1:],ec_signature,signed)
    kem=verify_signature(identity[1:],pq_signature,pq)
    canonical=[]
    # Conservative canonical-coefficient profile (<3329); this is a range
    # check, NOT proof that a remote key was honestly generated. rho is32B.
    for i in range(512):
        b0,b1,b2=pq[1+3*i:4+3*i]
        canonical.extend(canonical_pair(b0,b1,b2,one))
    device=metadata[4]
    accepted=all_bits([same(trusted,identity),equal_byte(trusted[0],5),equal_byte(identity[0],5),
        equal_byte(signed[0],5),equal_byte(otp[0],5),equal_byte(pq[0],8),
        device[0]^one,equal_byte(device,0)^one]+canonical+
        [equal_byte(flag,1)for flag in flags]+flatten(ec)+flatten(kem))
    return accepted
