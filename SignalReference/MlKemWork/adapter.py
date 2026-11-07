"""Staged shared-bit ML-KEM/Kyber composition.

All algorithm inputs/outputs and rejection decisions stay shared. Artifact
selection, variant and dimensions are public. This orchestration is validated
separately; Lean proves each component and the whole mathematical composition.
The executor must validate/pin artifacts and use the same secret Boolean VM.
"""
class MlKem:
    def __init__(self, variant, execute, zero, one):
        if variant not in ('mlkem512','mlkem768','mlkem1024','kyber1024'):
            raise ValueError('variant')
        self.rank = {'mlkem512': 2, 'mlkem768': 3}.get(variant, 4)
        self.eta = 3 if self.rank == 2 else 2
        self.du, self.dv = (11, 5) if self.rank == 4 else (10, 4)
        self.kyber = variant == 'kyber1024'
        self.execute, self.zero, self.one = execute, zero, one

    def public(self, raw):
        return [self.one if value >> i & 1 else self.zero for value in raw for i in range(7, -1, -1)]

    def hash(self, mode, raw, output):
        return self.execute(('hash', mode, len(raw)//8, output), raw)

    def poly(self, mode, *inputs):
        return self.execute(('poly', mode), sum((list(x) for x in inputs), []))

    def ntt(self, mode, *inputs):
        return self.execute(('ntt', mode), sum((list(x) for x in inputs), []))

    def encoding(self, mode, width, raw):
        return self.execute(('encoding', mode, width), raw)

    def noise(self, seed, nonce, eta):
        return self.execute(('noise', eta), list(seed)+self.public(bytes([nonce])))

    def matrix(self, rho, transpose):
        rows, status = [], self.one
        for i in range(self.rank):
            row = []
            for j in range(self.rank):
                indices = bytes([i,j] if transpose else [j,i])
                sampled = self.execute(('matrix', 256, 224), list(rho)+self.public(indices))
                status = status & sampled[0]
                row.append(sampled[8:])
            rows.append(row)
        return status, rows

    def dot(self, left, right):
        out = [self.zero]*4096
        for a,b in zip(left,right):
            out = self.poly('add',out,self.ntt('multiply',a,b))
        return out

    def pke_keygen(self, seed):
        expanded = self.hash('sha3-512',list(seed)+(self.public(bytes([self.rank])) if not self.kyber else []),64)
        rho,sigma = expanded[:256],expanded[256:]
        status,matrix = self.matrix(rho,False)
        secret = [self.ntt('forward',self.noise(sigma,i,self.eta)) for i in range(self.rank)]
        error = [self.ntt('forward',self.noise(sigma,self.rank+i,self.eta)) for i in range(self.rank)]
        public = [self.poly('add',self.dot(row,secret),e) for row,e in zip(matrix,error)]
        sk = sum((self.encoding('encode',12,p) for p in secret),[])
        pk = sum((self.encoding('encode',12,p) for p in public),[])+rho
        return status,sk,pk

    def pke_encrypt(self, pk, message, coins):
        polys = [self.encoding('decode',12,pk[3072*i:3072*(i+1)]) for i in range(self.rank)]
        status,matrix = self.matrix(pk[3072*self.rank:],True)
        ephemeral = [self.ntt('forward',self.noise(coins,i,self.eta)) for i in range(self.rank)]
        error = [self.noise(coins,self.rank+i,2) for i in range(self.rank)]
        error2 = self.noise(coins,2*self.rank,2)
        msg = self.encoding('decompress',1,message)
        u = [self.poly('add',self.ntt('inverse',self.dot(row,ephemeral)),e) for row,e in zip(matrix,error)]
        v = self.poly('add',self.poly('add',self.ntt('inverse',self.dot(polys,ephemeral)),error2),msg)
        return status,sum((self.encoding('compress',self.du,p) for p in u),[])+self.encoding('compress',self.dv,v)

    def pke_decrypt(self, sk, ciphertext):
        secret = [self.encoding('decode',12,sk[3072*i:3072*(i+1)]) for i in range(self.rank)]
        width = 256*self.du
        u = [self.ntt('forward',self.encoding('decompress',self.du,ciphertext[width*i:width*(i+1)])) for i in range(self.rank)]
        v = self.encoding('decompress',self.dv,ciphertext[width*self.rank:])
        return self.encoding('compress',1,self.poly('sub',v,self.ntt('inverse',self.dot(secret,u))))

    def kdf(self, secret, ciphertext):
        return self.hash('shake256',list(secret)+self.hash('sha3-256',ciphertext,32),32) if self.kyber else list(secret)

    def gate(self,status,out):
        return [status]*8+[bit & status for bit in out]

    def keygen(self, seed):
        if len(seed)!=512:raise ValueError('seed64')
        status,sk,pk=self.pke_keygen(seed[:256])
        return self.gate(status,sk+pk+self.hash('sha3-256',pk,32)+list(seed[256:])+pk)

    def encapsulate(self,raw):
        pksize=(384*self.rank+32)*8
        if len(raw)!=pksize+256:raise ValueError('pk,entropy32')
        pk,entropy=raw[:pksize],raw[pksize:]
        message=self.hash('sha3-256',entropy,32) if self.kyber else entropy
        expanded=self.hash('sha3-512',list(message)+self.hash('sha3-256',pk,32),64)
        status,ct=self.pke_encrypt(pk,message,expanded[256:])
        return self.gate(status,ct+self.kdf(expanded[:256],ct))

    def decapsulate(self,raw):
        sksize=(768*self.rank+96)*8
        if len(raw)!=sksize+256*(self.du*self.rank+self.dv):raise ValueError('sk,ciphertext')
        sk,ct=raw[:sksize],raw[sksize:]
        cpasize=3072*self.rank;pksize=(384*self.rank+32)*8
        pk=sk[cpasize:cpasize+pksize]
        public_hash=sk[cpasize+pksize:cpasize+pksize+256]
        z=sk[cpasize+pksize+256:]
        message=self.pke_decrypt(sk[:cpasize],ct)
        expanded=self.hash('sha3-512',message+list(public_hash),64)
        status,expected=self.pke_encrypt(pk,message,expanded[256:])
        equal=self.one
        for left,right in zip(ct,expected):equal=equal & (left ^ right ^ self.one)
        candidate=self.kdf(expanded[:256],ct)
        rejection=self.kdf(self.hash('shake256',list(z)+list(ct),32),ct)
        selected=[(equal & left)^((equal^self.one)&right) for left,right in zip(candidate,rejection)]
        return self.gate(status,selected)
