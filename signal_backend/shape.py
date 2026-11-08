"""Public dimensions matching SendShape.h and the Lean SPQR send exporter."""
class SendShape:
    def __init__(self, arguments):
        mode, *values = arguments
        if mode != 'signal-spqr-send' or len(values) != 8:
            raise ValueError('expected bounded established Signal send profile')
        if any(not str(x).isascii() or not str(x).isdecimal() for x in values[:6]):
            raise ValueError('expected public decimal dimensions')
        self.size, cw, pw, ew, iw, kw = map(int, values[:6])
        chunk, addresses = values[6:]
        if chunk not in ('present', 'none') or addresses not in ('present', 'none'):
            raise ValueError('invalid presence profile')
        self.chunk = chunk == 'present'
        self.addresses = addresses == 'present'
        if not (0 <= self.size <= 1024 and 1 <= cw <= 5 and 1 <= pw <= 5
                and 1 <= ew <= 10 and 1 <= iw <= 5 and
                (1 <= kw <= 3 if self.chunk else kw == 0)):
            raise ValueError('invalid Signal send dimensions')
        self.arguments = [mode, *map(str, (self.size, cw, pw, ew, iw, kw)), chunk, addresses]
        self.stem = '-'.join(self.arguments)
        self.chunk_bytes = 34 if self.chunk else 0
        self.input_bytes = 182 + self.chunk_bytes + self.size + (36 if self.addresses else 0)
        ciphertext = 16 * (self.size // 16 + 1)
        pq = 2 + ew + iw + (kw + 32 if self.chunk else 0)
        def width(n):
            return max(1, (n.bit_length() + 6) // 7)
        self.wire_bytes = (1 + 35 + 1 + cw + 1 + pw + 1 + width(ciphertext) + ciphertext
                           + 1 + width(pq) + pq + (38 if self.addresses else 0) + 8)
        self.output_bytes = 73 + self.wire_bytes
        self.function_name = 'signal_binary_' + self.stem.replace('-', '_')
        self.descriptor = (f'{self.function_name}-sbv:[{self.input_bytes*8}x1]'
                           f'-sbv:[{self.output_bytes*8}x1]')
