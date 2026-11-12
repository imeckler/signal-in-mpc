"""Tiny multivariate polynomial arithmetic over Z (dict monomial -> coefficient) for the H-GROUP
cofactor search. No external library. Monomials are tuples of exponents over VARS."""

VARS = ['d', 'x1', 'y1', 'x2', 'y2', 'x3', 'y3']
IDX = {v: i for i, v in enumerate(VARS)}
NV = len(VARS)


class P:
    __slots__ = ('t',)

    def __init__(self, t=None):
        self.t = {m: c for m, c in (t or {}).items() if c != 0}

    @staticmethod
    def const(c):
        return P({(0,) * NV: c})

    @staticmethod
    def var(name):
        m = [0] * NV
        m[IDX[name]] = 1
        return P({tuple(m): 1})

    def _co(self, o):
        return o if isinstance(o, P) else P.const(o)

    def __add__(self, o):
        o = self._co(o)
        t = dict(self.t)
        for m, c in o.t.items():
            t[m] = t.get(m, 0) + c
        return P(t)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.t.items()})

    def __sub__(self, o):
        return self + (-self._co(o))

    def __rsub__(self, o):
        return self._co(o) - self

    def __mul__(self, o):
        o = self._co(o)
        t = {}
        for m1, c1 in self.t.items():
            for m2, c2 in o.t.items():
                m = tuple(a + b for a, b in zip(m1, m2))
                t[m] = t.get(m, 0) + c1 * c2
        return P(t)

    __rmul__ = __mul__

    def __pow__(self, n):
        r = P.const(1)
        for _ in range(n):
            r = r * self
        return r

    def is_zero(self):
        return not self.t

    def __len__(self):
        return len(self.t)

    def lean(self, width=100):
        if not self.t:
            return '0'
        parts = []
        for m in sorted(self.t, reverse=True):
            c = self.t[m]
            fs = []
            for v, e in zip(VARS, m):
                if e == 1:
                    fs.append(v)
                elif e > 1:
                    fs.append(f'{v}^{e}')
            a = abs(c)
            if not fs:
                body = str(a)
            elif a == 1:
                body = ' * '.join(fs)
            else:
                body = ' * '.join([str(a)] + fs)
            parts.append(('-' if c < 0 else '+', body))
        out, line = [], ''
        for i, (s, b) in enumerate(parts):
            piece = (('-' if s == '-' else '') + b) if i == 0 else f' {s} {b}'
            if len(line) + len(piece) > width and line:
                out.append(line)
                line = '     ' + piece
            else:
                line += piece
        out.append(line)
        return '\n'.join(out)


def V(*names):
    return [P.var(n) for n in names]


def curve(i):
    """H_i = 1 + d x_i^2 y_i^2 + x_i^2 - y_i^2  (zero on the curve -x^2 + y^2 = 1 + d x^2 y^2)."""
    d, x, y = P.var('d'), P.var(f'x{i}'), P.var(f'y{i}')
    return 1 + d * x * x * y * y + x * x - y * y


def reduce(N, pts=(1, 2, 3), order=None):
    """Rewrite d x_i^2 y_i^2 -> y_i^2 - x_i^2 - 1. Returns (cofactors {i: P}, remainder) with
    N = sum_i cof[i] * H_i + remainder."""
    cof = {i: {} for i in pts}
    work = dict(N.t)
    rem = {}
    di = IDX['d']
    pts = list(order or pts)
    while work:
        m, c = work.popitem()
        if c == 0:
            continue
        done = False
        if m[di] >= 1:
            for i in pts:
                xi, yi = IDX[f'x{i}'], IDX[f'y{i}']
                if m[xi] >= 2 and m[yi] >= 2:
                    q = list(m)
                    q[di] -= 1
                    q[xi] -= 2
                    q[yi] -= 2
                    q = tuple(q)
                    cof[i][q] = cof[i].get(q, 0) + c
                    # c*q*(d x^2 y^2) = c*q*H - c*q*(1 + x^2 - y^2)
                    for dm, dc in (((0, 0), -c), ((2, 0), -c), ((0, 2), c)):
                        n = list(q)
                        n[xi] += dm[0]
                        n[yi] += dm[1]
                        n = tuple(n)
                        work[n] = work.get(n, 0) + dc
                    done = True
                    break
        if not done:
            rem[m] = rem.get(m, 0) + c
    return {i: P(t) for i, t in cof.items()}, P(rem)


def check(N, cof, rem=None):
    s = P()
    for i, c in cof.items():
        s = s + c * curve(i)
    if rem is not None:
        s = s + rem
    return (N - s).is_zero()


def best_reduce(N, pts=(1, 2, 3), maxk=6):
    """Try all point orders and powers d^k; return (k, cof, order) with zero remainder, or None."""
    import itertools
    d = P.var('d')
    for k in range(maxk + 1):
        M = N * d ** k
        for order in itertools.permutations(pts):
            cof, rem = reduce(M, pts, order)
            if rem.is_zero():
                assert check(M, cof)
                return k, cof, order
    return None
