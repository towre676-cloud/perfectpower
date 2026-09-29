"""Exact characteristic-zero squarefree decomposition; coefficients ascend.

This executable is independently tested. It is NOT extracted from Lean, and
its output is not itself a pp-cert/1 completeness certificate.
"""
from fractions import Fraction as Q
from dataclasses import dataclass


def poly(xs):
    xs = list(map(Q, xs))
    while xs and xs[-1] == 0:
        xs.pop()
    return tuple(xs)


ZERO, ONE = (), (Q(1),)


def add(a, b):
    return poly((a[i] if i < len(a) else 0) +
                (b[i] if i < len(b) else 0) for i in range(max(len(a), len(b))))


def scale(a, c):
    return poly(x * c for x in a)


def mul(a, b):
    if not a or not b:
        return ZERO
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return poly(out)


def power(a, n):
    if n < 0:
        raise ValueError('negative polynomial exponent')
    out = ONE
    while n:
        if n % 2:
            out = mul(out, a)
        a = mul(a, a)
        n //= 2
    return out


def divmod_poly(a, b):
    if not b:
        raise ZeroDivisionError('zero polynomial divisor')
    r = poly(a)
    q = [Q(0)] * max(0, len(r) - len(b) + 1)
    while r and len(r) >= len(b):
        j, c = len(r) - len(b), r[-1] / b[-1]
        q[j] += c
        r = add(r, (Q(0),) * j + scale(b, -c))
    return poly(q), r


def divide(a, b):
    q, r = divmod_poly(a, b)
    if r:
        raise ValueError('division was not exact')
    return q


def monic(a):
    return scale(a, 1 / a[-1]) if a else ZERO


def gcd(a, b):
    while b:
        a, b = b, divmod_poly(a, b)[1]
    return monic(a)


def derivative(a):
    return poly(i * a[i] for i in range(1, len(a)))


def evaluate(a, x):
    out = Q(0)
    for c in reversed(a):
        out = out * x + c
    return out


@dataclass(frozen=True)
class Decomposition:
    lead: Q
    layers: tuple  # (positive multiplicity, monic squarefree polynomial)

    def reconstruct(self):
        out = (self.lead,)
        for j, f in self.layers:
            out = mul(out, power(f, j))
        return out

    def split(self, d):
        if d < 2:
            raise ValueError('counting applications require d >= 2')
        g, r = ONE, ONE
        for j, f in self.layers:
            g = mul(g, power(f, j // d))
            r = mul(r, power(f, j % d))
        return g, r

    def bad_degree(self, d):
        if d < 2:
            raise ValueError('d >= 2 required')
        return sum(len(f) - 1 for j, f in self.layers if j % d)

    def verify(self, original):
        assert self.lead != 0
        assert self.reconstruct() == poly(original)
        seen = set()
        for j, f in self.layers:
            assert j > 0 and j not in seen and f != ONE and f[-1] == 1
            seen.add(j)
            assert gcd(f, derivative(f)) == ONE
        for i, (_, f) in enumerate(self.layers):
            for _, g in self.layers[i + 1:]:
                assert gcd(f, g) == ONE
        assert sum(j * (len(f) - 1) for j, f in self.layers) == len(poly(original)) - 1
        return True


def yun(original):
    f = poly(original)
    if not f:
        raise ValueError('zero polynomial has no finite squarefree decomposition')
    lead, f = f[-1], monic(f)
    c = gcd(f, derivative(f))
    w, j, layers = divide(f, c), 1, []
    while w != ONE:
        y = gcd(w, c)
        z = divide(w, y)
        if z != ONE:
            layers.append((j, z))
        w, c, j = y, divide(c, y), j + 1
    result = Decomposition(lead, tuple(layers))
    result.verify(original)
    return result


def integer_root(a, d):
    """Return the signed exact root, or None; no floating-point approximation."""
    if d < 2:
        raise ValueError('d >= 2 required')
    if a < 0:
        return None if d % 2 == 0 else (lambda r: None if r is None else -r)(integer_root(-a, d))
    lo, hi = 0, 1 << ((a.bit_length() + d - 1) // d)
    while lo <= hi:
        mid = (lo + hi) // 2
        v = mid ** d
        if v == a:
            return mid
        if v < a:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


def rational_power(q, d):
    q = Q(q)
    return integer_root(q.numerator, d) is not None and integer_root(q.denominator, d) is not None
