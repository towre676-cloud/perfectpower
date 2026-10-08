"""Richelot splittings of genus-two curves, including the singular (delta=0) case.

A quadratic splitting y^2=G1 G2 G3 is read projectively: G=(c0,c1,c2) is the
binary form c0 z^2+c1 xz+c2 x^2, so c2=0 puts a root at infinity.  When the
Richelot determinant vanishes the target is not a Jacobian: the three forms
lie in a pencil, the pencil contains two squares l1^2, l2^2 (defined over Q or
a quadratic field), and C has the involution l1/l2 -> -l1/l2 with elliptic
quotients E1, E2.  Every identity below is exact; the point counts are the
independent isogeny-invariant replay (L-polynomials at good primes).
"""
from fractions import Fraction as Q
from math import isqrt, gcd


# ---------------------------------------------------------------- Q(sqrt D)
def squarefree_part(n):
    n = Q(n)
    if n == 0:
        raise ValueError('nonzero value required')
    s = 1 if n > 0 else -1
    a = abs(n.numerator) * n.denominator
    d, out = 2, 1
    while d * d <= a:
        while a % (d * d) == 0:
            a //= d * d
        if a % d == 0:
            out *= d
            a //= d
        d += 1
    return s * out * a


class K:
    """a+b*sqrt(D), D squarefree integer (D=1: rationals)."""
    __slots__ = ('a', 'b', 'D')

    def __init__(self, a, b=0, D=1):
        self.a, self.b, self.D = Q(a), Q(b), D
        if D == 1:
            self.a, self.b = self.a + self.b, Q(0)

    def _c(self, o):
        return o if isinstance(o, K) else K(o, 0, self.D)

    def __add__(self, o):
        o = self._c(o)
        return K(self.a + o.a, self.b + o.b, self.D)
    __radd__ = __add__

    def __neg__(self):
        return K(-self.a, -self.b, self.D)

    def __sub__(self, o):
        return self + (-self._c(o))

    def __rsub__(self, o):
        return self._c(o) - self

    def __mul__(self, o):
        o = self._c(o)
        return K(self.a * o.a + self.D * self.b * o.b, self.a * o.b + self.b * o.a, self.D)
    __rmul__ = __mul__

    def conj(self):
        return K(self.a, -self.b, self.D)

    def norm(self):
        return self.a * self.a - self.D * self.b * self.b

    def inv(self):
        n = self.norm()
        if not n:
            raise ZeroDivisionError('zero in Q(sqrt D)')
        return K(self.a / n, -self.b / n, self.D)

    def __truediv__(self, o):
        return self * self._c(o).inv()

    def __rtruediv__(self, o):
        return self._c(o) * self.inv()

    def __eq__(self, o):
        o = self._c(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def __bool__(self):
        return bool(self.a or self.b)

    def __repr__(self):
        return str(self.a) if not self.b else '%s+(%s)*sqrt(%d)' % (self.a, self.b, self.D)

    def packet(self):
        return [str(self.a), str(self.b)] if self.D != 1 else str(self.a)


# --------------------------------------------------- polynomials (low first)
def ptrim(p):
    p = list(p)
    while p and not p[-1]:
        p.pop()
    return p


def padd(p, q):
    n = max(len(p), len(q))
    z = (p or q)[0] * 0 if (p or q) else 0
    return ptrim([(p[i] if i < len(p) else z) + (q[i] if i < len(q) else z) for i in range(n)])


def pmul(p, q):
    if not p or not q:
        return []
    out = [p[0] * 0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] = out[i + j] + a * b
    return ptrim(out)


def pscale(p, c):
    return ptrim([a * c for a in p])


def pder(p):
    return ptrim([i * p[i] for i in range(1, len(p))])


def form(p, degree):
    """Binary form of the given degree from a low-first list (pads zeros)."""
    p = list(p)
    if len(ptrim(p)) > degree + 1:
        raise ValueError('degree exceeds form degree')
    z = p[0] * 0 if p else Q(0)
    return (p + [z] * (degree + 1 - len(p)))[:degree + 1]


def fmul(f, g):
    out = [f[0] * 0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] = out[i + j] + a * b
    return out


# ------------------------------------------------------------- finite fields
def is_prime(p):
    return type(p) is int and p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def legendre(a, p):
    a %= p
    if not a:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def sqrt_mod(a, p):
    a %= p
    for x in range(p):
        if x * x % p == a:
            return x
    raise ValueError('nonresidue')


class Fq:
    """F_p (n=None) or F_p[s]/(s^2-n) with n a nonresidue; elements (u,v)."""

    def __init__(self, p, quadratic=False):
        self.p = p
        self.n = next(a for a in range(2, p) if legendre(a, p) == -1) if quadratic else None
        self.q = p * p if quadratic else p
        self.elements = [(u, v) for u in range(p) for v in range(p if quadratic else 1)]
        # quadratic character via norm: chi(x)=legendre(N(x)) on F_{p^2}
    def add(self, x, y):
        return ((x[0] + y[0]) % self.p, (x[1] + y[1]) % self.p)

    def mul(self, x, y):
        p, n = self.p, self.n or 0
        return ((x[0] * y[0] + n * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)

    def chi(self, x):
        if self.n is None:
            return legendre(x[0], self.p)
        return legendre(x[0] * x[0] - self.n * x[1] * x[1], self.p)

    def rational(self, r):
        r = Q(r)
        if r.denominator % self.p == 0:
            raise ArithmeticError('nonintegral reduction')
        return (r.numerator * pow(r.denominator, -1, self.p) % self.p, 0)

    def sqrt_of(self, d):
        """An element s with s^2=d (d an integer)."""
        d %= self.p
        if legendre(d, self.p) >= 0:
            return (sqrt_mod(d, self.p), 0)
        if self.n is None:
            raise ValueError('no square root in F_p')
        return (0, sqrt_mod(d * pow(self.n, -1, self.p), self.p))


def count_double_cover(F, field, coefficient_map):
    """#{(P,Y)} on the smooth model of Y^2=F(X,Z), F an even-degree binary form."""
    coeffs = [coefficient_map(c) for c in F]
    total = 0
    one = (1, 0)
    for x in field.elements:
        v, pw = (0, 0), one
        for c in coeffs:
            v = field.add(v, field.mul(c, pw))
            pw = field.mul(pw, x)
        total += 1 + field.chi(v)
    return total + 1 + field.chi(coeffs[-1])


def lpoly_from_counts(N1, N2, p, g):
    """Numerator of zeta from N_1..N_g (g<=2), returned low-first."""
    s1 = p + 1 - N1
    if g == 1:
        return [1, -s1, p]
    p2 = s1 * s1 - (p * p + 1 - N2)  # = 2 e2
    if p2 % 2:
        raise AssertionError('non-integral second symmetric function')
    e2 = p2 // 2
    return [1, -s1, e2, -p * s1, p * p]


def reduce_mod_p(poly, p):
    out = []
    for c in poly:
        c = Q(c)
        if c.denominator % p == 0:
            return None
        out.append(c.numerator * pow(c.denominator, -1, p) % p)
    return out


def _pmod_trim(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return a


def _pmod_rem(a, b, p):
    a, b = _pmod_trim(a), _pmod_trim(b)
    inv = pow(b[-1], -1, p)
    while len(a) >= len(b):
        f = a[-1] * inv % p
        sh = len(a) - len(b)
        for i, c in enumerate(b):
            a[sh + i] = (a[sh + i] - f * c) % p
        a = _pmod_trim(a)
    return a


def form_squarefree_mod_p(F, p):
    """Binary form F (low-first coefficients of x) squarefree of full degree in P^1(F_p-bar)."""
    f = reduce_mod_p(F, p)
    if f is None:
        return False
    d = len(F) - 1
    f = _pmod_trim(f)
    if len(f) - 1 < d - 1:
        return False  # double root at infinity
    df = _pmod_trim([(i * f[i]) % p for i in range(1, len(f))])
    if not df:
        return False
    a, b = f, df
    while b:
        a, b = b, _pmod_rem(a, b, p)
    return len(a) == 1


# ------------------------------------------------------------- Richelot data
def _parse_forms(factors):
    if len(factors) != 3 or any(len(v) != 3 for v in factors):
        raise ValueError('three binary quadratic forms (c0,c1,c2) required')
    return [[Q(c) for c in v] for v in factors]


def det3(m):
    return (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))


def sextic_form(G):
    return fmul(fmul(G[0], G[1]), G[2])


def binary_squarefree(F):
    """Exact squarefreeness of a binary form over Q (incl. the root at infinity)."""
    f = ptrim(F)
    d = len(F) - 1
    if len(f) - 1 < d - 1:
        return False
    df = pder(f)
    a, b = f, df
    while b:
        a, b = b, _qrem(a, b)
    return len(a) == 1


def _qrem(a, b):
    a, b = ptrim(a), ptrim(b)
    while len(a) >= len(b) and a:
        f = a[-1] / b[-1]
        sh = len(a) - len(b)
        a = ptrim([a[i] - f * b[i - sh] if i >= sh else a[i] for i in range(len(a))])
    return a


def bracket(F, G):
    """Affine bracket F'G-FG' of binary quadratics: half the Jacobian covariant."""
    return form(padd(pmul(pder(ptrim(F)), ptrim(G)), pscale(pmul(ptrim(F), pder(ptrim(G))), -1)), 2)


def smooth_richelot_target(factors):
    """Nonzero determinant: the classical genus-two Richelot target (binary sextic)."""
    G = _parse_forms(factors)
    delta = det3(G)
    if not delta:
        raise ValueError('determinant zero: use singular_richelot')
    H = [bracket(G[(i + 1) % 3], G[(i + 2) % 3]) for i in range(3)]
    target = [c / delta for c in sextic_form(H)]
    return dict(delta=delta, brackets=H, target=target)


def singular_richelot(factors):
    """delta=0: explicit (2,2)-splitting J(C) ~ E1 x E2 (or Res_{Q(sqrt D)/Q} E1)."""
    G = _parse_forms(factors)
    F = sextic_form(G)
    if not binary_squarefree(F):
        raise ValueError('source sextic form is not squarefree: not a genus-two curve')
    delta = det3(G)
    if delta:
        raise ValueError('nonzero Richelot determinant: target is a genus-two Jacobian')
    # A basis P,R of the pencil spanned by the three forms.
    P = G[0]
    R = next((g for g in G[1:] if any(P[i] * g[j] - P[j] * g[i] for i in range(3) for j in range(3))), None)
    if R is None:
        raise AssertionError('pencil of rank one forces common roots')
    # disc(lam P + mu R) = A lam^2 + B lam mu + C mu^2
    A = P[1] ** 2 - 4 * P[0] * P[2]
    C = R[1] ** 2 - 4 * R[0] * R[2]
    B = 2 * P[1] * R[1] - 4 * (P[0] * R[2] + P[2] * R[0])
    disc = B * B - 4 * A * C
    if not disc:
        raise AssertionError('pencil discriminant is a square: squares coincide, forcing a common root')
    D = squarefree_part(disc)
    m2 = disc / D
    m = Q(isqrt(m2.numerator), isqrt(m2.denominator))
    if m * m != m2:
        raise AssertionError('pencil square root failed')
    sq = K(m, 0, D) if D == 1 else K(0, m, D)
    if A:
        params = [((-B + s * sq) / (2 * A), K(1, 0, D)) for s in (1, -1)]
    else:
        params = [(K(1, 0, D), K(0, 0, D)), (K(-C, 0, D), K(B, 0, D))]
    squares = []
    for lam, mu in params:
        M = [lam * P[i] + mu * R[i] for i in range(3)]
        if M[1] * M[1] - 4 * M[0] * M[2]:
            raise AssertionError('pencil member is not a square')
        if M[2]:
            kappa, lin = M[2], [M[1] / (2 * M[2]), K(1, 0, D)]
        else:
            kappa, lin = M[0], [K(1, 0, D), K(0, 0, D)]
        if [kappa * lin[0] * lin[0], 2 * kappa * lin[0] * lin[1], kappa * lin[1] * lin[1]] != M:
            raise AssertionError('square factorization failed')
        squares.append((M, kappa, lin))
    (M1, k1, l1), (M2, k2, l2) = squares
    W = l1[1] * l2[0] - l1[0] * l2[1]  # l1' l2 - l1 l2'
    if not W:
        raise AssertionError('linear forms proportional')
    coeffs = []
    for g in G:
        gk = [K(c, 0, D) for c in g]
        sol = None
        for i, j in ((0, 1), (0, 2), (1, 2)):
            dd = M1[i] * M2[j] - M1[j] * M2[i]
            if dd:
                al = (gk[i] * M2[j] - gk[j] * M2[i]) / dd
                be = (M1[i] * gk[j] - M1[j] * gk[i]) / dd
                sol = (al, be)
                break
        al, be = sol
        if any(al * M1[k] + be * M2[k] != gk[k] for k in range(3)):
            raise AssertionError('form not in the pencil')
        coeffs.append((al * k1, be * k2))  # G = a l1^2 + b l2^2
    a = [c[0] for c in coeffs]
    b = [c[1] for c in coeffs]
    if not all(a) or not all(b):
        raise AssertionError('a factor is a square, contradicting squarefreeness')
    # exact identities over Q(sqrt D)[x], as binary forms of degree 2 and 6
    L1 = [l1[0], l1[1]]
    L2 = [l2[0], l2[1]]
    sq1 = [L1[0] * L1[0], 2 * L1[0] * L1[1], L1[1] * L1[1]]
    sq2 = [L2[0] * L2[0], 2 * L2[0] * L2[1], L2[1] * L2[1]]
    for g, ai, bi in zip(G, a, b):
        if [ai * u + bi * v for u, v in zip(sq1, sq2)] != [K(c, 0, D) for c in g]:
            raise AssertionError('pencil decomposition identity failed')
    E1 = [K(1, 0, D)]
    E2 = [K(1, 0, D)]
    for ai, bi in zip(a, b):
        E1 = pmul(E1, [bi, ai])   # prod(a_i X + b_i)
        E2 = pmul(E2, [ai, bi])   # prod(a_i + b_i X)
    E1, E2 = form(E1, 3), form(E2, 3)
    # pullback of the cubic through X=l1^2/l2^2 times l2^6 equals the sextic
    pulled = [K(0, 0, D)] * 7
    pulled2 = [K(0, 0, D)] * 7
    for k in range(4):
        term = fmul(fmul(_fpow(sq1, k), _fpow(sq2, 3 - k)), [E1[k]])
        pulled = [u + v for u, v in zip(pulled, term)]
        term2 = fmul(fmul(_fpow(sq2, k), _fpow(sq1, 3 - k)), [E2[k]])
        pulled2 = [u + v for u, v in zip(pulled2, term2)]
    if pulled != [K(c, 0, D) for c in F] or pulled2 != [K(c, 0, D) for c in F]:
        raise AssertionError('elliptic quotient map identity failed')
    # differentials: d(l1^2/l2^2) l2^4 = 2W l1 l2 dx, so phi1^*(dX/Y)=2W l1 dx/y, phi2^*=-2W l2 dx/y
    lhs = padd(pmul(pder(pmul(L1, L1)), pmul(L2, L2)), pscale(pmul(pmul(L1, L1), pder(pmul(L2, L2))), -1))
    if ptrim(lhs) != ptrim(pscale(pmul(L1, L2), 2 * W)):
        raise AssertionError('differential pullback identity failed')
    pull = [[2 * W * L1[0], 2 * W * L1[1]], [-2 * W * L2[0], -2 * W * L2[1]]]
    if not (pull[0][0] * pull[1][1] - pull[0][1] * pull[1][0]):
        raise AssertionError('pullback differentials dependent')
    conj_ok = None
    if D != 1:
        conj_ok = all(x.conj() == y for x, y in zip(E1, E2))
        if not conj_ok:
            raise AssertionError('E2 is not the Galois conjugate of E1')
    two_torsion = [dict(factor=i + 1, E1_x=(-b[i] / a[i]).packet(), E2_x=(-a[i] / b[i]).packet()) for i in range(3)]
    return dict(schema='pp-singular-richelot/1', factors=[[str(c) for c in g] for g in G], determinant='0',
                sextic_form=[str(c) for c in F], pencil_discriminant=str(disc), field_D=D,
                squares=[dict(member=[c.packet() for c in M], kappa=k.packet(), linear_form=[c.packet() for c in l])
                         for M, k, l in squares],
                wronskian=W.packet(), a=[x.packet() for x in a], b=[x.packet() for x in b],
                E1_cubic=[c.packet() for c in E1], E2_cubic=[c.packet() for c in E2],
                maps=dict(phi1='X=l1^2/l2^2, Y=y/l2^3 onto E1: Y^2=prod(a_i X+b_i)',
                          phi2='X=l2^2/l1^2, Y=y/l1^3 onto E2: Y^2=prod(a_i+b_i X)',
                          involution='l1/l2 -> -l1/l2 (fixes both quotient maps)'),
                differential_pullbacks=[[c.packet() for c in row] for row in pull],
                gluing=dict(two_torsion=two_torsion,
                            psi='E1[2] -> E2[2], (-b_i/a_i,0) -> (-a_i/b_i,0); kernel of E1 x E2 -> J(C) is its graph',
                            richelot_kernel='classes of [roots of G_i] - [roots of G_j] in J(C)[2]'),
                E2_is_conjugate_of_E1=conj_ok,
                identities_checked=['pencil decomposition G_i=a_i l1^2+b_i l2^2', 'l2^6 E1(l1^2/l2^2)=F=l1^6 E2(l2^2/l1^2)',
                                    'phi1^*(dX/Y)=2W l1 dx/y, phi2^*(dX/Y)=-2W l2 dx/y, independent'],
                scope='binary-form input over Q with squarefree sextic and Richelot determinant zero; '
                      'quotients are over Q or the quadratic field of the pencil squares')


def _fpow(f, k):
    out = [f[0] * 0 + 1]
    for _ in range(k):
        out = fmul(out, f)
    return out


def classify_splitting(factors):
    G = _parse_forms(factors)
    if not binary_squarefree(sextic_form(G)):
        return 'singular_source'
    return 'singular_richelot' if not det3(G) else 'genus_two_target'


# ------------------------------------------------------------ L-polynomials
def curve_lpoly(F, p, g):
    """L-polynomial of Y^2=F (binary form, rational coefficients) at an odd good prime."""
    f1 = Fq(p)
    N1 = count_double_cover(F, f1, f1.rational)
    if g == 1:
        return lpoly_from_counts(N1, None, p, 1)
    f2 = Fq(p, True)
    N2 = count_double_cover(F, f2, f2.rational)
    return lpoly_from_counts(N1, N2, p, g)


def _reduce_K(x, field, sqrtD):
    a, b = field.rational(x.a), field.rational(x.b)
    return field.add(a, field.mul(b, sqrtD))


def _cubic_good(E, field, sqrtD):
    """Cubic model with leading coefficient and discriminant units (smooth reduction)."""
    c = [_reduce_K(x, field, sqrtD) for x in E]
    if c[3] == (0, 0):
        return False
    # check distinct roots through the discriminant of the cubic
    p = field.p
    def m(*xs):
        out = (1, 0)
        for x in xs:
            out = field.mul(out, x)
        return out
    def s(x, k):
        return ((x[0] * k) % p, (x[1] * k) % p)
    d0, d1, d2, d3 = c
    terms = [s(m(d1, d1, d2, d2), 1), s(m(d0, d2, d2, d2), -4), s(m(d1, d1, d1, d3), -4), s(m(d0, d1, d2, d3), 18), s(m(d0, d0, d3, d3), -27)]
    tot = (0, 0)
    for t in terms:
        tot = field.add(tot, t)
    return tot != (0, 0)


def elliptic_lpoly_K(E, p, D, inert):
    """L-polynomial of Y^2=E(X) (cubic over Q(sqrt D)) at a prime above p.

    split: over F_p with a chosen sqrt(D); inert: over F_{p^2}=F_p(sqrt D)."""
    field = Fq(p, inert)
    sqrtD = field.sqrt_of(D) if D != 1 else (0, 0)
    if not _cubic_good(E, field, sqrtD):
        return None
    form4 = list(E) + [K(0, 0, D)]  # quartic binary form with a root at infinity
    N = count_double_cover(form4, field, lambda x: _reduce_K(x, field, sqrtD))
    q = field.q
    return [1, -(q + 1 - N), q]


def verify_singular_lpolys(factors, primes):
    """Exact comparison of L-polynomials of C and of the elliptic factors."""
    r = singular_richelot(factors)
    D = r['field_D']
    F = [Q(c) for c in r['sextic_form']]
    def unpack(v):
        return K(Q(v[0]), Q(v[1]), D) if isinstance(v, list) else K(Q(v), 0, D)
    E1 = [unpack(v) for v in r['E1_cubic']]
    E2 = [unpack(v) for v in r['E2_cubic']]
    rows = []
    for p in primes:
        if not is_prime(p) or p == 2 or D % p == 0 or not form_squarefree_mod_p(F, p):
            continue
        try:
            LC = curve_lpoly(F, p, 2)
            if D == 1 or legendre(D, p) == 1:
                L1 = elliptic_lpoly_K(E1, p, D, False)
                # the second prime above p: conjugate square root, i.e. E2 with the same embedding
                L2 = elliptic_lpoly_K(E2, p, D, False)
                if L1 is None or L2 is None:
                    continue
                LE = [int(c) for c in pmul(L1, L2)]
                kind = 'split' if D != 1 else 'rational'
            else:
                L1 = elliptic_lpoly_K(E1, p, D, True)
                if L1 is None:
                    continue
                LE = [1, 0, L1[1], 0, L1[2]]  # Weil restriction at an inert prime: L(T^2)
                kind = 'inert'
        except ArithmeticError:
            continue
        rows.append(dict(p=p, kind=kind, curve_lpoly=LC, product_lpoly=LE, jacobian_order=sum(LC),
                         product_order=sum(LE), equal=LC == LE))
    return rows


def verify_smooth_lpolys(factors, primes):
    """Regular Richelot: source and target L-polynomials agree at good primes."""
    G = _parse_forms(factors)
    t = smooth_richelot_target(factors)
    F = sextic_form(G)
    H = t['target']
    target_squarefree = binary_squarefree(H)
    rows = []
    for p in primes:
        if not is_prime(p) or p == 2 or not form_squarefree_mod_p(F, p) or not form_squarefree_mod_p(H, p):
            continue
        a, b = curve_lpoly(F, p, 2), curve_lpoly(H, p, 2)
        rows.append(dict(p=p, source_lpoly=a, target_lpoly=b, equal=a == b))
    return dict(delta=str(t['delta']), target=[str(c) for c in H], target_squarefree=target_squarefree, rows=rows)
