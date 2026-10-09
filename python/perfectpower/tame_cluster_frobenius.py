"""Galois action on branch roots in tame extension fields, and what it gives.

Setting.  C: y^2=f(x), f in Q[x] squarefree of degree n>=3, p a prime.  The
roots of f are found in an explicit field

    L = Q_q(varpi),  Q_q=Q_p[zeta]/(phi),  varpi^e = p,

phi monic, irreducible mod p, deg phi = f, p does not divide e and e | q-1, so
L/Q_p is Galois and tamely ramified with Gal(L/Q_p)=<tau,F>:
F(zeta)=Hensel lift of zeta^p, F(varpi)=varpi; tau(zeta)=zeta,
tau(varpi)=omega*varpi, omega the Teichmuller lift of an element of order e.
Every element of L is sum a_{ij} zeta^j varpi^i with rational a_{ij}; the
valuation is exactly min(v_p(a_ij)+i/e) because {zeta^j} is an integral basis
of the unramified ring and the varpi-powers have distinct fractional parts.

Roots are approximations r~ found by residue enumeration and Hensel lifting,
certified by Newton's lemma on f itself (exact arithmetic): v(f(r~))>2v(f'(r~))
gives a unique root r with v(r-r~)>=v(f(r~))-v(f'(r~)).  Root distances below
that radius are therefore exact, and tau, F act on roots by certified
permutations.  The smallest (f,e) in a fixed search order is used.

Consequences implemented here (p odd unless stated):
* the cluster picture over K (reused from cluster_stable_reduction through an
  index domain), with inertia and Frobenius permutations of roots and clusters;
* the tame inertia action for any tame e (not only e<=2): dim H^1(C)^I is the
  sum of a Lefschetz average over the positive-genus components of the
  semistable fibre and a Lefschetz average on the dual graph, which gives the
  conductor exponent n=2g-dim H^1^I (wild part zero);
* for curves semistable over Q_p: the Frobenius action on clusters and sheets
  (signs from quadratic characters of residues in F_{p^m} at orbit closings),
  hence the Frobenius-fixed component group (Tamagawa number);
* Swan conductor (wild part) for p odd via local discriminants of the root
  fields, using PARI's number-field different as an exact oracle.
"""
from fractions import Fraction as Q
from math import gcd
from .cluster_stable_reduction import vp, is_prime, cluster_picture, semistable_graph, stable_contraction, \
    inertia_action, ddmm_semistability, INF
from .semistable_tamagawa import component_group

SCHEMA = 'pp-tame-cluster-frobenius/1'


# ------------------------------------------------------------- F_p[x] helpers
def _ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def _pmod(a, m, p):
    a = _ptrim([x % p for x in a])
    m = _ptrim([x % p for x in m])
    inv = pow(m[-1], -1, p)
    while len(a) >= len(m):
        c = a[-1] * inv % p
        s = len(a) - len(m)
        for i, x in enumerate(m):
            a[s + i] = (a[s + i] - c * x) % p
        a = _ptrim(a)
    return a


def _pmulmod(a, b, m, p):
    out = [0] * (len(a) + len(b) - 1) if a and b else []
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return _pmod(out, m, p)


def _ppowmod(a, k, m, p):
    r, b = [1], _pmod(a, m, p)
    while k:
        if k & 1:
            r = _pmulmod(r, b, m, p)
        b = _pmulmod(b, b, m, p)
        k >>= 1
    return r


def _pgcd(a, b, p):
    a, b = _ptrim([x % p for x in a]), _ptrim([x % p for x in b])
    while b:
        a, b = b, _pmod(a, b, p)
    return a


def _primes_dividing(n):
    out, d = [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def irreducible_mod_p(p, f):
    """Lexicographically first monic irreducible polynomial of degree f over F_p (low->high)."""
    if f == 1:
        return [0, 1]
    import itertools
    for tail in itertools.product(range(p), repeat=f):
        m = list(tail) + [1]
        if m[0] == 0:
            continue
        x = [0, 1]
        if _ppowmod(x, p ** f, m, p) != _pmod(x, m, p):
            continue
        if all(len(_pgcd([a - b for a, b in zip(_pad(_ppowmod(x, p ** (f // l), m, p), f + 1), _pad(x, f + 1))], m, p)) == 1
               for l in _primes_dividing(f)):
            return m
    raise AssertionError('no irreducible polynomial found')


def _pad(a, n):
    return list(a) + [0] * (n - len(a))


def _qtrunc(c, N, p):
    """Rational c reduced to absolute p-adic precision N (representative p^k*[0,p^(N-k)))."""
    if not c:
        return Q(0)
    k = int(vp(c, p))
    if k >= N:
        return Q(0)
    u = c / Q(p) ** k
    m = p ** (N - k)
    r = u.numerator * pow(u.denominator, -1, m) % m
    return Q(r) * Q(p) ** k


# ------------------------------------------------------------- the field L
class TameField:
    def __init__(self, p, f=1, e=1, N=30):
        if not is_prime(p):
            raise ValueError('prime p required')
        if type(f) is not int or type(e) is not int or f < 1 or e < 1:
            raise ValueError('positive integers f, e required')
        if e % p == 0:
            raise ValueError('tame ramification (p does not divide e) required')
        if (p ** f - 1) % e:
            raise ValueError('e must divide p^f-1 so that L/Q_p is Galois')
        self.p, self.f, self.e, self.N, self.q = p, f, e, N, p ** f
        self.phi = irreducible_mod_p(p, f)  # monic, integral, irreducible mod p
        self.zero = tuple(tuple(Q(0) for _ in range(f)) for _ in range(e))
        self.one = self.const(1)
        # Frobenius image of zeta and a primitive e-th root of unity, Hensel lifted.
        self.frob_zeta = self._lift_frobenius()
        self.omega = self._teichmuller_order_e()

    # -- element construction
    def const(self, c):
        rows = [[Q(0)] * self.f for _ in range(self.e)]
        rows[0][0] = Q(c)
        return tuple(tuple(r) for r in rows)

    def _unit_vector(self, i, j):
        rows = [[Q(0)] * self.f for _ in range(self.e)]
        rows[i][j] = Q(1)
        return tuple(tuple(r) for r in rows)

    def from_zeta_poly(self, coeffs, i=0):
        rows = [[Q(0)] * self.f for _ in range(self.e)]
        for j, c in enumerate(coeffs):
            rows[i][j] = Q(c)
        return tuple(tuple(r) for r in rows)

    # -- arithmetic
    def add(self, x, y):
        return tuple(tuple(a + b for a, b in zip(r, s)) for r, s in zip(x, y))

    def sub(self, x, y):
        return tuple(tuple(a - b for a, b in zip(r, s)) for r, s in zip(x, y))

    def scale(self, x, c):
        c = Q(c)
        return tuple(tuple(a * c for a in r) for r in x)

    def _zmul(self, a, b):
        f, phi = self.f, self.phi
        out = [Q(0)] * (2 * f - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        out[i + j] += x * y
        for k in range(2 * f - 2, f - 1, -1):
            c = out[k]
            if c:
                out[k] = Q(0)
                for j in range(f):
                    out[k - f + j] -= c * phi[j]
        return out[:f]

    def mul(self, x, y):
        e, f, p = self.e, self.f, self.p
        acc = [[Q(0)] * f for _ in range(e)]
        for i, r in enumerate(x):
            if not any(r):
                continue
            for k, s in enumerate(y):
                if not any(s):
                    continue
                prod = self._zmul(r, s)
                idx = i + k
                if idx >= e:
                    idx -= e
                    prod = [c * p for c in prod]
                row = acc[idx]
                for j in range(f):
                    row[j] += prod[j]
        return tuple(tuple(r) for r in acc)

    def is_zero(self, x):
        return not any(any(r) for r in x)

    def v(self, x):
        best = INF
        for i, r in enumerate(x):
            for c in r:
                if c:
                    w = vp(c, self.p) + Q(i, self.e)
                    if best is INF or w < best:
                        best = w
        return best

    def trunc(self, x, N=None):
        N = self.N if N is None else N
        return tuple(tuple(_qtrunc(c, N, self.p) for c in r) for r in x)

    def varpi_power(self, k):
        """varpi^k for any integer k, exactly."""
        a, b = divmod(k, self.e)
        x = self._unit_vector(b, 0) if self.e > 1 else self.const(1)
        return self.scale(x, Q(self.p) ** a)

    def normalise(self, x):
        """(k, u) with x = varpi^k u, v(u)=0."""
        k = int(self.v(x) * self.e)
        return k, self.mul(x, self.varpi_power(-k))

    # -- residue field F_q = F_p[zeta]/(phi)
    def residue(self, x):
        if self.v(x) is not INF and self.v(x) < 0:
            raise ValueError('residue of a non-integral element')
        out = []
        for c in x[0]:
            if c and vp(c, self.p) < 0:
                raise ValueError('non-integral coefficient')
            out.append(c.numerator * pow(c.denominator, -1, self.p) % self.p if c else 0)
        return tuple(out)

    def res_mul(self, a, b):
        return tuple(_pad(_pmulmod(list(a), list(b), self.phi, self.p), self.f))

    def res_pow(self, a, k):
        return tuple(_pad(_ppowmod(list(a), k, self.phi, self.p), self.f))

    def res_elements(self):
        import itertools
        return [tuple(t) for t in itertools.product(range(self.p), repeat=self.f)]

    def lift(self, a):
        return self.from_zeta_poly(a)

    def inverse(self, x):
        k, u = self.normalise(x)
        r = self.residue(u)
        w = self.lift(self.res_pow(r, self.q - 2))
        prec = 1
        while prec < self.N + 4:
            w = self.trunc(self.mul(w, self.sub(self.const(2), self.mul(u, w))), self.N + 8)
            prec *= 2
        return self.mul(w, self.varpi_power(-k))

    # -- Galois action
    def _lift_frobenius(self):
        if self.f == 1:
            return self.const(0)
        z = self.from_zeta_poly([0, 1])
        phi = [Q(c) for c in self.phi]
        r = self.lift(self.res_pow((0, 1) + (0,) * (self.f - 2), self.p))
        for _ in range(64):
            val, der = self.const(0), self.const(0)
            for c in reversed(phi):
                der = self.add(self.mul(der, r), val)
                val = self.add(self.mul(val, r), self.const(c))
            if self.v(val) is INF or self.v(val) >= self.N + 8:
                break
            r = self.trunc(self.sub(r, self.mul(val, self.inverse(der))), self.N + 8)
        return r

    def _teichmuller_order_e(self):
        if self.e == 1:
            return self.const(1)
        order = self.q - 1
        for a in self.res_elements():
            if not any(a):
                continue
            # element of exact order e
            b = self.res_pow(a, order // self.e)
            if all(self.res_pow(b, self.e // l) != (1,) + (0,) * (self.f - 1) for l in _primes_dividing(self.e)):
                break
        r = self.lift(b)
        for _ in range(64):
            pw = self.const(1)
            for _ in range(self.e - 1):
                pw = self.mul(pw, r)
            val = self.sub(self.mul(pw, r), self.const(1))
            if self.v(val) is INF or self.v(val) >= self.N + 8:
                break
            r = self.trunc(self.sub(r, self.mul(val, self.inverse(self.scale(pw, self.e)))), self.N + 8)
        return r

    def automorphism(self, x, frob=0, tau=0):
        """F^frob tau^tau applied to x (tau first)."""
        zeta_img = self.from_zeta_poly([0, 1]) if self.f > 1 else self.const(0)
        for _ in range(frob):
            zeta_img = self.trunc(self._apply_zeta(self.frob_zeta, zeta_img), self.N + 8) if self.f > 1 else zeta_img
        w = self.const(1)
        for _ in range(tau % self.e):
            w = self.trunc(self.mul(w, self.omega), self.N + 8)
        # varpi -> w*varpi ; zeta -> zeta_img
        out = self.zero
        zp = [self.const(1)]
        for j in range(1, self.f):
            zp.append(self.trunc(self.mul(zp[-1], zeta_img), self.N + 8))
        wp = [self.const(1)]
        for i in range(1, self.e):
            wp.append(self.trunc(self.mul(wp[-1], w), self.N + 8))
        for i, row in enumerate(x):
            if not any(row):
                continue
            piece = self.zero
            for j, c in enumerate(row):
                if c:
                    piece = self.add(piece, self.scale(zp[j], c))
            out = self.add(out, self.mul(self.mul(piece, wp[i]), self.varpi_power(i)))
        return out

    def _apply_zeta(self, poly_elem, zeta_img):
        """Substitute zeta->zeta_img into an element of Q_q (row 0)."""
        out = self.const(0)
        pw = self.const(1)
        for c in poly_elem[0]:
            if c:
                out = self.add(out, self.scale(pw, c))
            pw = self.trunc(self.mul(pw, zeta_img), self.N + 8)
        return out

    def packet(self, x):
        return [[str(c) for c in r] for r in x]


# ------------------------------------------------------------- polynomials over L
def _peval(L, coeffs, x):
    val = L.zero
    for c in reversed(coeffs):
        val = L.add(L.mul(val, x), c)
    return val


def _pderiv(L, coeffs):
    return [L.scale(c, k) for k, c in enumerate(coeffs)][1:]


def _taylor_shift(L, coeffs, a, k):
    """g(a + varpi^k y) as a polynomial in y."""
    n = len(coeffs) - 1
    # Horner-style shift by a
    c = list(coeffs)
    for i in range(n):
        for j in range(n - 1, i - 1, -1):
            c[j] = L.add(c[j], L.mul(a, c[j + 1]))
    s = L.varpi_power(k)
    out, pw = [], L.one
    for j in range(n + 1):
        out.append(L.mul(c[j], pw))
        pw = L.mul(pw, s)
    return out


def _res_poly_roots(L, coeffs):
    """Roots with multiplicity in F_q of a residue polynomial (list of F_q tuples, low->high)."""
    zero = (0,) * L.f

    def ev(cs, a):
        val = zero
        for c in reversed(cs):
            val = tuple((x + y) % L.p for x, y in zip(L.res_mul(val, a), c))
        return val

    def dv(cs):
        return [tuple(k * x % L.p for x in c) for k, c in enumerate(cs)][1:]
    out = []
    for a in L.res_elements():
        m, cs = 0, list(coeffs)
        while cs and any(any(c) for c in cs) and ev(cs, a) == zero:
            # multiplicity via Hasse-type deflation: divide by (x-a)
            q, r = [], zero
            for c in reversed(cs):
                r = tuple((x + y) % L.p for x, y in zip(L.res_mul(r, a), c))
                q.append(r)
            q = list(reversed(q))[1:]
            cs = q
            m += 1
        if m:
            out.append((a, m))
    return out


def _roots_integral(L, g, depth=0, max_depth=400):
    """All roots in O_L of polynomial g (coefficients in L)."""
    if depth > max_depth:
        raise ArithmeticError('root separation exceeded the recursion bound')
    vals = [L.v(c) for c in g if not L.is_zero(c)]
    m = min(vals)
    s = L.varpi_power(-int(m * L.e))
    g = [L.mul(c, s) for c in g]
    res = [L.residue(c) if (not L.is_zero(c) and L.v(c) >= 0) else (0,) * L.f for c in g]
    while res and not any(res[-1]):
        res.pop()
    if len(res) <= 1:
        return []
    out = []
    for a, mult in _res_poly_roots(L, res):
        A = L.lift(a)
        if mult == 1:
            out.append(_newton(L, g, A))
        else:
            h = _taylor_shift(L, g, A, 1)
            for y in _roots_integral(L, h, depth + 1, max_depth):
                out.append(L.add(A, L.mul(L.varpi_power(1), y)))
    return out


def _newton(L, g, r):
    dg = _pderiv(L, g)
    W = L.N + 12
    for _ in range(200):
        val = _peval(L, g, r)
        if L.is_zero(val) or L.v(val) >= W:
            return r
        r = L.trunc(L.sub(r, L.mul(val, L.inverse(_peval(L, dg, r)))), W + 4)
    raise ArithmeticError('Newton iteration did not converge')


# ------------------------------------------------------------- roots of f over Q
def _qpoly(coeffs):
    c = [Q(x) for x in coeffs]
    while c and not c[-1]:
        c.pop()
    return c


def candidate_fields(p, max_f=6, max_e=12, max_q=5000):
    out = []
    for f in range(1, max_f + 1):
        if p ** f > max_q:
            break
        for e in range(1, max_e + 1):
            if e % p and (p ** f - 1) % e == 0:
                out.append((f * e, e, f))
    return [(f, e) for _, e, f in sorted(out)]


def split_roots(coeffs, p, *, f=None, e=None, N=None):
    """Certified approximations of all roots of f in the first tame field that splits it.

    coeffs: rational coefficients low->high.  Returns the field and the roots
    r~_i with certified radii delta_i (v(r~_i - r_i) >= delta_i).
    """
    c = _qpoly(coeffs)
    n = len(c) - 1
    if n < 1:
        raise ValueError('nonconstant polynomial required')
    from sympy import Poly, symbols, gcd as sgcd
    X = symbols('X')
    P = Poly([x for x in reversed(c)], X, domain='QQ')
    if sgcd(P, P.diff(X)).degree() != 0:
        raise ValueError('squarefree polynomial required')
    lead = c[-1]
    # monic integral polynomial in X = lam * x, lam an integer clearing denominators
    den = 1
    for x in c:
        den = den * x.denominator // gcd(den, x.denominator)
    ci = [x * den for x in c]
    a = ci[-1]
    # F(X) = a^(n-1) f(X/a) is monic integral
    F = [ci[k] * a ** (n - 1 - k) for k in range(n)] + [Q(1)]
    lam = Q(a)
    order = [(f, e)] if f is not None else candidate_fields(p)
    for ff, ee in order:
        prec = N if N is not None else 24 + 2 * int(sum(abs(vp(x, p)) for x in F if x))
        L = TameField(p, ff, ee, prec)
        Fl = [L.const(x) for x in F]
        try:
            raw = _roots_integral(L, Fl)
        except ArithmeticError:
            continue
        if len(raw) != n:
            if f is not None:
                raise ArithmeticError('polynomial does not split in the requested field')
            continue
        dF = _pderiv(L, Fl)
        roots, radii = [], []
        for r in raw:
            fv, dv = L.v(_peval(L, Fl, r)), L.v(_peval(L, dF, r))
            if fv is not INF and not fv > 2 * dv:
                raise ArithmeticError('Newton certificate failed')
            radius = INF if fv is INF else fv - dv
            roots.append(L.scale(r, 1 / lam))
            radii.append(INF if radius is INF else radius - vp(lam, p))
        return dict(field=L, roots=roots, radii=radii, leading=lead, monic_scale=str(lam))
    raise ArithmeticError('no tame splitting field within the search bounds (wild or too large)')


def root_galois_data(coeffs, p, **kw):
    sp = split_roots(coeffs, p, **kw)
    L, roots, radii = sp['field'], sp['roots'], sp['radii']
    n = len(roots)
    dist = [[None if i == j else L.v(L.sub(roots[i], roots[j])) for j in range(n)] for i in range(n)]
    sep = max(d for row in dist for d in row if d is not None)
    rad = min(r for r in radii if r is not INF) if any(r is not INF for r in radii) else Q(10 ** 6)
    # coefficient-side precision of the Galois images
    shift = max([0] + [-int(vp(c, p)) + 1 for r in roots for row in r for c in row if c])
    gal_prec = min(rad, Q(L.N + 8 - shift))
    if not gal_prec > sep:
        raise ArithmeticError('precision does not separate the roots')

    def perm(frob, tau):
        out = []
        for r in roots:
            s = L.automorphism(r, frob=frob, tau=tau)
            hits = [j for j, t in enumerate(roots) if L.v(L.sub(s, t)) is INF or L.v(L.sub(s, t)) >= gal_prec]
            if len(hits) != 1:
                raise ArithmeticError('Galois image not matched uniquely')
            out.append(hits[0])
        if sorted(out) != list(range(n)):
            raise ArithmeticError('Galois action is not a permutation')
        return out
    frob = perm(1, 0)
    tau = perm(0, 1)
    return dict(field=L, roots=roots, radii=radii, dist=dist, separation=sep, galois_precision=gal_prec,
                frobenius=frob, inertia=tau, leading=sp['leading'])


# ------------------------------------------------------------- index domain for clusters
class IndexDomain:
    """Roots as indices; valuations from the certified distance table."""

    def __init__(self, p, data):
        self.p, self.data = p, data
        self.name = 'Q_%d (roots in Q_%d^%d(%d^(1/%d)))' % (p, p, data['field'].f, p, data['field'].e)

    def parse(self, r):
        return int(r)

    def sub(self, i, j):
        return (i, j)

    def v(self, x):
        return self.data['dist'][x[0]][x[1]]

    def sigma(self, i):
        return self.data['inertia'][i]

    def frobenius(self, i):
        return self.data['frobenius'][i]

    def packet(self, i):
        return i

    def lead_v(self, c):
        return vp(c, self.p)


def _cycle_power(perm, k):
    out = list(range(len(perm)))
    for _ in range(k):
        out = [perm[i] for i in out]
    return out


def _cluster_perm(pic, root_perm):
    by = {frozenset(c['roots']): c['id'] for c in pic['clusters']}
    out = []
    for c in pic['clusters']:
        img = frozenset(root_perm[i] for i in c['roots'])
        if img not in by:
            raise AssertionError('Galois action does not permute clusters')
        out.append(by[img])
    return out


def _frac1(x):
    return Q(x) - (Q(x).numerator // Q(x).denominator)


# ------------------------------------------------------------- tame inertia by Lefschetz
def tame_inertia(pic, tau_roots, e):
    """dim H^1(C)^I for tame inertia of order dividing 2e, any genus, p odd.

    The generator tau multiplies p^a by exp(2 pi i a).  On the component of a
    cluster s fixed by tau^k (centre chosen tau^k-invariant): x -> alpha x,
    Y' -> gamma Y', alpha=exp(2 pi i k d_s), gamma=exp(pi i k (nu_s-2 d_s E_s)).
    tr(phi|H^1)=2-#Fix(phi) for phi != id; graph: chi_{H_1}=1-#fixV+#fixE.
    """
    cl = pic['clusters']
    N = 2 * e
    powers = [_cluster_perm(pic, _cycle_power(tau_roots, k)) for k in range(N)]
    root_powers = [_cycle_power(tau_roots, k) for k in range(N)]
    if _cycle_power(tau_roots, N) != list(range(len(tau_roots))):
        raise AssertionError('inertia order does not divide 2e')
    info = {}
    for c in cl:
        flags = c['odd_children'] + c['size'] % 2
        E = sum(cl[k]['size'] // 2 for k in c['children'])
        mu = c['nu'] - c['size'] * c['depth']
        odd_kids = [('r', i) for i in c['singletons']] + [('c', k) for k in c['children'] if cl[k]['size'] % 2]
        info[c['id']] = dict(two=(flags == 0), g=(flags - 2) // 2 if flags else 0, E=E, mu=mu, n=c['odd_children'],
                             odd_kids=odd_kids, d=c['depth'], nu=c['nu'])

    def sheet_sign(mu, k):
        x = k * mu
        if x.denominator != 1:
            raise AssertionError('sheet phase is not a sign')
        return 1 if int(x) % 2 == 0 else -1

    trace_graph = []
    for k in range(N):
        fixV = fixE = 0
        for c in cl:
            if powers[k][c['id']] != c['id']:
                continue
            I = info[c['id']]
            fixV += (2 if sheet_sign(I['mu'], k) == 1 else 0) if I['two'] else 1
            if c['parent'] is not None:
                fixE += (2 if sheet_sign(I['mu'], k) == 1 else 0) if c['size'] % 2 == 0 else 1
        trace_graph.append(1 - fixV + fixE)
    toric_sum = sum(trace_graph)
    if toric_sum % N:
        raise AssertionError('graph Lefschetz average not integral')
    toric_inv = toric_sum // N

    ab_inv, seen, comp_rows = 0, set(), []
    for c in cl:
        I = info[c['id']]
        if I['two'] or I['g'] < 1 or c['id'] in seen:
            continue
        orbit, x = [], c['id']
        while x not in orbit:
            orbit.append(x)
            x = powers[1][x]
        seen.update(orbit)
        m = len(orbit)
        traces = []
        for j in range(N // m):
            k = m * j
            a_ph = _frac1(k * I['d'])
            g_ph = _frac1(Q(k) * (I['nu'] - 2 * I['d'] * I['E']) / 2)
            if a_ph == 0 and g_ph == 0:
                traces.append(2 * I['g'])
                continue
            n_odd = I['n']
            if a_ph == 0:
                if g_ph != Q(1, 2):
                    raise AssertionError('alpha=1 forces the hyperelliptic involution')
                fix = n_odd + (1 if n_odd % 2 else 0)
                traces.append(2 - fix)
                continue
            # alpha != 1: fixed points over x=0 and x=infinity
            fixed_kids = [o for o in I['odd_kids'] if (root_powers[k][o[1]] == o[1] if o[0] == 'r' else powers[k][o[1]] == o[1])]
            if len(fixed_kids) > 1:
                raise AssertionError('two odd children fixed by a nontrivial rotation')
            if fixed_kids:
                fix0 = 1
            else:
                if _frac1(2 * g_ph) != 0:
                    raise AssertionError('gamma^2 != 1 over x=0')
                fix0 = 2 if g_ph == 0 else 0
            if n_odd % 2:
                fixinf = 1
            else:
                ph = _frac1(g_ph - Q(n_odd, 2) * a_ph)
                if _frac1(2 * ph) != 0:
                    raise AssertionError('phase at infinity not a sign')
                fixinf = 2 if ph == 0 else 0
            traces.append(2 - fix0 - fixinf)
        s = sum(traces)
        if s % (N // m):
            raise AssertionError('component Lefschetz average not integral')
        ab_inv += s // (N // m)
        comp_rows.append(dict(cluster=c['id'], orbit=orbit, genus=I['g'], traces=traces, invariants=s // (N // m)))
    g = pic['genus']
    graph = semistable_graph(pic)
    pot_ab = sum(v['genus'] for v in graph['vertices'])
    b1 = graph['cycle_rank']
    n_tame = 2 * g - ab_inv - toric_inv
    if n_tame < 0:
        raise AssertionError('negative conductor')
    return dict(order=N, abelian_part_invariants=ab_inv, toric_rank=toric_inv, potential_abelian_dimension=pot_ab,
                potential_toric_rank=b1, conductor_exponent=n_tame, tame_part=n_tame, wild_part=0,
                semistable_over_K=(ab_inv == 2 * pot_ab and toric_inv == b1),
                graph_traces=trace_graph, component_traces=comp_rows)


# ------------------------------------------------------------- Frobenius on clusters and sheets
def frobenius_graph_action(pic, data, coeffs):
    """Vertex and edge permutations of Frobenius on the semistable graph over Q_p.

    Requires semistability over Q_p (so inertia acts trivially on the graph)
    and mu_s=v(Theta_s) even for every even cluster.  Sheets of an even
    cluster s are labelled by theta_s=sqrt(c prod_{r notin s}(z_s-r)); for a
    two-sheeted parent the labels are tied by theta_s=theta_P rho_s.  Labels
    are transported along Frobenius orbits; the closing sign of an orbit of
    length m is the quadratic character of a residue in F_{p^m}.
    """
    L, roots, p = data['field'], data['roots'], data['field'].p
    cl = pic['clusters']
    Fc = _cluster_perm(pic, data['frobenius'])
    lead = Q(_qpoly(coeffs)[-1])
    graph = semistable_graph(pic)
    two = {c['id']: (c['odd_children'] + c['size'] % 2) == 0 for c in cl}
    level = {}
    for c in cl:
        level[c['id']] = 0 if c['parent'] is None else level[c['parent']] + 1

    def unit_residue(x, v):
        if v.denominator != 1:
            raise ValueError('ramified sheet character unsupported (half-integral valuation)')
        u = L.mul(x, L.const(Q(p) ** (-int(v))))
        return L.residue(u)

    def theta_sq(s):
        z = roots[cl[s]['roots'][0]]
        val = L.const(lead)
        for i in range(len(roots)):
            if i not in cl[s]['roots']:
                val = L.mul(val, L.sub(z, roots[i]))
        return val

    def chi(res, m):
        one = (1,) + (0,) * (L.f - 1)
        mone = (p - 1,) + (0,) * (L.f - 1)
        t = L.res_pow(res, (p ** m - 1) // 2)
        if t == one:
            return 1
        if t == mone:
            return -1
        raise AssertionError('residue not in F_{p^m}')
    eta, record = {}, {}
    order = sorted((c['id'] for c in cl if c['size'] % 2 == 0), key=lambda k: (level[k], k))
    for s in order:
        if s in eta:
            continue
        orbit, x = [], s
        while x not in orbit:
            orbit.append(x)
            x = Fc[x]
        m = len(orbit)
        P = cl[s]['parent']
        if P is not None and two[P]:
            z = roots[cl[s]['roots'][0]]
            prod = L.const(1)
            for i in cl[P]['roots']:
                if i not in cl[s]['roots']:
                    prod = L.mul(prod, L.sub(z, roots[i]))
            v = L.v(prod)
            close = chi(unit_residue(prod, v), m)
            for i, t in enumerate(orbit):
                eta[t] = eta[cl[t]['parent']] * (close if i == m - 1 else 1)
            record[s] = dict(orbit=orbit, kind='relative', valuation=str(v), closing_sign=close)
        else:
            th = theta_sq(s)
            v = L.v(th)
            if v.denominator != 1 or int(v) % 2:
                raise ValueError('odd or fractional v(Theta_s): sheet character needs a ramified square root')
            close = chi(unit_residue(th, v), m)
            for i, t in enumerate(orbit):
                eta[t] = close if i == m - 1 else 1
            record[s] = dict(orbit=orbit, kind='absolute', valuation=str(v), closing_sign=close)
    lifts = graph['lifts']
    va = []
    for vtx in graph['vertices']:
        s = vtx['cluster']
        tgt = lifts[Fc[s]]
        if len(tgt) == 2:
            va.append(tgt[vtx['sheet'] ^ (eta[s] < 0)])
        else:
            va.append(tgt[0])
    by = {(ed['child'], ed['lift']): i for i, ed in enumerate(graph['edges'])}
    ea = []
    for ed in graph['edges']:
        c = ed['child']
        j = 0 if ed['ramified'] else ed['lift'] ^ (eta[c] < 0)
        ea.append((by[Fc[c], j], 1))
    return dict(graph=graph, vertex_action=va, edge_action=ea, cluster_frobenius=Fc,
                sheet_signs={str(k): v for k, v in sorted(eta.items())}, orbit_records={str(k): v for k, v in record.items()})


# ------------------------------------------------------------- public entry points
def analyse_curve(coeffs, p, leading_check=True, **kw):
    """Cluster picture, inertia/Frobenius permutations and tame conductor of y^2=f(x)."""
    if p == 2:
        raise ValueError('odd p required for the cluster conductor (see dyadic_reduction for p=2)')
    c = _qpoly(coeffs)
    data = root_galois_data(c, p, **kw)
    D = IndexDomain(p, data)
    pic = cluster_picture(D, list(range(len(data['roots']))), c[-1])
    tame = tame_inertia(pic, data['inertia'], data['field'].e)
    inertia_orbit_max = max(len(set(_orbit(data['inertia'], i))) for i in range(len(data['inertia'])))
    ddmm = ddmm_semistability(pic) and inertia_orbit_max <= 2
    # The principal-cluster criterion is stated for g>=2; in genus one R can be a
    # cotwin and the criterion is silent about the twin, so only g>=2 is compared.
    if pic['genus'] >= 2 and ddmm != tame['semistable_over_K']:
        raise AssertionError('Lefschetz semistability disagrees with the DDMM criterion')
    legacy = None
    if inertia_orbit_max <= 2 and all((2 * cc['depth']).denominator == 1 for cc in pic['clusters']):
        try:
            legacy = inertia_action(pic)
        except AssertionError:
            legacy = None
        if legacy is not None and legacy['conductor_exponent'] != tame['conductor_exponent']:
            raise AssertionError('Lefschetz conductor disagrees with the order-two inertia replay')
    stable = stable_contraction(semistable_graph(pic))
    L = data['field']
    out = dict(schema=SCHEMA, p=p, coefficients=[str(x) for x in c], genus=pic['genus'],
               splitting_field=dict(f=L.f, e=L.e, phi_mod_p=L.phi, precision=L.N),
               root_radii=[str(r) for r in data['radii']], galois_precision=str(data['galois_precision']),
               frobenius_root_permutation=data['frobenius'], inertia_root_permutation=data['inertia'],
               frobenius_cluster_permutation=_cluster_perm(pic, data['frobenius']),
               inertia_cluster_permutation=_cluster_perm(pic, data['inertia']),
               clusters=[dict(id=k['id'], roots=k['roots'], depth=str(k['depth']), parent=k['parent'],
                              principal=k['principal'], nu=str(k['nu'])) for k in pic['clusters']],
               stable_graph=stable, potentially_good=stable['cycle_rank'] == 0 and len(stable['vertices']) == 1,
               tame_inertia=tame, conductor_exponent=tame['conductor_exponent'], ddmm_semistable_over_K=ddmm,
               semistable_over_K=tame['semistable_over_K'],
               order_two_replay=None if legacy is None else legacy['conductor_exponent'],
               scope='p odd, splitting field tame; conductor is tame (wild part zero)')
    return out, pic, data


def _orbit(perm, i):
    out, x = [], i
    while x not in out:
        out.append(x)
        x = perm[x]
    return out


def extension_tamagawa(coeffs, p, **kw):
    """Frobenius-fixed component group of a curve semistable over Q_p with roots in any tame field."""
    out, pic, data = analyse_curve(coeffs, p, **kw)
    if not out['semistable_over_K']:
        raise ValueError('semistable reduction over Q_p required')
    act = frobenius_graph_action(pic, data, coeffs)
    g = act['graph']
    cg = component_group(len(g['vertices']), [(e['parent_vertex'], e['child_vertex'], e['length']) for e in g['edges']],
                         vertex_action=act['vertex_action'], edge_action=act['edge_action'])
    out.update(component_group=cg, tamagawa_number=cg['tamagawa_number'], geometric_component_order=cg['geometric_order'],
               frobenius_sheet_signs=act['sheet_signs'], frobenius_orbit_records=act['orbit_records'],
               scope='p odd, semistable over Q_p, roots in Q_q(p^(1/e)) with e<=2 forced by semistability')
    return out


# ------------------------------------------------------------- wild part for p odd (Swan)
def swan_conductor_roots(coeffs, p, pari=None):
    """Swan conductor of the permutation representation on the roots of f.

    sum over Galois orbits of roots of v(Delta_{K(r)/K}) - [K(r):K] + f_{K(r)/K},
    with local discriminant exponents f_P * v_P(different) from PARI's nfinit.
    For p odd this is the wild conductor exponent of Jac(y^2=f) (DDMM).
    """
    import cypari2
    pari = pari or cypari2.Pari()
    c = _qpoly(coeffs)
    from sympy import Poly, symbols, factor_list
    X = symbols('x')
    P = Poly([x for x in reversed(c)], X, domain='QQ')
    total, rows = 0, []
    for fac, mult in factor_list(P.as_expr())[1]:
        fp = Poly(fac, X)
        if fp.degree() == 1:
            rows.append(dict(factor=str(fac), primes=[dict(e=1, f=1, swan=0)]))
            continue
        coeffs_int = fp.clear_denoms()[1].all_coeffs()
        polstr = 'Pol([%s])' % ','.join(str(int(a)) for a in coeffs_int)
        data = pari('my(nf=nfinit(polredbest(%s))); [[pr.e, pr.f, idealval(nf, nf.diff, pr)] | pr <- idealprimedec(nf, %d)]' % (polstr, p))
        prs = []
        for row in data:
            e_, f_, vd = int(row[0]), int(row[1]), int(row[2])
            sw = f_ * vd - e_ * f_ + f_
            total += sw
            prs.append(dict(e=e_, f=f_, different_valuation=vd, swan=sw))
        rows.append(dict(factor=str(fac), primes=prs))
    return dict(swan=total, factors=rows)
