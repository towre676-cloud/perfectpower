"""Reduction at p=2 (and p=3) by routes independent of cluster pictures.

The odd-p cluster calculus does not describe reduction at 2: the Galois action
on the roots of f no longer determines the action on H^1 because the double
cover y^2=f is itself wildly ramified over the special fibre.  This module
implements what is tractable and exactly checkable:

1. Tate's algorithm for elliptic curves over Z_(p), every p including 2 and 3:
   Kodaira symbol, conductor exponent (Ogg-Saito f=v(Delta_min)-m+1), local
   Tamagawa number, minimal discriminant valuation, and the Swan conductor
   delta=f-epsilon (epsilon=0,1,2 for good, multiplicative, additive).
2. Genus one as hyperelliptic curves: y^2=cubic and y^2=quartic are sent to
   Weierstrass equations (the quartic through the classical invariants I, J of
   its Jacobian y^2=x^3-27Ix-27J) and passed to (1).
3. Genus two at 2, two subclasses with exact certificates:
   (a) good reduction: a model y^2+Q(x)y=P(x) with Q,P in Z_(2)[x] obtained
       from y^2=f by y=2y'+T(x), f=T^2 mod 4, whose reduction over F_2 is smooth
       of genus two (checked affinely and at infinity by resultants over F_2);
       then the conductor exponent at 2 is 0;
   (b) bielliptic split curves y^2=g(x^2), g a squarefree cubic with g(0)!=0:
       Jac(C) is Q-isogenous to E1 x E2, E1: Y^2=g(X), E2: Y^2=X^3 g(1/X), so
       the conductor exponent (and Swan conductor) at every p is the sum of
       those of E1 and E2 from (1).
Nothing here uses PARI; PARI's elllocalred and genus2red are oracles in the
develop script and tests only.
"""
from fractions import Fraction as Q
from itertools import product

SCHEMA = 'pp-dyadic-reduction/1'


def _v(x, p):
    x = Q(x)
    if not x:
        return 10 ** 9
    n, d, k = abs(x.numerator), x.denominator, 0
    while n % p == 0:
        n //= p
        k += 1
    while d % p == 0:
        d //= p
        k -= 1
    return k


def _invariants(a):
    a1, a2, a3, a4, a6 = a
    b2 = a1 * a1 + 4 * a2
    b4 = 2 * a4 + a1 * a3
    b6 = a3 * a3 + 4 * a6
    b8 = a1 * a1 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 * a3 - a4 * a4
    c4 = b2 * b2 - 24 * b4
    c6 = -b2 ** 3 + 36 * b2 * b4 - 216 * b6
    disc = -b2 * b2 * b8 - 8 * b4 ** 3 - 27 * b6 * b6 + 9 * b2 * b4 * b6
    return b2, b4, b6, b8, c4, c6, disc


def _rst(a, r, s, t):
    a1, a2, a3, a4, a6 = a
    return (a1 + 2 * s,
            a2 - s * a1 + 3 * r - s * s,
            a3 + r * a1 + 2 * t,
            a4 - s * a3 + 2 * r * a2 - (t + r * s) * a1 + 3 * r * r - 2 * s * t,
            a6 + r * a4 + r * r * a2 + r ** 3 - t * a3 - t * t - r * t * a1)


def _integral_model(a):
    a = [Q(x) for x in a]
    u = 1
    while any(x.denominator != 1 for x in a):
        # scale by the least common denominator's primes
        d = 1
        for x in a:
            d = d * x.denominator // __import__('math').gcd(d, x.denominator)
        u *= d
        a = [a[i] * d ** w for i, w in enumerate((1, 2, 3, 4, 6))]
    return tuple(int(x) for x in a)


def _quadroots(a, b, c, p):
    a, b, c = a % p, b % p, c % p
    if a == 0:
        return b != 0 or c == 0
    return any((a * x * x + b * x + c) % p == 0 for x in range(p))


def _cubicroots(b, c, d, p):
    return sum((x ** 3 + b * x * x + c * x + d) % p == 0 for x in range(p))


def tate(ainvs, p):
    """Tate's algorithm at the prime p for y^2+a1xy+a3y=x^3+a2x^2+a4x+a6."""
    a = _integral_model(ainvs)
    if _invariants(a)[6] == 0:
        raise ValueError('singular cubic')
    half = pow(2, -1, p) if p != 2 else None

    def pr(x):
        return x % p
    scalings = 0
    while True:
        b2, b4, b6, b8, c4, c6, disc = _invariants(a)
        vD = _v(disc, p)
        if vD == 0:
            return _pack(p, 'I0', 0, 1, vD, a, scalings)
        a1, a2, a3, a4, a6 = a
        if p == 2:
            if b2 % 2 == 0:
                r = a4 % 2
                t = (r * (1 + a2 + a4) + a6) % 2
            else:
                r = a3 % 2
                t = (r + a4) % 2
        elif p == 3:
            r = (-b6) % 3 if b2 % 3 == 0 else (-b2 * b4) % 3
            t = (a1 * r + a3) % 3
        else:
            if c4 % p == 0:
                r = (-pow(12, -1, p) * b2) % p
            else:
                r = (-pow(12 * c4, -1, p) * (c6 + b2 * c4)) % p
            t = (-half * (a1 * r + a3)) % p
        a = _rst(a, r, 0, t)
        a1, a2, a3, a4, a6 = a
        b2, b4, b6, b8, c4, c6, disc = _invariants(a)
        if _v(c4, p) == 0:
            if _quadroots(1, a1, -a2, p):
                cp, split = vD, True
            else:
                cp, split = (2 if vD % 2 == 0 else 1), False
            out = _pack(p, 'I%d' % vD, 1, cp, vD, a, scalings)
            out['split'] = split
            return out
        if _v(a6, p) < 2:
            return _pack(p, 'II', vD, 1, vD, a, scalings)
        if _v(b8, p) < 3:
            return _pack(p, 'III', vD - 1, 2, vD, a, scalings)
        if _v(b6, p) < 3:
            cp = 3 if _quadroots(1, a3 // p, -(a6 // p ** 2), p) else 1
            return _pack(p, 'IV', vD - 2, cp, vD, a, scalings)
        if p == 2:
            s = a2 % 2
            t = 2 * ((a6 // 4) % 2)
        else:
            s = (-a1 * half) % p
            t = (-a3 * half) % (p * p)
        a = _rst(a, 0, s, t)
        a1, a2, a3, a4, a6 = a
        b, c, d = a2 // p, a4 // p ** 2, a6 // p ** 3
        w = 27 * d * d - b * b * c * c + 4 * b ** 3 * d - 18 * b * c * d + 4 * c ** 3
        x = 3 * c - b * b
        if w % p:
            return _pack(p, 'I0*', vD - 4, 1 + _cubicroots(b, c, d, p), vD, a, scalings)
        if x % p:
            if p == 2:
                r = c
            elif p == 3:
                r = b * c
            else:
                r = (b * c - 9 * d) * pow(2 * x, -1, p)
            a = _rst(a, p * (r % p), 0, 0)
            ix = iy = 3
            mx = my = p * p
            while True:
                a1, a2, a3, a4, a6 = a
                a2t, a3t, a4t, a6t = a2 // p, a3 // my, a4 // (p * mx), a6 // (mx * my)
                if (a3t * a3t + 4 * a6t) % p:
                    cp = 4 if _quadroots(1, a3t, -a6t, p) else 2
                    break
                t = my * a6t if p == 2 else my * ((-a3t * half) % p)
                a = _rst(a, 0, 0, t)
                my *= p
                iy += 1
                a1, a2, a3, a4, a6 = a
                a2t, a3t, a4t, a6t = a2 // p, a3 // my, a4 // (p * mx), a6 // (mx * my)
                if (a4t * a4t - 4 * a6t * a2t) % p:
                    cp = 4 if _quadroots(a2t, a4t, a6t, p) else 2
                    break
                r = mx * ((a6t * a2t) % p) if p == 2 else mx * ((-a4t * pow(2 * a2t, -1, p)) % p)
                a = _rst(a, r, 0, 0)
                mx *= p
                ix += 1
            n = ix + iy - 5
            return _pack(p, 'I%d*' % n, vD - ix - iy + 1, cp, vD, a, scalings)
        rp = -d if p == 3 else -b * (pow(3, -1, p) if p != 3 else 1)
        a = _rst(a, p * (rp % p), 0, 0)
        a1, a2, a3, a4, a6 = a
        x3t, x6t = a3 // p ** 2, a6 // p ** 4
        if (x3t * x3t + 4 * x6t) % p:
            cp = 3 if _quadroots(1, x3t, -x6t, p) else 1
            return _pack(p, 'IV*', vD - 6, cp, vD, a, scalings)
        t = x6t if p == 2 else x3t * half
        a = _rst(a, 0, 0, -p * p * (t % p))
        a1, a2, a3, a4, a6 = a
        if _v(a4, p) < 4:
            return _pack(p, 'III*', vD - 7, 2, vD, a, scalings)
        if _v(a6, p) < 6:
            return _pack(p, 'II*', vD - 8, 1, vD, a, scalings)
        # non-minimal: divide by p
        a = (a1 // p, a2 // p ** 2, a3 // p ** 3, a4 // p ** 4, a6 // p ** 6)
        scalings += 1


def _pack(p, kod, f, cp, vD, a, scalings):
    eps = 0 if kod == 'I0' else (1 if kod[1:].isdigit() else 2)
    if f < eps:
        raise AssertionError('conductor below tame part')
    if p > 3 and f != eps:
        raise AssertionError('wild conductor at p>3')
    return dict(p=p, kodaira=kod, conductor_exponent=f, tamagawa=cp, minimal_discriminant_valuation=vD,
                tame_part=eps, swan=f - eps, minimal_model=list(a), non_minimal_scalings=scalings)


def kodaira_pari_code(kod):
    """PARI's elllocalred integer code of a Kodaira symbol."""
    if kod == 'I0':
        return 1
    table = {'II': 2, 'III': 3, 'IV': 4, 'II*': -2, 'III*': -3, 'IV*': -4}
    if kod in table:
        return table[kod]
    if kod == 'I0*':
        return -1
    if kod.endswith('*'):
        return -(4 + int(kod[1:-1]))
    return 4 + int(kod[1:])


# ------------------------------------------------------------- genus one models
def weierstrass_from_hyperelliptic(coeffs):
    """a-invariants of the Jacobian of y^2=f, deg f in {3,4} (coefficients low->high)."""
    c = [Q(x) for x in coeffs]
    while c and not c[-1]:
        c.pop()
    if len(c) == 4:
        c0, c1, c2, c3 = c
        return (Q(0), c2, Q(0), c1 * c3, c0 * c3 * c3)
    if len(c) == 5:
        e_, d, cc, b, a = c
        I = 12 * a * e_ - 3 * b * d + cc * cc
        J = 72 * a * cc * e_ + 9 * b * cc * d - 27 * a * d * d - 27 * e_ * b * b - 2 * cc ** 3
        return (Q(0), Q(0), Q(0), -27 * I, -27 * J)
    raise ValueError('cubic or quartic required')


def genus_one_reduction(coeffs, p):
    a = weierstrass_from_hyperelliptic(coeffs)
    out = tate(a, p)
    out['weierstrass'] = [str(x) for x in a]
    return out


# ------------------------------------------------------------- F_2 polynomial helpers
def _f2(a):
    a = [x % 2 for x in a]
    while a and a[-1] == 0:
        a.pop()
    return a


def _f2_mod(a, b):
    a, b = _f2(a), _f2(b)
    while len(a) >= len(b):
        s = len(a) - len(b)
        for i, x in enumerate(b):
            a[s + i] ^= x
        a = _f2(a)
    return a


def _f2_gcd(a, b):
    a, b = _f2(a), _f2(b)
    while b:
        a, b = b, _f2_mod(a, b)
    return a


def _f2_mul(a, b):
    out = [0] * (len(a) + len(b) - 1) if a and b else []
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] ^= y
    return _f2(out)


def _f2_add(a, b):
    n = max(len(a), len(b))
    return _f2([(a[i] if i < len(a) else 0) ^ (b[i] if i < len(b) else 0) for i in range(n)])


def _f2_der(a):
    return _f2([(k * a[k]) % 2 for k in range(1, len(a))])


def _smooth_affine(Qp, Pp):
    """y^2+Qy=P over F_2bar has no affine singular point."""
    Qp, Pp = _f2(Qp), _f2(Pp)
    if not Qp:
        return False  # y^2=P is never smooth of positive genus in char 2 (purely inseparable)
    crit = _f2_add(_f2_mul(_f2_mul(_f2_der(Qp), _f2_der(Qp)), Pp), _f2_mul(_f2_der(Pp), _f2_der(Pp)))
    return len(_f2_gcd(Qp, crit)) == 1


def _reverse(a, d):
    a = list(a) + [0] * (d + 1 - len(a))
    return list(reversed(a[:d + 1]))


def good_model_genus2_at_2(Qp, Pp):
    """Smooth genus-two reduction of y^2+Qy=P over F_2 (weights 3 and 6 at infinity)."""
    Qb, Pb = _f2(Qp), _f2(Pp)
    if len(Qb) > 4 or len(Pb) > 7:
        return False
    if max(2 * (len(Qb) - 1), len(Pb) - 1) not in (5, 6):
        return False
    return _smooth_affine(Qb, Pb) and _smooth_affine(_reverse(Qb, 3), _reverse(Pb, 6))


def genus2_good_reduction_certificate(coeffs, max_shift=True):
    """Search y=2y'+T, f=T^2 mod 4, for a model with smooth reduction mod 2.

    coeffs: integer coefficients of f (low->high), deg 5 or 6.  Translations
    x->x+c (c in {0,1}) are tried as well.  Returns the certificate or None.
    """
    f0 = [int(x) for x in coeffs]
    if len(f0) - 1 not in (5, 6):
        raise ValueError('degree 5 or 6 required')
    shifts = [0, 1] if max_shift else [0]
    for c in shifts:
        f = _shift(f0, c)
        for T in product(range(4), repeat=4):
            T = list(T)
            T2 = [0] * 7
            for i in range(4):
                for j in range(4):
                    T2[i + j] += T[i] * T[j]
            diff = [(f[k] if k < len(f) else 0) - T2[k] for k in range(7)]
            if any(x % 4 for x in diff):
                continue
            Pp = [x // 4 for x in diff]
            if good_model_genus2_at_2(T, Pp):
                return dict(shift=c, T=T, Q=T, P=Pp, model='y^2+Q(x)y=P(x) with y=2y\'+T(x), x->x+%d' % c)
    return None


def _shift(f, c):
    """Coefficients of f(x+c)."""
    from math import comb
    n = len(f) - 1
    return [sum(f[j] * comb(j, k) * c ** (j - k) for j in range(k, n + 1)) for k in range(n + 1)]


# ------------------------------------------------------------- bielliptic genus two
def bielliptic_reduction(g, p):
    """y^2=g(x^2), g=(g0,g1,g2,g3) squarefree cubic with g0 != 0: conductor via E1 x E2."""
    g = [Q(x) for x in g]
    if len(g) != 4 or not g[3] or not g[0]:
        raise ValueError('cubic g with g(0)!=0 and leading coefficient nonzero required')
    E1 = genus_one_reduction(g, p)
    E2 = genus_one_reduction(list(reversed(g)), p)
    return dict(schema=SCHEMA, p=p, g=[str(x) for x in g], E1=E1, E2=E2,
                conductor_exponent=E1['conductor_exponent'] + E2['conductor_exponent'],
                swan=E1['swan'] + E2['swan'], tame_part=E1['tame_part'] + E2['tame_part'],
                argument='Jac(y^2=g(x^2)) ~ E1 x E2 over Q (maps (x,y)->(x^2,y), (x,y)->(1/x^2,y/x^3)); conductors are isogeny invariant')


def even_sextic_split(coeffs):
    """Return g if f(x)=g(x^2) for a cubic g, else None."""
    c = [Q(x) for x in coeffs]
    if len(c) != 7 or any(c[k] for k in (1, 3, 5)):
        return None
    return [c[0], c[2], c[4], c[6]]
