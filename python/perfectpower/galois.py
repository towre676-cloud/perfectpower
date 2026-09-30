"""Two symmetries behind the atlas: the Galois action on the roots of F, and, for the Pell type,
the unit action on the integer solutions.

**Root action.**  The squarefree decomposition F = c * prod_j S_j^j groups roots by multiplicity
j.  Each S_j is factored over Q (factor.factor_squarefree), and each irreducible factor is one
orbit of the Galois group of the splitting field.  Reported per orbit: its size, its group where
computed (trivial; C2 with its root field Q(sqrt(D)); A3 or S3 by the discriminant; S4, A4, D4,
C4 or V4 for quartics by the resolvent cubic and the Kappe–Warren criterion; degree >= 5: a
transitive group, not identified), its multiplicity j and its t = d / gcd(d, j).  A remainder
that the factorizer declines (too many modular factors) is reported as unknown, never as an
orbit.  The atlas profile {t_i} is a union of orbit profiles, and Theorem G's S = sum (1 - 1/t)
is a sum over orbits, so the type follows:
  * radical type: the single obstructed root is Galois-fixed, hence rational, alpha = u/v;
  * Pell type: the two obstructed roots are one conjugate pair or two rational roots;
  * power type: nothing is obstructed; finite type: S > 1.

**Unit action.**  For the Pell type the integer solutions do not move under the root Galois
group.  Each branch gamma * W(n) = square becomes A n^2 + B n + C = m^2, i.e. the norm form
X^2 - 4A Y^2 = Delta of the *real* quadratic field Q(sqrt(A)) (A > 0 not a square), and the
solutions move along orbits of its fundamental unit.  For 2n^2 + 1 = m^2 the roots of 2x^2 + 1
lie in Q(sqrt(-2)), while the unit 3 + 2 sqrt(2) lies in Q(sqrt(2)).  The two fields are reported
separately; which integer orbits survive is decided by the finite quotient of the unit action
(FilteredPell.lean), not by the root action.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd, isqrt

from .arith import divisors, factorint
from .factor import factor_squarefree
from .polyalg import degree, poly, squarefree_decomposition


def _is_rational_square(q: Fraction) -> bool:
    if q < 0:
        return False
    n, d = q.numerator, q.denominator
    return isqrt(n) ** 2 == n and isqrt(d) ** 2 == d


def _squarefree_kernel(q) -> int:
    """The squarefree integer D with Q(sqrt(q)) = Q(sqrt(D))."""
    q = Fraction(q)
    n = q.numerator * q.denominator
    sign = -1 if n < 0 else 1
    out = 1
    for p_, e in factorint(abs(n)).items():
        if e % 2:
            out *= p_
    return sign * out


def _field(q) -> str:
    D = _squarefree_kernel(q)
    return 'Q' if D == 1 else f'Q(sqrt({D}))'


def _rational_roots(p) -> list[Fraction]:
    """Rational roots of a rational polynomial (rational root theorem)."""
    p = [Fraction(c) for c in p]
    L = 1
    for c in p:
        L = L * c.denominator // gcd(L, c.denominator)
    q = [int(c * L) for c in p]
    if q[0] == 0:
        return sorted(set([Fraction(0)] + _rational_roots(q[1:])))
    out = set()
    for num in divisors(abs(q[0])):
        for den in divisors(abs(q[-1])):
            for s in (1, -1):
                x = Fraction(s * num, den)
                v = Fraction(0)
                for c in reversed(p):
                    v = v * x + c
                if v == 0:
                    out.add(x)
    return sorted(out)


def _integer_primitive(p) -> list[int]:
    p = [Fraction(c) for c in p]
    L = 1
    for c in p:
        L = L * c.denominator // gcd(L, c.denominator)
    q = [int(c * L) for c in p]
    g = 0
    for x in q:
        g = gcd(g, x)
    q = [x // g for x in q]
    return q if q[-1] > 0 else [-x for x in q]


def _disc_monic(p) -> Fraction:
    """Discriminant of a monic rational polynomial of degree 2, 3 or 4."""
    k = len(p) - 1
    if k == 2:
        c, b = p[0], p[1]
        return b * b - 4 * c
    if k == 3:
        r, q, s = p[0], p[1], p[2]
        return s * s * q * q - 4 * q ** 3 - 4 * s ** 3 * r - 27 * r * r + 18 * s * q * r
    # quartic: the discriminant of the resolvent cubic
    d, c, b, a = p[0], p[1], p[2], p[3]
    return _disc_monic([-(a * a * d - 4 * b * d + c * c), a * c - 4 * d, -b, Fraction(1)])


def _group(f_int) -> dict:
    """Galois group of an irreducible integer polynomial of degree <= 4 (or None beyond)."""
    k = len(f_int) - 1
    p = [Fraction(c, f_int[-1]) for c in f_int]
    if k == 1:
        return {'group': 'trivial'}
    disc = _disc_monic(p)
    if k == 2:
        return {'group': 'C2', 'discriminant': str(disc), 'root_field': _field(disc)}
    if k == 3:
        return {'group': 'A3' if _is_rational_square(disc) else 'S3', 'discriminant': str(disc)}
    if k == 4:
        d, c, b, a = p[0], p[1], p[2], p[3]
        res = [-(a * a * d - 4 * b * d + c * c), a * c - 4 * d, -b, Fraction(1)]
        rr = _rational_roots(res)
        sq = _is_rational_square(disc)
        if not rr:
            g = 'A4' if sq else 'S4'
        elif len(rr) == 3:
            g = 'V4'
        else:
            r = rr[0]
            # Kappe–Warren: C4 iff x^2 - r x + d and x^2 + a x + (b - r) split over Q(sqrt(disc))
            g = 'C4' if (_is_rational_square((r * r - 4 * d) * disc) and
                         _is_rational_square((a * a - 4 * (b - r)) * disc)) else 'D4'
        return {'group': g, 'discriminant': str(disc)}
    return {'group': None, 'note': 'transitive of degree %d; group not identified' % k}


def _orbits_of(S) -> list[dict]:
    """Orbits of the roots of a squarefree rational polynomial: its irreducible factors."""
    f = _integer_primitive(S)
    factors, rest = factor_squarefree(f)
    out = []
    for g in factors:
        o = {'size': len(g) - 1, 'factor': g}
        o.update(_group(g))
        if len(g) == 2:
            o['root'] = str(Fraction(-g[0], g[1]))
        out.append(o)
    if rest:
        out.append({'size': len(rest) - 1, 'factor': rest, 'group': None,
                    'unknown': 'not factored (too many modular factors); one or more orbits'})
    return out


def _unit_fields(coefficients, d) -> list[dict]:
    """The real quadratic fields whose units move the integer solutions of each Pell branch."""
    from .arith import is_square, pell_fundamental
    from .atlas import classify
    f = [int(c) for c in coefficients]
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    if d == 2 and len(f) == 3 and f[2] > 0 and not is_square(f[2]) and f[1] ** 2 - 4 * f[2] * f[0]:
        # F itself is the branch: report the unit in F's own coordinates X = 2An + B
        C, B, A = f
        x1, y1 = pell_fundamental(4 * A)
        return [{'branch': [A, B, C], 'case': 'pell', 'unit_field': _field(A),
                 'unit': f'{x1} + {y1}*sqrt({4 * A})',
                 'norm_form': f'X^2 - {4 * A} Y^2 = {B * B - 4 * A * C}'}]
    cl = classify(coefficients, d)
    if cl.kind != 'pell':
        return []
    out = []
    for q in cl.details['quadratics']:
        row = {'branch': [q['A'], q['B'], q['C']], 'case': q['case']}
        if q['case'] == 'pell':
            x1, y1 = q['unit']
            row.update(unit_field=_field(q['A']), unit=f'{x1} + {y1}*sqrt({q["D"]})',
                       norm_form=f"X^2 - {q['D']} Y^2 = {q['Delta']}")
        else:
            row['note'] = 'bounded branch (A < 0 or A a square): no unit acts'
        out.append(row)
    return out


def galois_profile(coefficients, d: int) -> dict:
    """Root orbits with their groups, multiplicities and obstructions; for the Pell type also
    the unit fields of the branches; and the reason for the atlas type."""
    F = poly(coefficients)
    if degree(F) <= 0:
        return {'orbits': [], 'unit_fields': [], 'explanation': 'constant: no roots'}
    _, parts = squarefree_decomposition(F)
    orbits = []
    for j, S in sorted(parts.items()):
        t = d // gcd(d, j)
        for o in _orbits_of(S):
            orbits.append({**o, 'multiplicity': j, 't': t})
    bad = [o for o in orbits if o['t'] != 1]
    nbad = sum(o['size'] for o in bad)
    units = []
    if nbad == 0:
        why = 'power type: every root has t = 1, so no root obstructs; F is c * G^d'
    elif nbad == 1:
        why = ('radical type: the only obstructed root is fixed by Galois, hence rational '
               f"(alpha = {bad[0]['root']}); hits are parametrized through v n - u = z0 w^t")
    elif nbad == 2 and all(o['t'] == 2 for o in bad):
        units = _unit_fields(coefficients, d)
        moving = ', '.join(sorted({u['unit_field'] for u in units if 'unit_field' in u}))
        if len(bad) == 1 and 'root_field' in bad[0]:
            roots = f"one conjugate pair with root field {bad[0]['root_field']}"
        else:
            roots = 'both rational (the quadratic splits over Q)'
        if moving:
            action = ('The integer solutions move under a different action: the units of the '
                      f'real quadratic field {moving}, acting on the norm form of each branch')
        else:
            action = 'No unit acts: every branch is bounded (A < 0 or A a square)'
        why = f'Pell type: the two obstructed roots are {roots}. {action}'
    else:
        S = sum(Fraction(o['size']) * (1 - Fraction(1, o['t'])) for o in bad)
        why = (f'finite type: over the obstructed roots S = sum (1 - 1/t) = {S} > 1, so '
               "chi = d'(1 - S) < 0 and Siegel gives finitely many hits (Theorem G)")
    return {'orbits': orbits, 'unit_fields': units, 'explanation': why}
