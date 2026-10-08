"""Topological replay of the t-adic inertia action through the branch braid.

For y^2=c(t) prod(x-r_i(t)) with Puiseux roots r_i in Q[t^(1/2),t^(-1/2)], the
generator of inertia of Q((t)) acts on H^1 as the monodromy of a small loop
around t=0.  The loop radius is chosen below an exact (Cauchy) lower bound for
every other collision; the braid word is read from floating root positions by
crossing detection, and the symplectic matrix is the exact integral product of
Picard-Lefschetz twists of marked_curve_topology.braid_monodromy, multiplied
by (-1)^v(c) for the winding of the leading coefficient.  The braid extraction
is numerical (checked by refinement agreement); the matrix algebra is exact.
"""
import cmath
import math
from fractions import Fraction as Q
from .cluster_stable_reduction import PuiseuxDomain, rank
from .marked_curve_topology import braid_monodromy


def _cauchy_lower(coeffs):
    """Exact lower bound for the nonzero roots of sum c_k u^k (c_0 the lowest nonzero)."""
    c = [abs(Q(a)) for a in coeffs]
    while c and not c[0]:
        c.pop(0)
    if len(c) <= 1:
        return None
    return c[0] / (c[0] + max(c[1:]))


def safe_radius(roots, leading):
    """Radius in s=t^(1/2) inside which t=0 is the only collision or zero of c."""
    D = PuiseuxDomain()
    rs = [D.parse(r) for r in roots]
    bounds = []
    for i in range(len(rs)):
        for j in range(i + 1, len(rs)):
            d = dict(D.sub(rs[i], rs[j]))
            lo = min(d)
            span = int(2 * (max(d) - lo))
            poly = [d.get(lo + Q(k, 2), Q(0)) for k in range(span + 1)]
            b = _cauchy_lower(poly)
            if b is not None:
                bounds.append(b)
    c = dict(D.parse(leading))
    lo = min(c)
    poly = [c.get(lo + k, Q(0)) for k in range(int(max(c) - lo) + 1)]
    b = _cauchy_lower(poly)
    if b is not None:
        # |t|>=b  <=>  |s|>=sqrt(b); use a rational under-approximation
        bounds.append(Q(math.isqrt(int(b * 10**12)), 10**6))
    rho = min(bounds) if bounds else Q(1)
    return min(rho / 2, Q(1, 2))


def _evaluate(root, s):
    return sum(float(a) * s ** int(2 * e) for e, a in root)


def braid_word(roots, radius, samples=2048, angle=0.6180339887, bend=0.3183098862):
    D = PuiseuxDomain()
    rs = [D.parse(r) for r in roots]
    R = float(radius)
    rot = cmath.exp(-1j * angle)

    def pos(theta):
        s = R * cmath.exp(0.5j * theta)
        # rotation followed by the shear (u,v)->(u+bend*v^2,v): a plane
        # diffeomorphism, so reading the order along u is still a valid braid
        # projection, while rigidly collinear root triples stop aligning.
        out = []
        for r in rs:
            w = _evaluate(r, s) * rot
            out.append(complex(w.real + bend * w.imag * w.imag, w.imag))
        return out

    def order(theta):
        w = pos(theta)
        return sorted(range(len(w)), key=lambda k: w[k].real)

    word = []

    def walk(a, b, oa, ob, depth):
        if oa == ob:
            return
        diff = [k for k in range(len(oa)) if oa[k] != ob[k]]
        pairs = [diff[i:i + 2] for i in range(0, len(diff), 2)]
        if all(len(q) == 2 and q[1] == q[0] + 1 and oa[q[0]] == ob[q[1]] and oa[q[1]] == ob[q[0]] for q in pairs):
            # disjoint adjacent transpositions commute (simultaneous only by symmetry)
            for k, _ in pairs:
                left, right = oa[k], oa[k + 1]
                lo, hi = a, b
                for _ in range(60):
                    mid = (lo + hi) / 2
                    w = pos(mid)
                    if (w[left].real - w[right].real) < 0:
                        lo = mid
                    else:
                        hi = mid
                w = pos((lo + hi) / 2)
                word.append((k + 1) if w[left].imag > w[right].imag else -(k + 1))
            return
        if depth > 50:
            raise ArithmeticError('crossing resolution failed')
        m = (a + b) / 2
        om = order(m)
        walk(a, m, oa, om, depth + 1)
        walk(m, b, om, ob, depth + 1)

    thetas = [2 * math.pi * k / samples for k in range(samples + 1)]
    prev = order(thetas[0])
    for a, b in zip(thetas, thetas[1:]):
        cur = order(b)
        walk(a, b, prev, cur, 0)
        prev = cur
    return word


def free_reduce(word):
    out = []
    for x in word:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def _mat_mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]


def topological_inertia(roots, leading=1, samples=2048):
    D = PuiseuxDomain()
    n = len(roots)
    g = (n - 1) // 2
    if not 3 <= n <= 10:
        raise ValueError('3 through 10 roots (genus at most 4) required')
    radius = safe_radius(roots, leading)
    vc = D.lead_v(leading)
    sign = -1 if vc % 2 else 1
    runs = []
    for angle, bend, k in ((0.6180339887, 0.3183098862, 1), (0.6180339887, 0.3183098862, 2), (1.1415926535, -0.2718281828, 1)):
        word = free_reduce(braid_word(roots, radius, samples * k, angle, bend))
        T = [[sign * x for x in row] for row in braid_monodromy(g, word)['matrix']]
        runs.append((word, T, _invariants(T, g)))
    if runs[0][1] != runs[1][1]:
        raise ArithmeticError('monodromy matrix not stable under refinement')
    if runs[0][2] != runs[2][2]:
        raise ArithmeticError('conjugacy invariants differ between projections')
    word, T, (inv, m, tpot) = runs[0]
    return dict(schema='pp-cluster-braid-monodromy/1', genus=g, loop_radius_s=str(radius),
                braid_word=word, leading_winding=int(vc), monodromy=T,
                invariant_dimension=inv, topological_conductor=2 * g - inv,
                semisimple_order=m, potential_toric_rank=tpot,
                second_projection_word=runs[2][0],
                scope='numerically read braid words (matrix stable under refinement, invariants stable under a second projection) on an exactly bounded loop; exact integral monodromy')


def _invariants(T, g):
    N = 2 * g
    I = [[int(i == j) for j in range(N)] for i in range(N)]
    inv = N - rank([[T[i][j] - I[i][j] for j in range(N)] for i in range(N)])
    P, m = T, 1
    while True:
        A = [[P[i][j] - I[i][j] for j in range(N)] for i in range(N)]
        if not any(any(row) for row in _mat_mul(A, A)):
            break
        m += 1
        if m > 60:
            raise AssertionError('monodromy not quasi-unipotent within bound')
        P = _mat_mul(P, T)
    return inv, m, rank(A)
