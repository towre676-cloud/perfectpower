"""Certified period matrices of genus-two curves y^2=f(x), deg f in {5,6}, with complex branch points.

Branch points. f has rational coefficients; its roots are isolated rigorously by
Arb (fmpz_poly.complex_roots, real roots exact-real). A quintic is first moved to
a sextic by a rational Moebius map x=(a t+b)/(c t+d) (mobius_model), which also
records the 2x2 matrix G with (dx/y, x dx/y)=G (dt/Y, t dt/Y).

Arc. The six branch points are ordered e_1..e_6 (default: lexicographically by
(Re,Im), a monotone polyline) and joined by straight segments s_j=[e_j,e_{j+1}].
simple_arc_certificate proves in Arb that L=s_1 u...u s_5 is a simple arc.

Global branch. Y=sqrt(lc) F_1 F_3 F_5 with F_k(z)=h_k G((z-m_k)/h_k),
G(w)=w sqrt(1-1/w^2) (principal), m_k, h_k the midpoint and half-vector of s_k.
F_k is analytic on C minus s_k with F_k^2=(z-e_k)(z-e_{k+1}), so Y is a branch of
sqrt f analytic on the complement of L (infinity is not a branch point).

Cycles. gamma_j is the closed lift of the clockwise-from-the-left loop around s_j
whose left edge carries y=Y_+ (left boundary value). Its period is
2 int_{s_j} omega/Y_+. On s_j, with z=m+h u, u=-cos t,
  y_j(z) = i h sqrt(1-u^2) S_j(u),   S_j=sqrt(lc) h^2 prod_k c_k sqrt((u-u_k)/(-d_k)),
where u_k=(e_k-m)/h for the four other roots and d_k=u_k-p_k (p_k the nearest point
of [-1,1]) so each principal cut is a ray running away from the segment. Then
dz/y_j = -i dt/S_j(u(t)), analytic on a neighbourhood of [0,pi], and acb.integral
returns rigorous balls. The sign s_j=Y_+(m)/y_j(m) is certified to be +1 or -1 at
the midpoint (both are continuous square roots of f along the open segment).

Intersections. An orientation-preserving homeomorphism of the sphere sends L to
[1,6] with e_j->j, its left side to the upper half plane and Y to +-(the branch
with cuts [1,2],[3,4],[5,6]); intersection numbers are therefore those of the
model, which model_intersection_matrix computes exactly (rational polygons,
sheet bookkeeping across cuts, signed transversal crossings).
"""
from fractions import Fraction as Fr
from flint import acb, arb, arb_mat, acb_mat, fmpz_poly, ctx
from perfectpower import genus2_certified_periods as g2

ctx.prec = 200
J4 = [[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]]


# ---------------------------------------------------------------- exact algebra
def poly_mul(p, q):
    r = [Fr(0)]*(len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a*b
    return r


def poly_pow(p, n):
    r = [Fr(1)]
    for _ in range(n):
        r = poly_mul(r, p)
    return r


def mobius_model(coeffs, abcd):
    """Y^2=g(t)=(c t+d)^6 f((a t+b)/(c t+d)), Y=y (c t+d)^3. Returns (g, G) exactly.

    coeffs are f's coefficients (constant first, rational). G (2x2 Fractions) satisfies
    (dx/y, x dx/y) = G (dt/Y, t dt/Y): dx/y=D(c t+d)dt/Y, x dx/y=D(a t+b)dt/Y, D=ad-bc.
    """
    a, b, c, d = (Fr(x) for x in abcd)
    D = a*d - b*c
    if D == 0:
        raise ValueError('singular Moebius map')
    g = [Fr(0)]*7
    for k, ck in enumerate(coeffs):
        term = [Fr(ck)*x for x in poly_mul(poly_pow([b, a], k), poly_pow([d, c], 6 - k))]
        for i, x in enumerate(term):
            g[i] += x
    while len(g) > 1 and g[-1] == 0:
        g.pop()
    return g, [[D*d, D*c], [D*b, D*a]]


def integer_poly(coeffs):
    den = 1
    for c in coeffs:
        den = den*Fr(c).denominator//_gcd(den, Fr(c).denominator)
    return [int(Fr(c)*den) for c in coeffs], den


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def _q(x):
    x = Fr(x)
    return acb(x.numerator)/x.denominator


def certified_roots(coeffs):
    """Arb-isolated simple roots of a rational sextic (constant coefficient first)."""
    ints, den = integer_poly(coeffs)
    if len(ints) != 7:
        raise ValueError('need degree exactly 6 (move a quintic with mobius_model)')
    rr = fmpz_poly(ints).complex_roots()
    if any(m != 1 for _, m in rr) or len(rr) != 6:
        raise ArithmeticError('f must be squarefree')
    return [acb(r) for r, _ in rr], _q(coeffs[-1])


# ---------------------------------------------------------------- arc geometry (Arb predicates)
def _orient(a, b, c):
    """Im(conj(b-a)(c-a)): >0 iff c lies left of the directed line a->b."""
    return ((b - a).conjugate()*(c - a)).imag


def _strict_sign(x):
    return 1 if x > 0 else (-1 if x < 0 else 0)


def _boxes_separated(p, q):
    for part in ('real', 'imag'):
        pv = [getattr(z, part) for z in p]; qv = [getattr(z, part) for z in q]
        if max(pv[0].upper(), pv[1].upper()) < min(qv[0].lower(), qv[1].lower()) or \
           max(qv[0].upper(), qv[1].upper()) < min(pv[0].lower(), pv[1].lower()):
            return True
    return False


def segments_disjoint(p, q):
    """Certified: closed segments p, q are disjoint."""
    if _boxes_separated(p, q):
        return True
    s1 = [_strict_sign(_orient(p[0], p[1], c)) for c in q]
    s2 = [_strict_sign(_orient(q[0], q[1], c)) for c in p]
    return (0 not in s1 and s1[0] == s1[1]) or (0 not in s2 and s2[0] == s2[1])


def simple_arc_certificate(e):
    """Certify that the polyline e_1..e_n is a simple arc; returns the list of checks."""
    n = len(e)
    segs = [(e[j], e[j + 1]) for j in range(n - 1)]
    checks = []
    for i in range(n - 1):
        for k in range(i + 1, n - 1):
            if k == i + 1:
                a, b, c = e[i], e[i + 1], e[i + 2]
                turn = _strict_sign(_orient(a, b, c))
                dot = ((b - a).conjugate()*(c - b)).real
                ok = turn != 0 or bool(dot > 0)
                checks.append(('adjacent', i + 1, k + 1, ok))
            else:
                checks.append(('disjoint', i + 1, k + 1, segments_disjoint(segs[i], segs[k])))
    if not all(c[3] for c in checks):
        raise ArithmeticError('arc not certified simple: %s' % [c for c in checks if not c[3]])
    return checks


def order_roots(roots, key='re_im'):
    if key == 're_im':
        f = lambda z: (float(z.real.mid()), float(z.imag.mid()))
    elif key == 'im_re':
        f = lambda z: (float(z.imag.mid()), float(z.real.mid()))
    else:
        raise ValueError(key)
    return sorted(roots, key=f)


# ---------------------------------------------------------------- branches
def _G(w):
    return w*(1 - 1/(w*w)).sqrt(analytic=True)


def global_branch(e, lc, z, left_of=None):
    """Y(z)=sqrt(lc) F_1 F_3 F_5(z) off L; with left_of=j (odd) the factor F_j is its left boundary value at the midpoint."""
    val = lc.sqrt()
    for k in (0, 2, 4):
        a, b = e[k], e[k + 1]
        m, h = (a + b)/2, (b - a)/2
        if left_of == k:
            val *= h*acb(0, 1)  # G_+(0)=i
        else:
            val *= h*_G((z - m)/h)
    if not val.is_finite():
        raise ArithmeticError('global branch evaluated on its cut')
    return val


class Segment:
    """Local branch y_j of sqrt f on the open segment [e_j, e_{j+1}]."""

    def __init__(self, e, lc, j):
        self.j, self.lc = j, lc
        self.a, self.b = e[j], e[j + 1]
        self.m, self.h = (self.a + self.b)/2, (self.b - self.a)/2
        self.uk = [(e[k] - self.m)/self.h for k in range(6) if k not in (j, j + 1)]
        self.dirs = []
        for u in self.uk:
            x, y = float(u.real.mid()), float(u.imag.mid())
            p = min(1., max(-1., x))
            self.dirs.append(-acb(x - p, y))  # cut of sqrt(v/dir) is the ray u_k + s(u_k-p_k)
        self.sq = lc.sqrt()*self.h**2

    def S(self, u):
        v = self.sq
        for uk, dk in zip(self.uk, self.dirs):
            v *= dk.sqrt()*((u - uk)/dk).sqrt(analytic=True)
        return v

    def y_mid(self):
        return acb(0, 1)*self.h*self.S(acb(0))

    def integral(self, power):
        """int_{e_j}^{e_{j+1}} z^power dz/y_j = -i int_0^pi z(t)^power / S(u(t)) dt."""
        m, h = self.m, self.h

        def f(t, analytic):
            u = -t.cos()
            return (m + h*u)**power/self.S(u)
        return acb(0, -1)*acb.integral(f, 0, arb.pi())


def branch_sign(e, lc, seg):
    """s_j with Y_+ = s_j y_j on the open segment, certified at the midpoint."""
    Yp = global_branch(e, lc, seg.m, left_of=seg.j if seg.j % 2 == 0 else None)
    r = Yp/seg.y_mid()
    for s in (1, -1):
        if (r - s).contains(0) and not (r + s).contains(0):
            return s, r
    raise ArithmeticError('branch sign not certified: %s' % r)


# ---------------------------------------------------------------- exact combinatorial intersection numbers
def _rect(j):
    """Clockwise rectangle around model segment [j, j+1] (1-based points 1..6), as a vertex list."""
    H = Fr(1, 2) if j % 2 else Fr(1, 4)
    x0, x1 = Fr(j) - Fr(1, 3), Fr(j + 1) + Fr(1, 3)
    return [(x0, H), (x1, H), (x1, -H), (x0, -H)]


def _edges_with_sheets(poly, cuts):
    """Edges of a closed polygon with the sheet (+1/-1) on each piece; start on the top edge, sheet +1."""
    out = []
    sheet = 1
    n = len(poly)
    for i in range(n):
        p, q = poly[i], poly[(i + 1) % n]
        # vertical edges cross the real axis once, at x=p[0]
        if p[0] == q[0] and (p[1] > 0) != (q[1] > 0):
            x = p[0]
            out.append((p, (x, Fr(0)), sheet))
            if any(c0 < x < c1 for c0, c1 in cuts):
                sheet = -sheet
            out.append(((x, Fr(0)), q, sheet))
        else:
            out.append((p, q, sheet))
    if sheet != 1:
        raise ArithmeticError('lift is not closed')
    return out


def _cross(p, q, r, s):
    """Transversal intersection point parameters of segments pq and rs (exact), or None."""
    d1 = (q[0] - p[0], q[1] - p[1]); d2 = (s[0] - r[0], s[1] - r[1])
    den = d1[0]*d2[1] - d1[1]*d2[0]
    if den == 0:
        return None
    t = ((r[0] - p[0])*d2[1] - (r[1] - p[1])*d2[0])/den
    u = ((r[0] - p[0])*d1[1] - (r[1] - p[1])*d1[0])/den
    if 0 < t < 1 and 0 < u < 1:
        return den
    if 0 <= t <= 1 and 0 <= u <= 1:
        raise ArithmeticError('non-generic crossing')
    return None


def model_intersection_matrix(n=6):
    """Exact intersection numbers of gamma_1..gamma_{n-1} on the model y^2=prod_{k=1}^n (x-k).

    Cuts of the global branch: [1,2],[3,4],[5,6]. gamma_j is the clockwise rectangle
    around [j,j+1] starting on sheet + on its top edge. Two lifts meet at a planar
    crossing only when their sheets agree; the local index is the sign of
    det(tangent_1, tangent_2).
    """
    cuts = [(Fr(k), Fr(k + 1)) for k in range(1, n, 2)]
    lifts = [_edges_with_sheets(_rect(j), cuts) for j in range(1, n)]
    M = [[0]*(n - 1) for _ in range(n - 1)]
    for i in range(n - 1):
        for k in range(n - 1):
            if i == k:
                continue
            tot = 0
            for p, q, s1 in lifts[i]:
                for r, s, s2 in lifts[k]:
                    den = _cross(p, q, r, s)
                    if den is not None and s1 == s2:
                        tot += 1 if den > 0 else -1
            M[i][k] = tot
    return M


def symplectic_basis(C):
    """Integral symplectic reduction: rows a_1..a_g, b_1..b_g (integer vectors) with T C T^t = J."""
    n = len(C)
    dot = lambda v, w: sum(v[i]*C[i][k]*w[k] for i in range(n) for k in range(n))
    rest = [[int(i == k) for k in range(n)] for i in range(n)]
    A, B = [], []
    while rest:
        v = rest.pop(0)
        idx = next((i for i, w in enumerate(rest) if abs(dot(v, w)) == 1), None)
        if idx is None:
            raise ArithmeticError('form not unimodular on the remaining span')
        w = rest.pop(idx)
        if dot(v, w) == -1:
            w = [-x for x in w]
        rest = [[x - dot(u, w)*a + dot(u, v)*b for x, a, b in zip(u, v, w)] for u in rest]
        A.append(v); B.append(w)
    T = A + B
    TCT = [[dot(T[i], T[k]) for k in range(n)] for i in range(n)]
    g = n//2
    Jn = [[(1 if k == i + g else -1 if i == k + g else 0) for k in range(n)] for i in range(n)]
    if TCT != Jn:
        raise ArithmeticError('symplectic reduction failed')
    return T


# ---------------------------------------------------------------- period matrices
def curve_periods(roots, lc, order='re_im', G=None, basis=None, sign_flip=None):
    """Certified periods over gamma_1..gamma_5 and the normalised period matrix.

    roots: six acb balls; lc: leading coefficient. G optionally maps (dt/Y, t dt/Y)
    to another differential basis (the forms of the original model). basis: rows
    of integer coefficients on gamma_1..gamma_4 (default: symplectic_basis of the
    certified intersection matrix).
    """
    e = order_roots(roots, order)
    arc = simple_arc_certificate(e)
    C5 = model_intersection_matrix()
    if C5 != g2.chain_intersection(1):
        raise ArithmeticError('model intersection matrix is not the chain')
    C = [row[:4] for row in C5[:4]]
    T = basis or symplectic_basis(C)
    P = [[None]*5 for _ in range(2)]
    signs = []
    for j in range(5):
        seg = Segment(e, lc, j)
        s, _ = branch_sign(e, lc, seg)
        signs.append(s)
        if sign_flip == j:  # negative control only: deliberately wrong sheet on one segment
            s = -s
        for p in (0, 1):
            P[p][j] = 2*s*seg.integral(p)
    if G is not None:
        P = [[_q(G[r][0])*P[0][j] + _q(G[r][1])*P[1][j] for j in range(5)] for r in (0, 1)]
    Pi = [[sum((c*P[r][j] for j, c in enumerate(row)), acb(0)) for row in T] for r in (0, 1)]
    A = acb_mat([Pi[r][:2] for r in (0, 1)]); B = acb_mat([Pi[r][2:] for r in (0, 1)])
    Om = A.solve(B)
    im = [[Om[i, k].imag for k in range(2)] for i in range(2)]
    return {'roots': e, 'arc_checks': arc, 'signs': signs, 'cycle_periods': P, 'intersection': C5,
            'basis': T, 'Pi': Pi, 'Omega': Om, 'symmetry_defect': Om[0, 1] - Om[1, 0],
            'Im_trace': im[0][0] + im[1][1], 'Im_det': im[0][0]*im[1][1] - im[0][1]*im[1][0],
            'relation_135': [P[r][0] + P[r][2] + P[r][4] for r in (0, 1)]}


def riemann_certified(pm):
    return bool(pm['symmetry_defect'].contains(0) and pm['Im_trace'] > 0 and pm['Im_det'] > 0)


def periods_of_polynomial(coeffs, order='re_im', mobius=None, basis=None, sign_flip=None):
    """Sextic or quintic with rational coefficients; a quintic needs a Moebius map moving infinity."""
    G = None
    deg = max(i for i, c in enumerate(coeffs) if c != 0)
    if mobius is not None:
        coeffs, G = mobius_model(coeffs, mobius)
    elif deg == 5:
        raise ValueError('quintic: pass mobius=(a,b,c,d) with f(a/c) != 0')
    roots, lc = certified_roots(coeffs)
    return curve_periods(roots, lc, order=order, G=G, basis=basis, sign_flip=sign_flip)


def _realify(Pi):
    return arb_mat([[x.real for x in Pi[0]], [x.real for x in Pi[1]], [x.imag for x in Pi[0]], [x.imag for x in Pi[1]]])


def integral_relation(Pi1, Pi2):
    """Certify the unique integer 4x4 M with Pi2 = Pi1 M (period lattices); M must be symplectic.

    Returns (M, max entry radius, symplectic flag). Raises if an entry interval holds no or two integers.
    """
    X = _realify(Pi1).solve(_realify(Pi2))
    M, rad = [], arb(0)
    for i in range(4):
        row = []
        for k in range(4):
            x = X[i, k]
            lo, hi = x.lower(), x.upper()
            c = [n for n in range(int(lo.floor().unique_fmpz()), int(hi.ceil().unique_fmpz()) + 1) if lo <= n <= hi]
            if len(c) != 1 or hi - lo >= 1:
                raise ArithmeticError('integer entry not certified: %s' % x)
            row.append(c[0]); rad = max(rad, x.rad())
        M.append(row)
    MtJM = [[sum(M[a][i]*J4[a][b]*M[b][k] for a in range(4) for b in range(4)) for k in range(4)] for i in range(4)]
    return M, rad, MtJM == J4


def apply_matrix(Pi, M):
    return [[sum((Pi[r][i]*M[i][k] for i in range(4)), acb(0)) for k in range(4)] for r in (0, 1)]


def omega_of(Pi):
    return acb_mat([Pi[r][:2] for r in (0, 1)]).solve(acb_mat([Pi[r][2:] for r in (0, 1)]))


def int_matpow(M, k):
    n = len(M)
    R = [[int(i == j) for j in range(n)] for i in range(n)]
    for _ in range(k):
        R = [[sum(R[i][a]*M[a][j] for a in range(n)) for j in range(n)] for i in range(n)]
    return R


def int_charpoly(M):
    """Characteristic polynomial of an integer 4x4 matrix (Faddeev-LeVerrier, exact), constant first."""
    n = len(M)
    c = [Fr(0)]*(n + 1); c[n] = Fr(1)
    Mk = [[Fr(0)]*n for _ in range(n)]
    I = [[Fr(int(i == j)) for j in range(n)] for i in range(n)]
    for k in range(1, n + 1):
        Mk = [[sum(Fr(M[i][a])*(Mk[a][j] + c[n - k + 1]*I[a][j]) for a in range(n)) for j in range(n)] for i in range(n)]
        c[n - k] = -sum(Mk[i][i] for i in range(n))/k
    return [int(x) for x in c]


def automorphism_action(pm, D):
    """Integral symplectic M with D Pi = Pi M, for an automorphism acting on the forms by the diagonal D."""
    Pi2 = [[acb(D[r])*x for x in pm['Pi'][r]] for r in (0, 1)]
    return integral_relation(pm['Pi'], Pi2)


def matrices_close(A, B):
    return all((A[i, k] - B[i, k]).contains(0) for i in range(2) for k in range(2))


def siegel_fixed_points(M):
    """Exact symmetric solutions of (M11+W M21) W = M12 + W M22 (fixed points of M), via sympy.

    Returns the list of solutions (p,q,r) for W=[[p,q],[q,r]] and those with Im W positive definite.
    """
    import sympy as sp
    p, q, r = sp.symbols('p q r')
    W = sp.Matrix([[p, q], [q, r]])
    Mm = sp.Matrix(M)
    A, B, C, D = Mm[:2, :2], Mm[:2, 2:], Mm[2:, :2], Mm[2:, 2:]
    eqs = list((A + W*C)*W - (B + W*D))
    sols = sp.solve(eqs, [p, q, r], dict=True)
    good = []
    for s in sols:
        Wn = W.subs(s)
        im = Wn.applyfunc(lambda z: sp.im(sp.nsimplify(z)))
        if sp.simplify(im[0, 0]) > 0 and sp.simplify(im.det()) > 0:
            good.append(tuple(sp.nsimplify(Wn[i]) for i in (0, 1, 3)))
    return sols, good
