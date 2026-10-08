"""Arb-certified continuation of Fuchsian connections and the Legendre Gauss-Manin system.

System.  A(t)=sum_k R_k/(t-a_k), rational poles a_k, exact rational residues R_k;
solutions are column vectors with Y'=A Y.  For the Legendre family
y^2=x(x-1)(x-t) and the period vector (int dx/y, int x dx/y) the connection of
curve_families gives R_0=[[0,-1/2],[0,0]] (nilpotent), R_1=[[-1/2,1/2],[-1/2,1/2]]
(nilpotent) and residue -(R_0+R_1)=[[1/2,0],[1/2,-1/2]] at infinity, whose
eigenvalues +-1/2 differ by the positive integer 1 (positive resonance).

Regular steps.  At a Gaussian-rational centre c the Taylor coefficients of the
fundamental matrix with Y(c)=I follow q(c+z)Y'=M(c+z)Y, q=prod(t-a_k), computed in
Arb.  The omitted tail is bounded by the Cauchy majorant: with rho<=min|c-a_k|
and kappa=sum ||R_k|| (infinity norm), ||Y_n||<=(kappa)_n/n! rho^-n, so for
|z|<=r the tail beyond N is at most T_N/(1-theta), T_N=(kappa)_N/N! x^N,
x=r/rho, theta=max(1,(kappa+N)/(N+1)) x<1.  Each step has |z|<=dist/3.

Singular charts.  In a local coordinate s with sY'=(R+E s/(1-sigma s))Y the
Frobenius vectors s^rho sum s^n (y_n+z_n log s) satisfy the exact two-term block
recurrence ((n+rho)-R)z_n=(F+sigma(n-1+rho))z_{n-1},
((n+rho)-R)y_n=(F+sigma(n-1+rho))y_{n-1}+sigma z_{n-1}-z_n, F=E-sigma R.
Coefficients are exact rationals.  At a positive resonance (eigenvalue gap
m>=1) the log coefficient c is the unique rational making the order-m block
consistent.  The tail beyond N obeys w_n<=Qbar w_{n-1} for w=||y||+||z||, an
explicit exact rational bound proved in the monograph.

Periods.  Pi(t0)=[P_A,P_B] uses the classical Euler integrals
P_A=(2 pi F(t), .), P_B=(2 pi i F(1-t), .), F=2F1(1/2,1/2;1;.), evaluated by Arb's
rigorous acb.hypgeom_2f1; the second row follows from the connection.  The
classical identities, the topological integrality premise (monodromy preserves
H_1(E,Z), A and B a Z-basis) and this Python/Arb execution are not Lean checked.
"""
from fractions import Fraction as Q
from math import ceil, isqrt
from flint import arb, acb, acb_mat, ctx, fmpq

SCHEMA = 'pp-legendre-certified-connection/1'


# ---------- exact helpers ----------

def _q(x):
    return x if isinstance(x, Q) else Q(x)


def _g(z):
    """Gaussian rational (re, im)."""
    if isinstance(z, (tuple, list)):
        return (_q(z[0]), _q(z[1]))
    return (_q(z), Q(0))


def _gsub(a, b): return (a[0]-b[0], a[1]-b[1])
def _gadd(a, b): return (a[0]+b[0], a[1]+b[1])
def _gmul(a, b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def _gscale(a, c): return (a[0]*c, a[1]*c)
def _gabs2(a): return a[0]*a[0]+a[1]*a[1]


def _qa(x):
    x = _q(x)
    return arb(fmpq(x.numerator, x.denominator))


def _ca(z):
    z = _g(z)
    return acb(_qa(z[0]), _qa(z[1]))


def _mnorm(M):
    """Exact infinity norm of a rational matrix."""
    return max(sum(abs(_q(x)) for x in row) for row in M)


def _vnorm(v):
    return max(abs(x) for x in v)


def _mv(M, v):
    return [sum(M[i][j]*v[j] for j in range(len(v))) for i in range(len(M))]


def _solve2(M, b):
    det = M[0][0]*M[1][1]-M[0][1]*M[1][0]
    if det == 0:
        raise ZeroDivisionError('singular block')
    return [(b[0]*M[1][1]-M[0][1]*b[1])/det, (M[0][0]*b[1]-M[1][0]*b[0])/det]


def _shift(R, x):
    """x*I - R."""
    return [[(x if i == j else 0)-R[i][j] for j in range(2)] for i in range(2)]


def _ball_error(eps):
    """acb ball containing every complex number of modulus <= eps (eps an arb)."""
    u = eps.upper()
    e = (-u).union(u)
    return acb(e, e)


def _mat_add_error(M, eps):
    e = _ball_error(eps)
    n = M.nrows()
    return acb_mat([[M[i, j]+e for j in range(n)] for i in range(n)])


def ball_text(z, digits=30):
    if isinstance(z, acb):
        return [z.real.str(digits, radius=True), z.imag.str(digits, radius=True)]
    return z.str(digits, radius=True)


def mat_text(M, digits=30):
    return [[ball_text(M[i, j], digits) for j in range(M.ncols())] for i in range(M.nrows())]


def max_radius(M):
    r = arb(0)
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            r = r.max(M[i, j].real.rad()).max(M[i, j].imag.rad())
    return r


# ---------- Fuchsian system ----------

class FuchsianSystem:
    def __init__(self, poles, residues):
        self.poles = [_q(a) for a in poles]
        self.residues = [[[_q(x) for x in row] for row in R] for R in residues]
        if len(set(self.poles)) != len(self.poles) or len(self.poles) != len(self.residues) or not self.poles:
            raise ValueError('distinct rational poles with one residue each required')
        self.n = len(self.residues[0])
        self.kappa = sum(_mnorm(R) for R in self.residues)

    def residue_at_infinity(self):
        n = self.n
        return [[-sum(R[i][j] for R in self.residues) for j in range(n)] for i in range(n)]

    def matrix(self, t):
        """Exact A(t) at a Gaussian rational point."""
        t = _g(t)
        out = [[(Q(0), Q(0))]*self.n for _ in range(self.n)]
        for a, R in zip(self.poles, self.residues):
            d = _gsub(t, (a, Q(0)))
            den = _gabs2(d)
            inv = (d[0]/den, -d[1]/den)
            out = [[_gadd(out[i][j], _gscale(inv, R[i][j])) for j in range(self.n)] for i in range(self.n)]
        return out

    def distance2(self, c):
        """Exact squared distance from c to the nearest pole."""
        c = _g(c)
        return min(_gabs2(_gsub(c, (a, Q(0)))) for a in self.poles)

    def segment_distance2(self, u, v):
        """Exact squared distance from segment [u,v] to the nearest pole."""
        u, v = _g(u), _g(v)
        d = _gsub(v, u)
        best = None
        for a in self.poles:
            w = _gsub((a, Q(0)), u)
            L = _gabs2(d)
            s = (w[0]*d[0]+w[1]*d[1])/L if L else Q(0)
            s = min(max(s, Q(0)), Q(1))
            p = _gadd(u, _gscale(d, s))
            dist = _gabs2(_gsub(p, (a, Q(0))))
            best = dist if best is None else min(best, dist)
        return best

    def _local_polynomials(self, c):
        """Exact Gaussian coefficients of q(c+z) and M(c+z), ascending in z."""
        c = _g(c)

        def pmul(p, r):
            out = [(Q(0), Q(0))]*(len(p)+len(r)-1)
            for i, x in enumerate(p):
                for j, y in enumerate(r):
                    out[i+j] = _gadd(out[i+j], _gmul(x, y))
            return out
        lin = [[_gsub(c, (a, Q(0))), (Q(1), Q(0))] for a in self.poles]
        q = [(Q(1), Q(0))]
        for L in lin:
            q = pmul(q, L)
        K = len(self.poles)
        M = [[[(Q(0), Q(0))]*K for _ in range(self.n)] for _ in range(self.n)]
        for k, R in enumerate(self.residues):
            other = [(Q(1), Q(0))]
            for l, L in enumerate(lin):
                if l != k:
                    other = pmul(other, L)
            for i in range(self.n):
                for j in range(self.n):
                    for d, x in enumerate(other):
                        M[i][j][d] = _gadd(M[i][j][d], _gscale(x, R[i][j]))
        return q, M

    def taylor_step(self, c, h, target_bits):
        """Certified transition matrix from c to c+h (Gaussian rationals)."""
        c, h = _g(c), _g(h)
        rho2 = self.distance2(c)
        if 9*_gabs2(h) > rho2:
            raise ValueError('step longer than one third of the pole distance')
        q, M = self._local_polynomials(c)
        n = self.n
        qa = [_ca(x) for x in q]
        Ma = [acb_mat([[_ca(M[i][j][d]) for j in range(n)] for i in range(n)]) for d in range(len(q)-1)]
        # x = |h|/rho <= 1/3; use exact upper bound via squares
        x = (_qa(_gabs2(h))/_qa(rho2)).sqrt()
        kappa = _qa(self.kappa)
        Ys = [acb_mat([[1 if i == j else 0 for j in range(n)] for i in range(n)])]
        term = arb(1)  # (kappa)_N/N! x^N
        N = 0
        limit = arb(2)**(-target_bits)
        while True:
            # term for current N, then bound
            theta = (kappa+N).max(arb(N+1))/(N+1)*x
            if N >= 8 and theta.upper() < 1:
                bound = term/(1-theta)
                if bound.upper() < limit:
                    break
            m = len(Ys)-1  # compute Y_{m+1}
            acc = acb_mat(n, n)
            for d, Md in enumerate(Ma):
                if m-d >= 0:
                    acc += Md*Ys[m-d]
            for d in range(1, len(qa)):
                k = m+1-d
                if k >= 0:
                    acc -= qa[d]*k*Ys[k]
            Ys.append(acc*(1/(qa[0]*(m+1))))
            term = term*(kappa+N)/(N+1)*x
            N += 1
            if N > 4000:
                raise ValueError('Taylor order limit')
        hh = _ca(h)
        T = acb_mat(n, n)
        for Y in reversed(Ys[:N]):
            T = T*hh+Y
        return _mat_add_error(T, bound), N, bound

    def transport(self, path, target_bits=110):
        """Certified transition matrix along a polygon of Gaussian-rational vertices."""
        pts = [_g(p) for p in path]
        n = self.n
        T = acb_mat([[1 if i == j else 0 for j in range(n)] for i in range(n)])
        steps = []
        worst = None
        for u, v in zip(pts, pts[1:]):
            d2 = self.segment_distance2(u, v)
            if d2 == 0:
                raise ValueError('path segment meets a pole')
            L2 = _gabs2(_gsub(v, u))
            k = max(1, ceil(3*(float(L2)/float(d2))**0.5))
            while 9*L2 > d2*k*k:
                k += 1
            h = _gscale(_gsub(v, u), Q(1, k))
            for j in range(k):
                c = _gadd(u, _gscale(h, Q(j)))
                S, N, bound = self.taylor_step(c, h, target_bits)
                T = S*T
                steps.append(N)
                worst = bound.upper() if worst is None else worst.max(bound.upper())
        return T, dict(steps=len(steps), max_order=max(steps), min_order=min(steps),
                       max_step_tail=worst.upper().str(3))


def from_family(family):
    """Exact partial fractions of a CurveFamily connection with simple rational poles."""
    import sympy
    t = sympy.Symbol('t')
    n = family.dimension
    entries = [[(list(map(Q, a.n)), list(map(Q, a.d))) for a in row] for row in family.connection]
    poles = set()
    for row in entries:
        for num, den in row:
            if not any(num):
                continue
            dn = max(i for i, c in enumerate(num) if c)
            dd = max(i for i, c in enumerate(den) if c)
            if dn >= dd:
                raise ValueError('polynomial part present')
            D = sympy.Poly(list(reversed([sympy.Rational(x.numerator, x.denominator) for x in den])), t)
            rts = sympy.roots(D, filter='Q')
            if sum(rts.values()) != D.degree() or any(m != 1 for m in rts.values()):
                raise ValueError('connection denominator needs simple rational roots')
            poles |= {Q(int(r.p), int(r.q)) for r in rts}
    poles = sorted(poles)
    residues = []
    for a in poles:
        R = []
        for row in entries:
            out = []
            for num, den in row:
                pa = sum(c*a**i for i, c in enumerate(num))
                dd = [i*c for i, c in enumerate(den)][1:]
                da = sum(c*a**i for i, c in enumerate(dd))
                if sum(c*a**i for i, c in enumerate(den)) != 0:
                    out.append(Q(0))
                else:
                    out.append(pa/da)
            R.append(out)
        residues.append(R)
    system = FuchsianSystem(poles, residues)
    # exact identity check at several rational points
    for x in (Q(1, 3), Q(-2, 7), Q(5, 2), Q(11, 13)):
        A = system.matrix(x)
        for i in range(n):
            for j in range(n):
                num, den = entries[i][j]
                v = sum(c*x**k for k, c in enumerate(num))/sum(c*x**k for k, c in enumerate(den))
                if A[i][j] != (v, Q(0)):
                    raise ValueError('connection is not of the simple-pole partial-fraction form')
    return system


LEGENDRE_R0 = [[Q(0), Q(-1, 2)], [Q(0), Q(0)]]
LEGENDRE_R1 = [[Q(-1, 2), Q(1, 2)], [Q(-1, 2), Q(1, 2)]]


def certified_transport(family, path, prec=128, target_bits=100):
    """Arb-certified analogue of family_continuation.transport for simple-pole connections."""
    old = ctx.prec
    ctx.prec = prec
    try:
        S = from_family(family)
        T, info = S.transport(path, target_bits)
        return dict(schema='pp-certified-family-transport/1', poles=[str(a) for a in S.poles],
                    residues=[[_encv(r) for r in R] for R in S.residues], path=[[str(_g(p)[0]), str(_g(p)[1])] for p in path],
                    transfer_matrix=mat_text(T, 25), max_radius=ball_text(max_radius(T), 6), **info,
                    certified_error_bound=True, closed_parameter_path=_g(path[0]) == _g(path[-1]),
                    scope='Arb ball for the de Rham-basis transfer matrix; tails by Cauchy majorants; no cycle marking'), T
    finally:
        ctx.prec = old


def legendre_system():
    return FuchsianSystem([0, 1], [LEGENDRE_R0, LEGENDRE_R1])


# ---------- Frobenius charts ----------

def _eigen(R):
    """Rational eigenvalues (hi, lo) and eigenvectors of a 2x2 rational matrix."""
    tr = R[0][0]+R[1][1]
    det = R[0][0]*R[1][1]-R[0][1]*R[1][0]
    disc = tr*tr-4*det
    if disc < 0:
        raise ValueError('rational real eigenvalues required')
    num, den = disc.numerator, disc.denominator
    rn, rd = isqrt(num), isqrt(den)
    if rn*rn != num or rd*rd != den:
        raise ValueError('rational eigenvalues required')
    s = Q(rn, rd)
    return (tr+s)/2, (tr-s)/2


def _kernel(M):
    """A nonzero rational kernel vector of a singular nonzero-or-zero 2x2 matrix."""
    if M[0][0] or M[0][1]:
        v = [-M[0][1], M[0][0]]
    elif M[1][0] or M[1][1]:
        v = [-M[1][1], M[1][0]]
    else:
        return [Q(1), Q(0)]
    return v


def frobenius_chart(R, E, sigma, order):
    """Exact Frobenius basis for sY'=(R+E s/(1-sigma s))Y, 2x2, rational eigenvalues.

    Returns two solutions, each {rho, y:[...], z:[...]} with
    Y(s)=s^rho sum_{n<order} s^n (y_n + z_n log s), and the local monodromy data.
    """
    R = [[_q(x) for x in r] for r in R]
    E = [[_q(x) for x in r] for r in E]
    sigma = _q(sigma)
    F = [[E[i][j]-sigma*R[i][j] for j in range(2)] for i in range(2)]
    hi, lo = _eigen(R)
    gap = hi-lo
    zero = [Q(0), Q(0)]

    def run(rho, y0, z0, start=1, ys=None, zs=None, resonance=None):
        ys = ys or [y0]
        zs = zs or [z0]
        for n in range(start, order):
            S = _shift(R, n+rho)
            G = [[F[i][j]+(sigma*(n-1+rho) if i == j else 0) for j in range(2)] for i in range(2)]
            if resonance is not None and n == resonance[0]:
                ys.append(resonance[1])
                zs.append(resonance[2])
                continue
            z = _solve2(S, _mv(G, zs[-1])) if any(zs[-1]) else list(zero)
            rhs = [a+sigma*b-c for a, b, c in zip(_mv(G, ys[-1]), zs[-1], z)]
            ys.append(_solve2(S, rhs))
            zs.append(z)
        return ys, zs

    out = dict(R=R, E=E, sigma=sigma, F=F, eigenvalues=[hi, lo], gap=gap)
    if gap.denominator != 1:
        v = _kernel(_shift(R, hi))
        u = _kernel(_shift(R, lo))
        s1 = run(hi, v, list(zero))
        s2 = run(lo, u, list(zero))
        out.update(kind='nonresonant', solutions=[dict(rho=hi, y=s1[0], z=s1[1]), dict(rho=lo, y=s2[0], z=s2[1])],
                   log_coefficient=Q(0))
        return out
    m = int(gap)
    if m == 0:
        N = _shift(R, hi)
        N = [[-x for x in r] for r in N]  # R - hi
        if not any(x for r in N for x in r):
            s1 = run(hi, [Q(1), Q(0)], list(zero))
            s2 = run(hi, [Q(0), Q(1)], list(zero))
            out.update(kind='scalar_residue', log_coefficient=Q(0),
                       solutions=[dict(rho=hi, y=s1[0], z=s1[1]), dict(rho=hi, y=s2[0], z=s2[1])])
            return out
        w = [Q(1), Q(0)] if any(_mv(N, [Q(1), Q(0)])) else [Q(0), Q(1)]
        v = _mv(N, w)
        s1 = run(hi, v, list(zero))
        s2 = run(hi, w, v)
        out.update(kind='nilpotent_log', log_coefficient=Q(1), eigenvector=v, generalized_eigenvector=w,
                   solutions=[dict(rho=hi, y=s1[0], z=s1[1]), dict(rho=hi, y=s2[0], z=s2[1])])
        return out
    # positive resonance, gap m >= 1
    v = _kernel(_shift(R, hi))
    u = _kernel(_shift(R, lo))
    s1 = run(hi, v, list(zero))
    zs = [list(zero) for _ in range(m)]
    # prefix below the resonance: z vanishes, blocks invertible
    ys = [u]
    for n in range(1, m):
        S = _shift(R, n+lo)
        G = [[F[i][j]+(sigma*(n-1+lo) if i == j else 0) for j in range(2)] for i in range(2)]
        ys.append(_solve2(S, _mv(G, ys[-1])))
    G = [[F[i][j]+(sigma*(m-1+lo) if i == j else 0) for j in range(2)] for i in range(2)]
    b = _mv(G, ys[-1])
    # b = beta_u u + beta_v v
    det = u[0]*v[1]-u[1]*v[0]
    beta_u = (b[0]*v[1]-b[1]*v[0])/det
    beta_v = (u[0]*b[1]-u[1]*b[0])/det
    c = beta_v
    ym = [beta_u/m*x for x in u]
    zm = [c*x for x in v]
    # check the resonant block identity exactly
    S = _shift(R, hi)
    lhs = _mv(S, ym)
    rhs = [bi-zi for bi, zi in zip(b, zm)]
    if lhs != rhs or any(_mv(S, zm)):
        raise AssertionError('resonant block not consistent')
    ys2, zs2 = run(lo, None, None, start=m+1, ys=ys+[ym], zs=zs+[zm])
    # log part is exactly c times the first solution, shifted by m
    for j in range(order-m):
        if zs2[j+m] != [c*x for x in s1[0][j]]:
            raise AssertionError('log series is not c times the leading solution')
    out.update(kind='positive_resonance', resonance_order=m, log_coefficient=c, resonance_rhs=b,
               eigenvector_hi=v, eigenvector_lo=u, normalization='v-component of y_m set to zero',
               solutions=[dict(rho=hi, y=s1[0], z=s1[1]), dict(rho=lo, y=ys2, z=zs2)])
    return out


def frobenius_tail(chart, solution, r):
    """Exact rational bound on sum_{n>=N} (||y_n||+||z_n||) r^n, N=len(y)."""
    R, F, sigma = chart['R'], chart['F'], chart['sigma']
    rho = solution['rho']
    if abs(sigma) > 1:
        raise ValueError('|sigma|<=1 required by the monotone tail bound')
    ys, zs = solution['y'], solution['z']
    N = len(ys)
    nR, nF = _mnorm(R), _mnorm(F)
    D = N+rho-nR
    if D <= 0 or N-1+rho < 0:
        raise ValueError('order too small for the tail bound')
    qN = (nF+abs(sigma)*(N-1+rho))/D
    qbar = max(qN, Q(1))
    Qbar = qbar+(1+qbar)/D*max(abs(sigma), Q(1))
    r = _q(r)
    if Qbar*r >= 1:
        raise ValueError('evaluation radius too large for the tail bound')
    w = _vnorm(ys[-1])+_vnorm(zs[-1])
    return w*r**(N-1)*Qbar*r/(1-Qbar*r)


def frobenius_matrix(chart, s0, prec_tail=True):
    """Certified fundamental matrix [Y1(s0), Y2(s0)] at real rational 0<s0<1 (principal branches)."""
    s0 = _q(s0)
    if not 0 < s0 < 1:
        raise ValueError('real chart point in (0,1) required')
    sa = _qa(s0)
    L = sa.log()
    cols = []
    tails = []
    for sol in chart['solutions']:
        tail = frobenius_tail(chart, sol, s0)
        tails.append(tail)
        eps = _qa(tail)
        e = _ball_error(eps)
        Ys = [acb(0), acb(0)]
        Zs = [acb(0), acb(0)]
        for n in reversed(range(len(sol['y']))):
            for i in range(2):
                Ys[i] = Ys[i]*sa+_qa(sol['y'][n][i])
                Zs[i] = Zs[i]*sa+_qa(sol['z'][n][i])
        rho = sol['rho']
        pw = sa**_qa(rho) if rho else arb(1)
        cols.append([acb(pw)*((Ys[i]+e)+L*(Zs[i]+e)) for i in range(2)])
    return acb_mat([[cols[0][0], cols[1][0]], [cols[0][1], cols[1][1]]]), tails


def local_monodromy(chart):
    """K with Phi -> Phi K for one counterclockwise turn of s around 0."""
    lam = chart['eigenvalues'][0]
    phase = acb(0, 2*_qa(lam)*arb.pi()).exp()
    if chart['kind'] in ('nilpotent_log', 'positive_resonance'):
        c = _qa(chart['log_coefficient'])
        off = acb(0, 2*arb.pi()*c)
        return acb_mat([[phase, phase*off], [0, phase]])
    if chart['kind'] == 'scalar_residue':
        return acb_mat([[phase, 0], [0, phase]])
    lo = chart['eigenvalues'][1]
    return acb_mat([[phase, 0], [0, acb(0, 2*_qa(lo)*arb.pi()).exp()]])


def legendre_charts(order):
    """Charts at 0 (s=t), 1 (s=1-t) and infinity (s=1/t) for the Legendre system."""
    R0, R1 = LEGENDRE_R0, LEGENDRE_R1
    neg = lambda M: [[-x for x in r] for r in M]
    Rinf = [[-(R0[i][j]+R1[i][j]) for j in range(2)] for i in range(2)]
    return {'0': frobenius_chart(R0, neg(R1), 1, order),
            '1': frobenius_chart(R1, neg(R0), 1, order),
            'infinity': frobenius_chart(Rinf, neg(R1), 1, order)}


# ---------- Legendre periods ----------

def legendre_period_matrix(t0):
    """Pi(t0)=[P_A, P_B] (columns), real rational 0<t0<1, as an Arb matrix."""
    t0 = _q(t0)
    if not 0 < t0 < 1:
        raise ValueError('0<t0<1 required')
    t = _qa(t0)
    half, three = arb(1)/2, arb(3)/2
    pi = arb.pi()

    def F(x): return acb(x).hypgeom_2f1(half, half, 1)
    def dF(x): return acb(x).hypgeom_2f1(three, three, 2)/4
    fA = 2*pi*F(t)
    dA = 2*pi*dF(t)
    fB = acb(0, 2*pi)*F(1-t)
    dB = -acb(0, 2*pi)*dF(1-t)
    g = lambda f, d: 2*t*(t-1)*d+t*f
    return acb_mat([[fA, fB], [g(fA, dA), g(fB, dB)]])


def integer_matrix(M):
    """Unique integer matrix in an Arb ball matrix, requiring every radius < 1/2."""
    out = []
    for i in range(M.nrows()):
        row = []
        for j in range(M.ncols()):
            z = M[i, j]
            if not (z.imag.contains(0) and z.imag.rad() < 0.5 and z.real.rad() < 0.5):
                return None
            k = z.real.unique_fmpz()
            if k is None:
                return None
            row.append(int(k))
        out.append(row)
    return out


def imat_mul(A, B):
    return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def imat_inv(A):
    det = A[0][0]*A[1][1]-A[0][1]*A[1][0]
    if det not in (1, -1):
        raise ValueError('not unimodular')
    return [[A[1][1]*det, -A[0][1]*det], [-A[1][0]*det, A[0][0]*det]]


def gamma2_member(A):
    det = A[0][0]*A[1][1]-A[0][1]*A[1][0]
    return det == 1 and A[0][0] % 2 == 1 and A[1][1] % 2 == 1 and A[0][1] % 2 == 0 and A[1][0] % 2 == 0


def _enc(x):
    return str(x)


def _encv(v):
    return [_enc(x) for x in v]


def chart_record(name, chart, coordinate, terms_shown=6):
    sols = []
    for s in chart['solutions']:
        sols.append(dict(rho=_enc(s['rho']), order=len(s['y']), y_head=[_encv(v) for v in s['y'][:terms_shown]],
                         z_head=[_encv(v) for v in s['z'][:terms_shown]],
                         log_terms_present=any(any(v) for v in s['z'])))
    rec = dict(chart=name, coordinate=coordinate, residue=[_encv(r) for r in chart['R']],
               E=[_encv(r) for r in chart['E']], sigma=_enc(chart['sigma']),
               eigenvalues=_encv(chart['eigenvalues']), exponent_gap=_enc(chart['gap']), kind=chart['kind'],
               log_coefficient=_enc(chart['log_coefficient']), solutions=sols)
    if chart['kind'] == 'positive_resonance':
        rec.update(resonance_order=chart['resonance_order'], resonance_rhs=_encv(chart['resonance_rhs']),
                   eigenvector_hi=_encv(chart['eigenvector_hi']), eigenvector_lo=_encv(chart['eigenvector_lo']),
                   normalization=chart['normalization'])
    return rec


def legendre_packet(prec=192, order=120, target_bits=120):
    """Full certified monodromy/connection packet for the Legendre system."""
    old = ctx.prec
    ctx.prec = prec
    try:
        S = legendre_system()
        half = Q(1, 2)
        Pi = legendre_period_matrix(half)
        Pinv = Pi.inv()
        loops = {
            'gamma_0': [half, (0, half), (-half, 0), (0, -half), half],
            'gamma_1': [half, (1, -half), (Q(3, 2), 0), (1, half), half],
        }
        to_two = [half, (half, half), (Q(3, 2), half), 2]
        square = [2, (0, 2), (-2, 0), (0, -2), 2]
        loops['gamma_infinity_outer'] = to_two+square[1:]+list(reversed(to_two))[1:]
        taylor = {}
        ints = {}
        for name, path in loops.items():
            T, info = S.transport(path, target_bits)
            Nb = Pinv*T*Pi
            ints[name] = integer_matrix(Nb)
            taylor[name] = dict(path=[[str(_g(p)[0]), str(_g(p)[1])] for p in path], **info,
                                transition_max_radius=ball_text(max_radius(T), 6),
                                cycle_matrix_ball=mat_text(Nb, 20),
                                cycle_matrix_max_radius=ball_text(max_radius(Nb), 6),
                                integer_matrix=ints[name])
        # Frobenius certificates
        charts = legendre_charts(order)
        TP, infoP = S.transport(to_two, target_bits)
        frob = {}
        fints = {}
        Phis = {}
        pi, l2 = arb.pi(), arb(2).log()
        closed = {  # classical closed forms, checked for ball overlap only
            '0': [[-4*pi, acb(0, -16*l2)], [0, acb(0, 4)]],
            '1': [[8-16*l2, acb(0, -4*pi)], [4, 0]],
            'infinity': [[acb(-2*pi, -8*l2), acb(0, -8*l2)], [acb(0, -4), acb(0, -4)]]}
        for name, chart in charts.items():
            Phi, tails = frobenius_matrix(chart, half)
            K = local_monodromy(chart)
            if name == 'infinity':
                # counterclockwise in t on |t|=2 is clockwise in s=1/t
                Tloc = Phi*K.inv()*Phi.inv()
                T = TP.inv()*Tloc*TP
                key = 'gamma_infinity_outer'
            else:
                T = Phi*K*Phi.inv()
                key = 'gamma_' + name
            Nb = Pinv*T*Pi
            fints[key] = integer_matrix(Nb)
            C = Phi.inv()*(Pi if name != 'infinity' else TP*Pi)
            Phis[name] = Phi if name != 'infinity' else TP.inv()*Phi
            overlap = all(C[i, j].overlaps(acb(closed[name][i][j])) for i in range(2) for j in range(2))
            frob[name] = dict(chart_point='s=1/2', tail_bounds=[_qa(x).upper().str(3) for x in tails],
                              closed_form_period_coordinates=dict(
                                  formula={'0': '[[-4 pi, -16 i log 2],[0, 4 i]]', '1': '[[8-16 log 2, -4 pi i],[4, 0]]',
                                           'infinity': '[[-2 pi - 8 i log 2, -8 i log 2],[-4 i, -4 i]]'}[name],
                                  balls_overlap=overlap, status='consistency check, not a proof of the closed form'),
                              local_monodromy=mat_text(K, 20), period_coordinates_of_frobenius_basis=mat_text(C, 25),
                              cycle_matrix_ball=mat_text(Nb, 20), cycle_matrix_max_radius=ball_text(max_radius(Nb), 6),
                              integer_matrix=fints[key])
        N0, N1, Ninf = ints['gamma_0'], ints['gamma_1'], ints['gamma_infinity_outer']
        relations = {}
        if None not in (N0, N1, Ninf):
            relations = {'N1*N0': imat_mul(N1, N0), 'N0*N1': imat_mul(N0, N1)}
        detPi = Pi.det()
        conn = {}
        for a, b in (('0', '1'), ('0', 'infinity'), ('1', 'infinity')):
            Cab = Phis[a].inv()*Phis[b]
            conn[a+'->'+b] = dict(matrix=mat_text(Cab, 25), max_radius=ball_text(max_radius(Cab), 6),
                                  meaning='Phi_'+a+' C = Phi_'+b+' at t=1/2 (infinity basis transported along the upper path)')
        det_ok = detPi.overlaps(acb(0, 8*pi)) and abs(detPi-acb(0, 8*pi)).upper() < arb(2)**(-80)
        packet = dict(schema=SCHEMA, precision_bits=prec, frobenius_order=order, taylor_target_bits=target_bits,
                      system=dict(poles=['0', '1'], residues=[[_encv(r) for r in LEGENDRE_R0], [_encv(r) for r in LEGENDRE_R1]],
                                  residue_at_infinity=[_encv(r) for r in S.residue_at_infinity()],
                                  convention='Y\'=A(t)Y, Y=(int_gamma dx/y, int_gamma x dx/y), y^2=x(x-1)(x-t)'),
                      base_point='1/2', period_matrix=mat_text(Pi, 30), period_determinant=ball_text(detPi, 30),
                      period_determinant_closed_form=dict(value='8 pi i', consistent=det_ok,
                                                          reason='tr A=0 so det Pi is constant (Legendre relation)'),
                      singular_point_connections=conn,
                      positive_resonance=dict(chart='infinity', exponents=['1/2', '-1/2'], gap=1,
                                              log_coefficient=_enc(charts['infinity']['log_coefficient']),
                                              log_term_necessary=charts['infinity']['log_coefficient'] != 0,
                                              local_monodromy='-[[1, 2 pi i c],[0, 1]], c=log_coefficient'),
                      taylor_loops=taylor, transport_to_two=dict(path=[[str(_g(p)[0]), str(_g(p)[1])] for p in to_two], **infoP),
                      charts={k: chart_record(k, v, {'0': 's=t', '1': 's=1-t', 'infinity': 's=1/t'}[k]) for k, v in charts.items()},
                      frobenius_certificates=frob,
                      monodromy=dict(N0=N0, N1=N1, Ninf_outer=Ninf, frobenius_agree=all(fints[k] == ints[k] for k in ints),
                                     gamma2=dict((k, gamma2_member(v)) for k, v in ints.items() if v is not None),
                                     relations=relations),
                      convention='T Pi = Pi N; loop transitions compose right to left; N is the action on the cycle basis (A,B)',
                      integrality_premise='monodromy acts on H_1(E_t,Z) with Z-basis (A,B); the ball then fixes the integer uniquely (radius < 1/2)',
                      kernel_checked=False)
        return packet
    finally:
        ctx.prec = old
