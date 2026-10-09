"""Certified Stokes data at an irregular singular point without closed forms (N42, remaining parts).

Y'=A(z)Y, A(z)=A_0+A_1/z+...+A_J/z^J at z=infinity (Poincare rank one in z), A_0 diagonalisable
with real rational eigenvalues.  Repeated eigenvalues are allowed when the residue block on each
eigenspace is diagonalisable over Q and non-resonant; Jordan (nilpotent) leading terms and
fractional Katz invariants are reached from scalar equations by the Turrittin reduction of part B.

A. Certified Stokes matrices (no closed form is used anywhere).

 1. formal_data: exact formal fundamental solution  Y^ = P F(z) z^{L} e^{Lambda z},
    F=sum F_k z^-k, F_0=I, Lambda, L=diag(mu) rational.  With B_j=P^{-1}A_jP the recursion is the
    one of irregular_stokes.formal_normal_form, generalised from the diagonal to eigenvalue
    clusters: inside a cluster (lambda_i=lambda_k) the level-m equation fixes F_{m-1} through
        (m-1+mu_i-mu_k) F_{m-1,ik} = -(sum_{l not in cluster} B_{1,il}F_{m-1,lk} + sum_{j>=2}(B_jF_{m-j})_{ik}).
    The defining identity is replayed exactly at every level and the distinct-eigenvalue case is
    compared with irregular_stokes.formal_normal_form.

 2. Sectorial enclosure (Volterra/Olver error bound).  Truncate at N and put W=F_N(z)V.  Then
    V'=(Lambda+L/z+E(z))V with E=F_N^{-1}R_N, R_N(z)=sum_{m=N+1}^{N+J} R_m z^-m an exact Laurent
    polynomial (the levels 1..N vanish).  For |t|>=R:
        ||E(t)|| <= C |t|^{-N-1},  C = sum_m ||R_m|| R^{N+1-m} / (1-delta),  delta = sum_{k<=N} ||F_k|| R^-k < 1.
    Column j is v=z^{mu_j}e^{lambda_j z}(e_j+q) with
        q_i(z) = -int_z^{z+i infinity} e^{(lambda_i-lambda_j)(z-t)} (z/t)^{mu_i-mu_j} [E(t)(e_j+q(t))]_i dt.
    On the vertical ray from z=iR the exponential has modulus 1 (real lambda), |(z/t)|^{mu_i-mu_j} <= (|t|/|z|)^sigma,
    sigma=max mu-min mu, so the Volterra operator is a contraction with constant
        phi = C R^{-N}/(N-sigma) < 1   and   ||q||_inf <= eta = phi/(1-phi)
    on the whole ray (Banach fixed point; N>sigma).  The solution so obtained is the sectorial
    solution Y_1 (asymptotic to Y^ on arg z in (-0, pi+0)): the difference of the two is a
    combination of columns of Y_1 which along the ray is O(|z|^{mu_j-N}); comparing the component of
    largest mu shows every coefficient vanishes once N > mu_j - min mu.  Downward from -iR the same
    argument gives Y_0 (arg z in (-pi-0, 0+0)).  Only the classical existence of the sectorial
    solutions (Hukuhara-Turrittin-Sibuya) is used, never their values.

 3. Certified Taylor transport (Arb) for general n and J in the eigenframe gauge B: around c,
    A(c+u) << K M_J/(1-u/rho'), rho'=|c|/2, K=sum ||B_j|| |c|^-j, M_J=max_k C(k+J-1,k)2^-k,
    so ||Y_m|| <= (kappa)_m/(m! rho'^m), kappa=K M_J rho', and the tail after N terms is at most
    2 T_N once theta=max(1,(kappa+N)/(N+1))|h|/rho' <= 1/2 and the bound is checked in Arb.

 4. certified_stokes: S_0=(T_cw W_1(iR))^{-1} W_0(-iR), S_pi=(T_ccw W_1(iR))^{-1} W_0(-iR) exp(2 pi i L),
    with the conventions of irregular_stokes (Y_0=Y_1 S_0 across arg z=0, Y_2=Y_1 S_pi across pi,
    Y_2(z)=Y_0(z e^{-2 pi i}) exp(2 pi i L), M=S_0 exp(2 pi i L) S_pi^{-1}).  Checks: block-unipotent
    triangular shape (entries between equal eigenvalues vanish), the cyclic product against an
    independently transported loop of smaller radius, and, when z=0 is a regular singular point
    (J=1), the characteristic polynomial of the cyclic product against prod(x-exp(2 pi i rho)),
    rho the eigenvalues of A_1 (an identity that the Stokes multipliers must satisfy, independent
    of the transport).  Different (R,N) give independent asymptotic error budgets; their balls
    must overlap.

 5. birkhoff2_closed_form: every 2x2 system A_0+A_1/z with distinct eigenvalues is gauge
    equivalent to Kummer's; the map (with possibly irrational a,b) gives the closed form used
    only for validation.

B. Turrittin formal reduction for scalar equations (repeated leading eigenvalues, ramification).

    Operators sum_j a_j(x) theta^j, theta=x d/dx, a_j Laurent polynomials.  Newton polygon at
    infinity, edge polynomials, exponential shifts theta -> theta + u x^m, ramification x=t^b,
    recursion on repeated roots: exact formal exponential factors q_i(z^{1/q}) and exponents.
    reduce_to_rank_one: when the exponential factors are psi(z)+c_i z^{p/q} (common psi, distinct
    c_i) and the sheared companion system only contains powers t^{p-kp}, the substitutions
    w=e^psi v, t=z^{1/q}, Y=diag(t^{kp})Y~, s=t^p give a Poincare-rank-one system in s with
    distinct eigenvalues c_i, so part A certifies its Stokes data (Airy, Weber, e^z x Bessel(2 sqrt z), ...).
"""
from fractions import Fraction as Q
from math import comb, isqrt, log, ceil, cos, sin, pi as PI

from .irregular_stokes import formal_normal_form

SCHEMA = 'pp-irregular-stokes-general/1'


# ============================================================ exact matrix helpers
def _fq(x):
    if isinstance(x, Q):
        return x
    if isinstance(x, float):
        raise ValueError('exact rational entries required')
    return Q(str(x))


def _fmat(a):
    return [[_fq(x) for x in row] for row in a]


def _zeros(n, m=None):
    return [[Q(0)] * (n if m is None else m) for _ in range(n)]


def _eye(n):
    return [[Q(int(i == j)) for j in range(n)] for i in range(n)]


def _mul(a, b):
    k = len(b)
    m = len(b[0])
    return [[sum((ai[l] * b[l][j] for l in range(k) if ai[l]), Q(0)) for j in range(m)] for ai in a]


def _add(a, b, s=1):
    return [[x + s * y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def _scal(c, a):
    return [[c * x for x in row] for row in a]


def _norm(a):
    """Exact infinity norm (max absolute row sum)."""
    return max(sum(abs(x) for x in row) for row in a)


def _inv(a):
    n = len(a)
    m = [list(row) + [Q(int(i == j)) for j in range(n)] for i, row in enumerate(a)]
    for c in range(n):
        p = next(r for r in range(c, n) if m[r][c] != 0)
        m[c], m[p] = m[p], m[c]
        piv = m[c][c]
        m[c] = [x / piv for x in m[c]]
        for r in range(n):
            if r != c and m[r][c] != 0:
                f = m[r][c]
                m[r] = [x - f * y for x, y in zip(m[r], m[c])]
    return [row[n:] for row in m]


def _packet(a):
    return [[str(x) for x in row] for row in a]


# ============================================================ A1. formal data
def formal_data(A, order=60, check_against_existing=True):
    """Exact formal fundamental solution P F(z) z^L e^{Lambda z} (clusters of equal eigenvalues allowed)."""
    from sympy import Matrix, Rational
    if not A or len(A) < 2:
        raise ValueError('A_0 and at least A_1 required')
    if type(order) is not int or not 2 <= order <= 600:
        raise ValueError('order 2..600 required')
    As = [_fmat(a) for a in A]
    n = len(As[0])
    J = len(As) - 1
    if any(len(a) != n or any(len(r) != n for r in a) for a in As):
        raise ValueError('square matrices of equal size required')
    S = lambda a: Matrix([[Rational(x.numerator, x.denominator) for x in row] for row in a])
    M0 = S(As[0])
    cols, lam_list = [], []
    for val, mult, vecs in sorted(M0.eigenvects(), key=lambda e: Rational(e[0]) if e[0].is_Rational else 0):
        if not val.is_Rational:
            raise ValueError('real rational leading eigenvalues required')
        if len(vecs) != mult:
            raise ValueError('leading matrix not diagonalisable: use the Turrittin reduction (part B)')
        for v in vecs:
            cols.append(v)
            lam_list.append(val)
    P = Matrix.hstack(*cols)
    B1 = P.inv() * S(As[1]) * P
    # diagonalise the residue on every eigenspace of dimension > 1
    i = 0
    while i < n:
        k = i
        while k < n and lam_list[k] == lam_list[i]:
            k += 1
        if k - i > 1:
            blk = B1[i:k, i:k]
            try:
                W, D = blk.diagonalize()
            except Exception:
                raise ValueError('residue block on a repeated eigenvalue is not diagonalisable')
            if any(not D[r, r].is_Rational for r in range(k - i)):
                raise ValueError('residue block on a repeated eigenvalue needs rational eigenvalues')
            order_idx = sorted(range(k - i), key=lambda r: D[r, r])
            W = Matrix.hstack(*[W[:, r] for r in order_idx])
            P[:, i:k] = P[:, i:k] * W
        i = k
    for c in range(n):
        v = P[:, c]
        r = next(r for r in range(n) if v[r] != 0)
        P[:, c] = v / v[r]
    Pq = [[Q(int(P[i, j].p), int(P[i, j].q)) for j in range(n)] for i in range(n)]
    Piq = _inv(Pq)
    B = [_mul(_mul(Piq, a), Pq) for a in As]
    lam = [B[0][i][i] for i in range(n)]
    if any(B[0][i][j] != 0 for i in range(n) for j in range(n) if i != j):
        raise ArithmeticError('eigenframe failed')
    mu = [B[1][i][i] for i in range(n)]
    cl = [lam.index(x) for x in lam]  # cluster label = first index with that eigenvalue
    for i in range(n):
        for k in range(n):
            if i != k and cl[i] == cl[k]:
                if B[1][i][k] != 0:
                    raise ArithmeticError('residue block not diagonal')
                d = mu[k] - mu[i]
                if d.denominator == 1 and d >= 1:
                    raise ValueError('resonant residue on a repeated eigenvalue (mu_k-mu_i positive integer)')
    F = [_eye(n)]
    for m in range(1, order + 2):
        if m >= 2:
            G = F[m - 1]
            hi = [_mul(B[j], F[m - j]) for j in range(2, min(m, J) + 1)]
            for i in range(n):
                for k in range(n):
                    if cl[i] != cl[k]:
                        continue
                    s = sum((B[1][i][l] * G[l][k] for l in range(n) if cl[l] != cl[i]), Q(0))
                    s += sum((h[i][k] for h in hi), Q(0))
                    G[i][k] = -s / (m - 1 + mu[i] - mu[k])
        rhs = _zeros(n)
        for j in range(1, min(m, J) + 1):
            rhs = _add(rhs, _mul(B[j], F[m - j]))
        Fm1 = F[m - 1]
        rhs = [[rhs[i][k] + (m - 1) * Fm1[i][k] - Fm1[i][k] * mu[k] for k in range(n)] for i in range(n)]
        Fm = [[(rhs[i][k] / (lam[k] - lam[i]) if cl[i] != cl[k] else Q(0)) for k in range(n)] for i in range(n)]
        F.append(Fm)
    F = F[:order + 1]
    for m in range(1, order + 1):
        if any(x != 0 for row in _level_residual(B, F, lam, mu, m, order) for x in row):
            raise ArithmeticError('formal identity failed at level %d' % m)
    cross = None
    if check_against_existing and len(set(lam)) == n:
        ko = min(order, 12)
        ch = formal_normal_form(A, order=ko)
        cross = (ch['eigenvalues'] == [str(x) for x in lam] and ch['formal_exponents'] == [str(x) for x in mu]
                 and ch['eigenframe'] == _packet(Pq)
                 and all(ch['coefficients'][k] == _packet(F[k]) for k in range(ko + 1)))
        if not cross:
            raise ArithmeticError('disagreement with irregular_stokes.formal_normal_form')
    return dict(n=n, J=J, order=order, A=As, P=Pq, B=B, lam=lam, mu=mu, clusters=cl, F=F,
                identity_checked=True, matches_irregular_stokes=cross)


def _level_residual(B, F, lam, mu, m, N):
    """Coefficient of z^-m in B F_N - F_N' - F_N(Lambda + L/z) for the truncation F_N=sum_{k<=N} F_k z^-k."""
    n = len(lam)
    J = len(B) - 1

    def f(k):
        return F[k] if 0 <= k <= N else None
    out = _zeros(n)
    for j in range(0, J + 1):
        Fk = f(m - j)
        if Fk is not None:
            out = _add(out, _mul(B[j], Fk))
    Fm1 = f(m - 1)
    if Fm1 is not None:
        out = [[out[i][k] + (m - 1) * Fm1[i][k] - Fm1[i][k] * mu[k] for k in range(n)] for i in range(n)]
    Fm = f(m)
    if Fm is not None:
        out = [[out[i][k] - Fm[i][k] * lam[k] for k in range(n)] for i in range(n)]
    return out


# ============================================================ A2. sectorial enclosures
def asymptotic_bound(fd, N, R):
    """Exact rational error budget of the truncated formal solution on |z|>=R (vertical rays)."""
    R = _fq(R)
    mu = fd['mu']
    sigma = max(mu) - min(mu)
    if not (N > sigma and N <= fd['order']):
        raise ValueError('need sigma < N <= order')
    delta = sum((_norm(fd['F'][k]) / R ** k for k in range(1, N + 1)), Q(0))
    if delta >= 1:
        return None
    J = fd['J']
    res = {m: _level_residual(fd['B'], fd['F'], fd['lam'], mu, m, N) for m in range(N + 1, N + J + 1)}
    C = sum((_norm(res[m]) * R ** (N + 1 - m) for m in res), Q(0)) / (1 - delta)
    phi = C / R ** N / (N - sigma)
    if phi >= 1:
        return None
    return dict(N=N, R=R, sigma=sigma, delta=delta, C=C, phi=phi, eta=phi / (1 - phi))


def best_truncation(fd, R, window=8):
    """N minimising the exact bound eta (scan around the smallest ||F_k|| R^-k)."""
    R = _fq(R)
    sigma = max(fd['mu']) - min(fd['mu'])
    lo = int(sigma) + 1

    def lg(x):
        return log(x.numerator) - log(x.denominator) if x else -1e300
    scores = [(lg(_norm(fd['F'][k])) - k * lg(R), k) for k in range(lo, fd['order'] + 1)]
    kstar = min(scores)[1]
    best = None
    for N in range(max(lo, kstar - window), min(fd['order'], kstar + window) + 1):
        b = asymptotic_bound(fd, N, R)
        if b is not None and (best is None or b['eta'] < best['eta']):
            best = b
    if best is None:
        raise ArithmeticError('no admissible truncation at this radius')
    return best


def _acbq(x):
    from flint import acb, arb, fmpq
    x = _fq(x)
    return acb(arb(fmpq(x.numerator, x.denominator)))


def _acbg(z):
    from flint import acb, arb, fmpq
    re, im = _fq(z[0]), _fq(z[1])
    return acb(arb(fmpq(re.numerator, re.denominator)), arb(fmpq(im.numerator, im.denominator)))


def _acbm(a):
    from flint import acb_mat
    return acb_mat([[_acbq(x) for x in row] for row in a])


def _ball(r):
    """Complex ball centred at 0 containing the closed disc of rational radius r."""
    from flint import acb, arb, fmpq
    r = _fq(r)
    rr = arb(fmpq(r.numerator, r.denominator))
    e = arb(0, rr.upper() if hasattr(rr, 'upper') else rr)
    return acb(e, e)


def sectorial_parts(fd, bound, side):
    """Factored enclosure W = F_N(z) (I+Q) D(z) of the sectorial matrix (eigenframe gauge W=P^{-1}Y).

    side=+1: Y_1 at z=iR, arg z=pi/2; side=-1: Y_0 at z=-iR, arg z=-pi/2.  Returns F_N(z) (tight
    Arb balls), the diagonal D(z) and Qhat, a ball matrix centred at 0 that contains D^{-1} Q D:
    |Q_ik|<=eta and |D_k/D_i| = R^(mu_k-mu_i) exactly on the imaginary axis (real lambda, mu).
    """
    from flint import acb, acb_mat, arb
    n = fd['n']
    N, R = bound['N'], bound['R']
    z = _acbg((0, side * R))
    w = 1 / z
    Fz = _acbm(fd['F'][N])
    for k in range(N - 1, -1, -1):
        Fz = Fz * w + _acbm(fd['F'][k])
    I = acb(0, 1)
    lnR = _acbq(R).log()
    argz = acb.pi() * side / 2
    D = [(_acbq(fd['mu'][j]) * (lnR + I * argz)).exp() * (_acbq(fd['lam'][j]) * z).exp() for j in range(n)]
    eta = _acbq(bound['eta']).real
    Qh = acb_mat(n, n)
    for i in range(n):
        for k in range(n):
            r = (eta * ((_acbq(fd['mu'][k] - fd['mu'][i]).real) * lnR.real).exp())
            r = arb(0, r.upper() if hasattr(r, 'upper') else r) + arb(0, r.rad())
            Qh[i, k] = acb(r, r)
    return dict(F=Fz, D=D, Qhat=Qh)


def sectorial_value(fd, bound, side):
    """Plain enclosure of W = F_N(z)(I+Q)D(z) (each |Q_ik|<=eta)."""
    from flint import acb_mat
    n = fd['n']
    p = sectorial_parts(fd, bound, side)
    e = _ball(bound['eta'])
    Qm = acb_mat([[(1 if i == j else 0) + e for j in range(n)] for i in range(n)])
    Dm = acb_mat([[p['D'][j] if i == j else 0 for j in range(n)] for i in range(n)])
    return p['F'] * Qm * Dm


def _scale(X, left, right):
    """diag(left)^{-1} X diag(right)."""
    from flint import acb_mat
    n = X.nrows()
    return acb_mat([[X[i, j] * right[j] / left[i] for j in range(n)] for i in range(n)])


# ============================================================ A3. certified transport
def _mj(J):
    best, k = Q(1), 0
    while True:
        k += 1
        v = Q(comb(k + J - 1, k), 2 ** k)
        if v > best:
            best = v
        if Q(k + J, 2 * (k + 1)) < 1 and v < best:
            return best


def _abs_lo(z):
    s = z[0] ** 2 + z[1] ** 2
    return Q(isqrt(int(s * 10 ** 12)), 10 ** 6)


def _abs_hi(z):
    s = z[0] ** 2 + z[1] ** 2
    return Q(isqrt(int(s * 10 ** 12) + 1) + 1, 10 ** 6)


class Transporter:
    """Certified Taylor transport for z^J Y' = (sum_j B_j z^{J-j}) Y (Arb balls, explicit tails)."""

    def __init__(self, B, prec):
        from flint import ctx
        self.B = [_fmat(b) for b in B]
        self.n = len(self.B[0])
        self.J = len(self.B) - 1
        self.Bacb = [_acbm(b) for b in self.B]
        self.Bnorm = [_norm(b) for b in self.B]
        self.MJ = _mj(self.J)
        self.prec = prec
        self.orders = []

    def step(self, c, d):
        from flint import acb, acb_mat, arb, fmpq
        n, J = self.n, self.J
        c = (_fq(c[0]), _fq(c[1]))
        h = (_fq(d[0]) - c[0], _fq(d[1]) - c[1])
        rho = _abs_lo(c)
        hs = _abs_hi(h)
        rp = rho / 2
        if not hs * 4 <= rho:
            raise ValueError('step longer than |c|/4')
        K = sum((self.Bnorm[j] / rho ** j for j in range(J + 1)), Q(0))
        kap = arb(fmpq((K * self.MJ * rp).numerator, (K * self.MJ * rp).denominator))
        x = arb(fmpq((hs / rp).numerator, (hs / rp).denominator))
        target = arb(2) ** (-(self.prec + 8))
        term = arb(1)
        m = 0
        while True:
            th = x * (kap + m) / (m + 1)
            if m >= 1 and (th < arb(1) / 2) and (x <= arb(1) / 2) and (2 * term < target):
                break
            term = term * (kap + m) / (m + 1) * x
            m += 1
            if m > 5000:
                raise ArithmeticError('tail bound not reached')
        Nt = m
        tail = (2 * term).upper() if hasattr(term, 'upper') else 2 * term
        C = _acbg(c)
        H = _acbg(h)
        q = [comb(J, l) * C ** (J - l) for l in range(J + 1)]
        Rl = []
        for l in range(J + 1):
            M = acb_mat(n, n)
            for j in range(J + 1 - l):
                M = M + self.Bacb[j] * (comb(J - j, l) * C ** (J - j - l))
            Rl.append(M)
        hR = [Rl[l] * H ** (l + 1) for l in range(J + 1)]
        hq = [q[l] * H ** l for l in range(J + 1)]
        inv_q0 = 1 / q[0]
        Z = [acb_mat([[int(i == j) for j in range(n)] for i in range(n)])]
        total = Z[0]
        for mm in range(0, Nt - 1):
            acc = acb_mat(n, n)
            for l in range(0, min(J, mm) + 1):
                acc = acc + hR[l] * Z[mm - l]
            for l in range(1, min(J, mm) + 1):
                acc = acc - Z[mm - l + 1] * (hq[l] * (mm - l + 1))
            Znew = acc * (inv_q0 / (mm + 1))
            Z.append(Znew)
            total = total + Znew
        e = acb(arb(0, tail), arb(0, tail))
        self.orders.append(Nt)
        return acb_mat([[total[i, j] + e for j in range(n)] for i in range(n)])

    def path(self, pts):
        from flint import acb_mat
        T = acb_mat([[int(i == j) for j in range(self.n)] for i in range(self.n)])
        for c, d in zip(pts, pts[1:]):
            T = self.step(c, d) * T
        return T


def _gr(x):
    return Q(round(x * 2 ** 24), 2 ** 24)


def arc_points(r, th0, th1, hmax):
    """Gaussian-rational points near the arc of radius r from th0 to th1 (exact endpoints on the axes)."""
    r = _fq(r)
    L = abs(th1 - th0) * float(r)
    steps = max(2, int(ceil(L / float(hmax))))
    pts = []
    for k in range(steps + 1):
        th = th0 + (th1 - th0) * k / steps
        pts.append((_gr(float(r) * cos(th)), _gr(float(r) * sin(th))))
    for k, th in ((0, th0), (steps, th1)):
        t = round(th / (PI / 2))
        if abs(th - t * PI / 2) < 1e-12:
            pts[k] = [(r, Q(0)), (Q(0), r), (-r, Q(0)), (Q(0), -r)][t % 4]
    return pts


def radial_points(r0, r1, hmax, phase=(0, 1)):
    """Points r*phase from r0 to r1 (phase a unit Gaussian integer), steps <= min(r/8, hmax)."""
    r0, r1 = _fq(r0), _fq(r1)
    pts = [r0]
    r = r0
    sgn = 1 if r1 > r0 else -1
    while r != r1:
        st = min(Q(r) / 8, _gr(float(hmax)))
        nr = r + sgn * st
        if (sgn > 0 and nr >= r1) or (sgn < 0 and nr <= r1):
            nr = r1
        r = _gr(float(nr)) if nr != r1 else r1
        pts.append(r)
    return [(phase[0] * x, phase[1] * x) for x in pts]


# ============================================================ A4. certified Stokes matrices
def _charpoly_coeffs(M):
    """Coefficients c_0..c_n of det(x I - M) (acb), from Arb."""
    p = M.charpoly()
    return [p[k] for k in range(M.nrows() + 1)]


def _expected_local_charpoly(A1):
    """prod (x - exp(2 pi i rho)), rho the eigenvalues of A_1 (Arb enclosures of algebraic rho)."""
    from flint import fmpq_poly, fmpq, acb, acb_poly
    from sympy import Matrix, Rational, Poly, symbols
    x = symbols('x')
    M = Matrix([[Rational(v.numerator, v.denominator) for v in row] for row in A1])
    cp = Poly(M.charpoly(x).as_expr(), x)
    co = [Q(int(c.p), int(c.q)) for c in reversed(cp.all_coeffs())]
    fp = fmpq_poly([fmpq(c.numerator, c.denominator) for c in co])
    roots = []
    for r, m in fp.complex_roots():
        roots += [r] * m
    two_pi_i = 2 * acb.pi() * acb(0, 1)
    poly = acb_poly([1])
    for r in roots:
        poly = poly * acb_poly([-(two_pi_i * r).exp(), 1])
    return [poly[k] for k in range(len(roots) + 1)], [str(r) for r in roots]


def certified_stokes(A, R, order=None, prec=None, loop_radius=None, fd=None, hmax=None, eta_override=None):
    """Arb enclosures of S_0, S_pi and the loop monodromy for Y'=(sum A_j z^-j)Y with checks.

    eta_override replaces the proven Volterra bound and exists only for negative controls
    (an understated bound must make some check fail); certified results never use it.
    """
    from flint import acb, acb_mat, ctx
    if fd is None:
        R0 = _fq(R)
        if order is None:
            order = int(3 * float(R0)) + 12
        fd = formal_data(A, order=order)
    R = _fq(R)
    n = fd['n']
    lam = fd['lam']
    span = float(max(lam) - min(lam))
    if prec is None:
        prec = 96 + int(1.6 * span * float(R) * 1.4427) + 8 * n
    old = ctx.prec
    ctx.prec = prec
    try:
        bd = best_truncation(fd, R)
        if eta_override is not None:
            bd = dict(bd, eta=_fq(eta_override))
        P1 = sectorial_parts(fd, bd, +1)
        P0 = sectorial_parts(fd, bd, -1)
        lmax = max(abs(float(x)) for x in lam) + float(_norm(fd['B'][1])) / float(R) + 0.25
        hm = hmax if hmax is not None else min(0.75 / lmax, float(R) / 9)
        tr = Transporter(fd['B'], prec)
        cw = arc_points(R, PI / 2, -PI / 2, hm)
        ccw = arc_points(R, PI / 2, 3 * PI / 2, hm)
        Tcw = tr.path(cw)
        Tccw = tr.path(ccw)
        rl = _fq(loop_radius) if loop_radius is not None else min(Q(R) / 2, Q(3))
        loop = radial_points(R, rl, hm) + arc_points(rl, PI / 2, PI / 2 + 2 * PI, min(hm, float(rl) / 9))[1:] + radial_points(rl, R, hm)[1:]
        Tloop = tr.path(loop)
        I = acb(0, 1)
        two_pi_i = 2 * acb.pi() * I
        E = acb_mat([[((two_pi_i * _acbq(fd['mu'][j])).exp() if i == j else 0) for j in range(n)] for i in range(n)])
        Id = acb_mat([[int(i == j) for j in range(n)] for i in range(n)])
        # S = [D1^-1 (I+Q1)^-1 D1] [D1^-1 F1^-1 T^-1 F0 D0] [D0^-1 (I+Q0) D0]
        U1 = (Id + P1['Qhat']).inv()
        V0 = Id + P0['Qhat']
        S0t = _scale((Tcw * P1['F']).solve(P0['F']), P1['D'], P0['D'])
        Spt = _scale((Tccw * P1['F']).solve(P0['F']), P1['D'], P0['D'])
        S0 = U1 * S0t * V0
        Sp = U1 * Spt * V0 * E
        Mt = _scale(P1['F'].solve(Tloop * P1['F']), P1['D'], P1['D'])
        M = U1 * Mt * (Id + P1['Qhat'])
        cyc = S0 * E * Sp.inv()
        # direct test of the Volterra enclosures: transport Y_1 from iR to i(5R/4) (Y_0 from -iR to -i(5R/4))
        # and compare with the independent enclosure there: Y(R')^{-1} T Y(R) must contain I.
        R2 = R * Q(5, 4)
        bd2 = best_truncation(fd, R2)
        if eta_override is not None:
            bd2 = dict(bd2, eta=_fq(eta_override))
        axis = {}
        for side, Pa in ((1, P1), (-1, P0)):
            Pb = sectorial_parts(fd, bd2, side)
            Tax = tr.path(radial_points(R, R2, hm, phase=(0, side)))
            X = _scale(Pb['F'].solve(Tax * Pa['F']), Pb['D'], Pa['D'])
            C = (Id + Pb['Qhat']).inv() * X * (Id + Pa['Qhat'])
            axis['Y1' if side == 1 else 'Y0'] = C
        cl = fd['clusters']
        one, zero = acb(1), acb(0)
        checks = {}
        checks['S0_block_unipotent_upper'] = all(
            S0[i, j].overlaps(one if i == j else zero) for i in range(n) for j in range(n)
            if i == j or not lam[i] < lam[j])
        checks['S_pi_block_unipotent_lower'] = all(
            Sp[i, j].overlaps(one if i == j else zero) for i in range(n) for j in range(n)
            if i == j or not lam[i] > lam[j])
        checks['cyclic_product_overlaps_independent_loop'] = all(cyc[i, j].overlaps(M[i, j]) for i in range(n) for j in range(n))
        checks['sectorial_enclosures_consistent_along_axis'] = all(
            C[i, j].overlaps(one if i == j else zero) for C in axis.values() for i in range(n) for j in range(n))
        tr1 = sum((fd['A'][1][i][i] for i in range(n)), Q(0))
        checks['loop_det_matches_trace_of_residue'] = bool(M.det().overlaps((two_pi_i * _acbq(tr1)).exp()))
        local = None
        if fd['J'] == 1:
            exp_cp, roots = _expected_local_charpoly(fd['A'][1])
            got = _charpoly_coeffs(cyc)
            checks['charpoly_matches_local_exponents_at_0'] = all(g.overlaps(e) for g, e in zip(got, exp_cp))
            local = dict(residue_eigenvalues=roots,
                         charpoly_cyclic_product=[_s(x) for x in got],
                         charpoly_expected=[_s(x) for x in exp_cp])
        stokes_entries = {}
        for i in range(n):
            for j in range(n):
                if lam[i] < lam[j]:
                    stokes_entries['S0[%d,%d]' % (i, j)] = _s(S0[i, j])
                if lam[i] > lam[j]:
                    stokes_entries['S_pi[%d,%d]' % (i, j)] = _s(Sp[i, j])
        maxrad = max(_rad(S0[i, j]) for i in range(n) for j in range(n))
        maxrad = max(maxrad, max(_rad(Sp[i, j]) for i in range(n) for j in range(n)))
        rec = dict(schema=SCHEMA, system=[_packet(a) for a in fd['A']], rank=n, J=fd['J'],
                   eigenvalues=[str(x) for x in lam], formal_exponents=[str(x) for x in fd['mu']],
                   eigenframe=_packet(fd['P']), radius=str(R), truncation=bd['N'], precision_bits=prec,
                   asymptotic_error_bound=_fs(bd['eta']), contraction_constant=_fs(bd['phi']),
                   delta=_fs(bd['delta']),
                   taylor_steps=len(tr.orders), taylor_order_max=max(tr.orders), loop_radius=str(rl),
                   stokes_entries=stokes_entries, max_ball_radius=maxrad,
                   axis_check_radius=str(R2), axis_check_truncation=bd2['N'],
                   axis_check_max_radius=max(_rad(C[i, j]) for C in axis.values() for i in range(n) for j in range(n)),
                   cyclic_product_minus_loop_max_radius=max(_rad(cyc[i, j] - M[i, j]) for i in range(n) for j in range(n)),
                   local_exponent_check=local, checks=checks,
                   certified=all(checks.values()) and eta_override is None)
        return rec, dict(S0=S0, S_pi=Sp, M=M, cyc=cyc, E=E, fd=fd, bound=bd)
    finally:
        ctx.prec = old


def _s(x):
    return x.str(radius=True, more=False) if hasattr(x, 'str') else str(x)


def _rad(x):
    return float(max(x.real.rad(), x.imag.rad()))


def _fs(x):
    x = Q(x)
    if x == 0:
        return '0'
    e = int((log(x.numerator) - log(x.denominator)) / log(10))
    return '%.4e' % (float(x * Q(10) ** (-e)) * 10.0 ** e) if abs(e) < 300 else '10^%d' % e


def balls_overlap(raw1, raw2):
    """Entrywise overlap of two independent certifications (different radius/truncation)."""
    n = raw1['S0'].nrows()
    return all(raw1[k][i, j].overlaps(raw2[k][i, j]) for k in ('S0', 'S_pi') for i in range(n) for j in range(n))


# ============================================================ A5. 2x2 closed form (validation only)
def birkhoff2_closed_form(fd, prec=None):
    """Closed-form Stokes multipliers of a 2x2 system A_0+A_1/z (distinct eigenvalues) via Kummer.

    In the eigenframe B_1=[[b11,b12],[b21,b22]], Delta=lambda_2-lambda_1.  With d a root of
    b21 d^2+(b11-b22) d-b12=0, a=b21 d, b=2a+b11-b22:
      s_0  = d Delta^{mu_1-mu_2} 2 pi i/(Gamma(1-a)Gamma(b-a)),
      s_pi = Delta^{mu_2-mu_1}/d (-2 pi i) e^{i pi(b-2a)}/(Gamma(a)Gamma(1+a-b)).
    Both roots d give the same values (checked by the caller).
    """
    from flint import acb, ctx
    if fd['n'] != 2 or fd['J'] != 1 or fd['lam'][0] == fd['lam'][1]:
        raise ValueError('2x2, J=1, distinct eigenvalues required')
    old = ctx.prec
    if prec is not None:
        ctx.prec = prec
    try:
        B1 = fd['B'][1]
        b11, b12, b21, b22 = (_acbq(B1[0][0]), _acbq(B1[0][1]), _acbq(B1[1][0]), _acbq(B1[1][1]))
        D = _acbq(fd['lam'][1] - fd['lam'][0])
        m1, m2 = _acbq(fd['mu'][0]), _acbq(fd['mu'][1])
        out = []
        if B1[1][0] != 0:
            disc = ((b11 - b22) ** 2 + 4 * b21 * b12).sqrt()
            ds = [(-(b11 - b22) + disc) / (2 * b21), (-(b11 - b22) - disc) / (2 * b21)]
        else:
            if B1[0][0] == B1[1][1]:
                raise ValueError('degenerate triangular residue')
            ds = [b12 / (b11 - b22)]
        two_pi_i = 2 * acb.pi() * acb(0, 1)
        for d in ds:
            if d == 0:
                continue
            a = b21 * d
            b = 2 * a + b11 - b22
            s0 = d * (D.log() * (m1 - m2)).exp() * two_pi_i * (1 - a).rgamma() * (b - a).rgamma()
            sp = (D.log() * (m2 - m1)).exp() / d * (-two_pi_i) * (acb.pi() * acb(0, 1) * (b - 2 * a)).exp() * a.rgamma() * (1 + a - b).rgamma()
            out.append(dict(d=d, a=a, b=b, s0=s0, s_pi=sp))
        return out
    finally:
        ctx.prec = old


# ============================================================ B. Turrittin reduction of scalar equations
# operators: dict {(e, j): c} meaning sum c x^e theta^j, e Fraction/int exponent, c sympy number
def _sp(x):
    from sympy import nsimplify, Rational, sympify
    if isinstance(x, Q):
        return Rational(x.numerator, x.denominator)
    return sympify(x)


def _clean(L):
    from sympy import expand, simplify
    out = {}
    for k, c in L.items():
        c = expand(c)
        if c != 0:
            c2 = simplify(c)
            if c2 != 0:
                out[k] = c2
    return out


def op_from_ode(p):
    """sum_k p_k(z) w^(k) = 0, p_k given as {exponent: coefficient} -> theta-form operator."""
    from sympy import symbols, Poly, expand, ff
    th = symbols('theta')
    L = {}
    for k, pk in enumerate(p):
        fall = Poly(expand(ff(th, k)), th) if k > 0 else Poly(1, th)
        for e, c in pk.items():
            for (j,), a in fall.terms():
                key = (Q(e) - k, j)
                L[key] = L.get(key, 0) + _sp(c) * a
    return _clean(L)


def op_mul(A, Bop):
    """(x^a theta^j)(x^b theta^k) = x^{a+b} (theta+b)^j theta^k."""
    out = {}
    for (a, j), c1 in A.items():
        for (b, k), c2 in Bop.items():
            bb = _sp(b)
            for i in range(j + 1):
                key = (a + b, i + k)
                out[key] = out.get(key, 0) + c1 * c2 * comb(j, i) * bb ** (j - i)
    return _clean(out)


def op_shift(L, g):
    """Substitute theta -> theta + g(x), g={e: c} (w = e^phi v with x phi' = g)."""
    T = {(Q(0), 1): _sp(1)}
    for e, c in g.items():
        T[(Q(e), 0)] = T.get((Q(e), 0), 0) + _sp(c)
    out = {}
    maxj = max(j for (_, j) in L)
    pw = {(Q(0), 0): _sp(1)}
    powers = [pw]
    for _ in range(maxj):
        powers.append(op_mul(T, powers[-1]))
    for (e, j), c in L.items():
        for (e2, k), c2 in powers[j].items():
            key = (Q(e) + e2, k)
            out[key] = out.get(key, 0) + c * c2
    return _clean(out)


def op_ramify(L, b):
    """x = t^b: theta_x = theta_t / b, x^e = t^{b e}."""
    out = {}
    for (e, j), c in L.items():
        key = (Q(e) * b, j)
        out[key] = out.get(key, 0) + c / _sp(b) ** j
    return _clean(out)


def newton_edges(L):
    """Upper-hull edges of the points (j, max e) with slope m (theta ~ u x^m) and edge polynomials."""
    pts = {}
    for (e, j) in L:
        pts[j] = max(pts.get(j, e), Q(e))
    js = sorted(pts)
    hull = []
    for j in js:
        P = (j, pts[j])
        while len(hull) >= 2:
            (j1, e1), (j2, e2) = hull[-2], hull[-1]
            # remove hull[-1] if it lies on or below the segment hull[-2] -> P
            if (e2 - e1) * (P[0] - j1) <= (P[1] - e1) * (j2 - j1):
                hull.pop()
            else:
                break
        hull.append(P)
    edges = []
    for (j1, e1), (j2, e2) in zip(hull, hull[1:]):
        m = Q(e1 - e2) / (j2 - j1)
        poly = {}
        for (e, j), c in L.items():
            if Q(e) + j * m == e1 + j1 * m:
                poly[j] = poly.get(j, 0) + c
        edges.append(dict(m=m, left=j1, right=j2, poly=poly))
    return edges


def _roots(poly):
    from sympy import symbols, Poly, roots
    u = symbols('u')
    P = Poly(sum(c * u ** j for j, c in poly.items()), u)
    rs = roots(P, u)
    if sum(rs.values()) != P.degree():
        raise ValueError('edge polynomial roots not found in closed form')
    return {r: m for r, m in rs.items() if r != 0}


def turrittin_scalar(L, q=1, phi=None, restrict=None, _depth=0):
    """Formal exponential factors of a scalar operator at infinity (exact, sympy algebraic numbers).

    Returns a list of dicts: q (ramification index used), phi {exponent of z (Fraction): coefficient}
    (the factor exp(sum c z^e)), multiplicity, rho (power of z for a simple factor, else the
    indicial roots of the regular part).  Edges of the Newton polygon with slope m<=0 give the
    regular part of the current cluster; edges with 0<m<restrict are refined recursively.
    """
    if _depth > 12:
        raise ArithmeticError('Turrittin recursion too deep')
    phi = dict(phi or {})
    all_edges = newton_edges(L)
    edges = [e for e in all_edges if e['m'] > 0 and (restrict is None or e['m'] < restrict)]
    if any(e['m'].denominator != 1 for e in edges):
        b = 1
        for e in edges:
            b = b * e['m'].denominator // _gcd(b, e['m'].denominator)
        return turrittin_scalar(op_ramify(L, b), q * b, phi, None if restrict is None else restrict * b, _depth + 1)
    out = []
    pos = [e for e in all_edges if e['m'] > 0]
    js = sorted({j for (_, j) in L})
    nreg = pos[0]['left'] if pos else js[-1]
    if nreg > 0:
        out.append(dict(q=q, phi=phi, multiplicity=nreg, rho=_regular_rho(L, all_edges, nreg, q), depth=_depth))
    for ed in edges:
        m = ed['m']
        for u, mult in _roots(ed['poly']).items():
            ph = dict(phi)
            key = Q(m) / q
            ph[key] = ph.get(key, 0) + u / _sp(m)
            sub = turrittin_scalar(op_shift(L, {m: u}), q, ph, m, _depth + 1)
            if sum(e['multiplicity'] for e in sub) != mult:
                raise ArithmeticError('cluster multiplicity mismatch')
            out += sub
    return out


def _regular_rho(L, edges, nreg, q):
    """Power of z of a single regular solution, or the indicial roots (in z) of a regular part."""
    from sympy import symbols, Poly, roots
    zero = [e for e in edges if e['m'] == 0]
    if nreg == 1:
        if zero and zero[0]['left'] == 0 and zero[0]['right'] == 1:
            from sympy import simplify
            return simplify(-zero[0]['poly'].get(0, 0) / zero[0]['poly'][1] / q)
        return _sp(0)
    if not zero:
        return None
    u = symbols('u')
    P = Poly(sum(c * u ** j for j, c in zero[0]['poly'].items()), u)
    return [r / q for r, m in roots(P, u).items() for _ in range(m)]


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return a


def reduce_to_rank_one(L, exps=None):
    """Exact reduction of a scalar operator to a Poincare-rank-one system in s (see module doc)."""
    from sympy import Rational, nsimplify
    if exps is None:
        exps = turrittin_scalar(L)
    if any(e['multiplicity'] != 1 for e in exps):
        raise ValueError('all exponential factors must be simple')
    keys = sorted({k for e in exps for k in e['phi']})
    differing = [k for k in keys if len({_sp(e['phi'].get(k, 0)) for e in exps}) > 1]
    if not differing:
        raise ValueError('no distinguishing exponent')
    kstar = max(differing)
    if any(k != kstar for k in differing):
        raise ValueError('factors differ in more than one exponent: not quasi-homogeneous')
    cs = [_sp(e['phi'].get(kstar, 0)) for e in exps]
    if len(set(cs)) != len(cs) or any(not c.is_Rational for c in cs):
        raise ValueError('distinct rational leading coefficients required')
    psi = {k: _sp(exps[0]['phi'][k]) for k in keys if k != kstar and k in exps[0]['phi']}
    qq = 1
    for k in list(psi) + [kstar]:
        qq = qq * Q(k).denominator // _gcd(qq, Q(k).denominator)
    p = int(kstar * qq)
    Lt = op_ramify(L, qq)
    g = {Q(k) * qq: Q(k) * qq * c for k, c in psi.items()}
    Lv = op_shift(Lt, g) if g else Lt
    n = max(j for (_, j) in Lv)
    lead = {e: c for (e, j), c in Lv.items() if j == n}
    if len(lead) != 1:
        raise ValueError('leading coefficient must be a monomial')
    (e_n, c_n), = lead.items()
    # companion: theta^n v = -sum_{j<n} (a_j/a_n) theta^j v
    C = [[{} for _ in range(n)] for _ in range(n)]
    for i in range(n - 1):
        C[i][i + 1] = {Q(0): _sp(1)}
    for (e, j), c in Lv.items():
        if j < n:
            C[n - 1][j][Q(e) - e_n] = C[n - 1][j].get(Q(e) - e_n, 0) - c / c_n
    # shear D=diag(t^{kp}): C~_ij = C_ij t^{p(j-i)} - delta_ij i p
    Ct = [[{Q(e) + p * (j - i): c for e, c in C[i][j].items()} for j in range(n)] for i in range(n)]
    for i in range(n):
        Ct[i][i][Q(0)] = Ct[i][i].get(Q(0), 0) - i * p
    blocks = {}
    for i in range(n):
        for j in range(n):
            for e, c in Ct[i][j].items():
                if c == 0:
                    continue
                k = p - e
                if k < 0 or k % p != 0:
                    raise ValueError('sheared system not quasi-homogeneous (power t^%s)' % e)
                blocks.setdefault(int(k // p), [[0] * n for _ in range(n)])[i][j] += c
    Jmax = max(max(blocks), 1)
    As = []
    for jj in range(Jmax + 1):
        Mb = blocks.get(jj, [[0] * n for _ in range(n)])
        As.append([[_fq(Rational(x) / p) for x in row] for row in Mb])
    return dict(q=qq, p=p, psi={str(k): str(v) for k, v in psi.items()}, kstar=str(kstar),
                leading_coefficients=[str(c) for c in cs], s_variable='s = z^(%s)' % (Q(p, qq)),
                A=As, exponents=exps)


def scalar_operator_record(L):
    return {'%s,%s' % (e, j): str(c) for (e, j), c in sorted(L.items(), key=lambda t: (t[0][1], t[0][0]))}


def exps_record(exps):
    return [dict(q=e['q'], exponential={str(k): str(v) for k, v in sorted(e['phi'].items())},
                 multiplicity=e['multiplicity'],
                 z_power=None if e['rho'] is None else (str(e['rho']) if not isinstance(e['rho'], list) else [str(r) for r in e['rho']]))
            for e in exps]
