"""Irregular singular points of Poincare rank one: formal normal forms and Stokes data.

System Y'=A(z)Y, A(z)=A_0+A_1/z+...+A_J/z^J near z=infinity (Poincare rank 1),
A_0 with distinct rational eigenvalues.

1. formal_normal_form: exact Hukuhara-Turrittin normal form in the unramified
   distinct-eigenvalue case.  With A_0=P Lambda P^{-1} (first eigenvector
   components normalised to 1 when possible) and B_j=P^{-1}A_jP, the formal
   fundamental solution is  Y^=P F^(z) z^{Lambda'} e^{Lambda z},  F^=sum F_k z^-k,
   F_0=I, Lambda'=diag(B_1), and for m>=1
       F_m Lambda - Lambda F_m = sum_{j=1}^m B_j F_{m-j} + (m-1)F_{m-1} - F_{m-1}Lambda',
   whose diagonal part fixes diag F_{m-1}.  Formal monodromy exp(2 pi i Lambda').
   Every coefficient is an exact rational and the identity is replayed.
2. Numerical Stokes multipliers for 2x2 systems by two independent routes:
   (a) late-term (resurgent) asymptotics of the exact coefficients with
       Richardson extrapolation; (b) Borel-Pade-Laplace lateral sums.
3. Certified Stokes matrices (Arb) for the confluent hypergeometric (Kummer)
   system, which contains Bessel (a=nu+1/2, b=2nu+1, variable 2z) and Airy
   (nu=1/3): the sectorial solutions are Tricomi U functions evaluated by
   Arb's rigorous acb_hypgeom_u on principal branches; they are moved to a
   common point by a certified Taylor continuation with explicit Cauchy-majorant
   tails; Stokes matrices and the monodromy along a full loop are enclosed,
   the classical closed forms are checked for containment, and the cyclic
   relation M = S_0 exp(2 pi i L) S_pi^{-1} is checked entrywise as an overlap.
"""
from fractions import Fraction as Q
from sympy import Matrix, Rational, eye, zeros

SCHEMA = 'pp-irregular-stokes/1'


def _mat(a):
    return Matrix([[Rational(Q(x).numerator, Q(x).denominator) if not hasattr(x, 'is_Rational') else x for x in row] for row in a])


def _packet(m):
    return [[str(x) for x in row] for row in m.tolist()]


# ------------------------------------------------------------- 1. formal normal form
def formal_normal_form(A, order=40):
    """Exact formal fundamental solution at an irregular singular point of rank one at infinity."""
    if not A or type(order) is not int or not 2 <= order <= 400:
        raise ValueError('coefficient list and order 2..400 required')
    As = [_mat(a) for a in A]
    n = As[0].rows
    if any(a.shape != (n, n) for a in As):
        raise ValueError('square matrices of equal size required')
    if any(x.q == 0 for a in As for x in a):
        raise ValueError('rational entries required')
    ev = As[0].eigenvects()
    lam = []
    cols = []
    for val, mult, vecs in ev:
        if mult != 1 or not val.is_Rational:
            raise ValueError('distinct rational leading eigenvalues required')
        v = vecs[0]
        k = 0 if v[0] != 0 else next(i for i in range(n) if v[i] != 0)
        v = v / v[k]
        lam.append(val)
        cols.append(v)
    order_idx = sorted(range(n), key=lambda i: lam[i])
    lam = [lam[i] for i in order_idx]
    P = Matrix.hstack(*[cols[i] for i in order_idx])
    Pi = P.inv()
    B = [Pi * a * P for a in As]
    J = len(B) - 1
    Lam = Matrix.diag(*lam)
    Lp = Matrix.diag(*[B[1][i, i] if J >= 1 else 0 for i in range(n)])
    F = [eye(n)]
    for m in range(1, order + 2):
        # diagonal of F_{m-1} from the diagonal equation at level m (m>=2)
        if m >= 2:
            Fm1 = F[m - 1]
            for i in range(n):
                s = sum(B[1][i, l] * Fm1[l, i] for l in range(n) if l != i)
                s += sum((B[j] * F[m - j])[i, i] for j in range(2, min(m, J) + 1))
                Fm1[i, i] = -s / (m - 1)
        rhs = zeros(n)
        for j in range(1, min(m, J) + 1):
            rhs += B[j] * F[m - j]
        rhs += (m - 1) * F[m - 1] - F[m - 1] * Lp
        Fm = zeros(n)
        for i in range(n):
            for k in range(n):
                if i != k:
                    Fm[i, k] = rhs[i, k] / (lam[k] - lam[i])
        F.append(Fm)
    F = F[:order + 1]
    # exact replay of the defining identity at levels 1..order
    for m in range(1, order + 1):
        lhs = -(m - 1) * F[m - 1] + F[m] * Lam + F[m - 1] * Lp
        rhs = Lam * F[m] + sum((B[j] * F[m - j] for j in range(1, min(m, J) + 1)), zeros(n))
        if lhs != rhs:
            raise ArithmeticError('formal identity failed at level %d' % m)
    return dict(schema=SCHEMA, rank=n, poincare_rank=1, order=order, eigenvalues=[str(x) for x in lam],
                eigenframe=_packet(P), formal_exponents=[str(Lp[i, i]) for i in range(n)],
                coefficients=[_packet(f) for f in F], identity_checked=True,
                solution='Y = P F(z) z^Lambda\' exp(Lambda z), F = sum F_k z^-k, F_0 = I',
                formal_monodromy='exp(2 pi i Lambda\')',
                scope='Poincare rank one, distinct rational leading eigenvalues (unramified Hukuhara-Turrittin); formal series diverge (Gevrey-1)')


def _qf(x):
    from sympy import Rational as R
    x = R(x)
    return Q(int(x.p), int(x.q))


# ------------------------------------------------------------- 2a. late terms
def late_term_stokes(chart, K=None, R=8, dps=40):
    """Stokes multipliers s_0 (ray of lambda_2-lambda_1>0) and s_pi from coefficient asymptotics.

    Convention (2x2, lambda_1<lambda_2, Delta=lambda_2-lambda_1, beta=lambda'_2-lambda'_1):
      (F_k)_{12} ~ (s_0/2 pi i) Gamma(k-beta)/Delta^(k-beta),
      (F_k)_{21} ~ -(s_pi/2 pi i) (-1)^k e^{i pi beta} Gamma(k+beta)/Delta^(k+beta),
    with Y_0=Y_1 S_0 across arg z=0 and Y_2=Y_1 S_pi across arg z=pi.
    Richardson extrapolation of order R in 1/k at k=K-R..K.
    """
    import mpmath as mp
    if chart['rank'] != 2:
        raise ValueError('2x2 system required')
    with mp.workdps(dps):
        lam = [_qf(x) for x in chart['eigenvalues']]
        lp = [_qf(x) for x in chart['formal_exponents']]
        D = _mq(lam[1] - lam[0])
        beta = _mq(lp[1] - lp[0])
        F = chart['coefficients']
        K = len(F) - 1 if K is None else K
        ks = list(range(K - R, K + 1))

        def entry(k, i, j):
            q = Q(F[k][i][j])
            return mp.mpf(q.numerator) / q.denominator
        s0_seq = [2j * mp.pi * entry(k, 0, 1) * D ** (k - beta) / mp.gamma(k - beta) for k in ks]
        sp_seq = [-2j * mp.pi * entry(k, 1, 0) * (-1) ** k * mp.exp(-1j * mp.pi * beta) * D ** (k + beta) / mp.gamma(k + beta) for k in ks]

        def richardson(seq):
            # polynomial extrapolation in h=1/k to h=0
            hs = [mp.mpf(1) / k for k in ks]
            return _neville(hs, seq)
        return dict(s0=richardson(s0_seq), s_pi=richardson(sp_seq), K=K, richardson_order=R)


def _mq(q):
    import mpmath as mp
    q = Q(q)
    return mp.mpf(q.numerator) / q.denominator


def _neville(xs, ys):
    import mpmath as mp
    p = list(ys)
    n = len(xs)
    for m in range(1, n):
        for i in range(n - m):
            p[i] = ((0 - xs[i + m]) * p[i] + (xs[i] - 0) * p[i + 1]) / (xs[i] - xs[i + m])
    return p[0]


# ------------------------------------------------------------- 2b. Borel-Pade-Laplace
def borel_pade_column(chart, j, z, theta, dps=40, terms=None):
    """f_j(z)=e_j+int_0^{infty e^{i theta}} e^{-z zeta} B_j(zeta) d zeta with Pade-continued Borel transform."""
    import mpmath as mp
    with mp.workdps(dps):
        F = chart['coefficients']
        n = chart['rank']
        N = len(F) - 1 if terms is None else terms
        out = []
        for i in range(n):
            ser = []
            for k in range(1, N + 1):
                q = Q(F[k][i][j])
                ser.append(mp.mpf(q.numerator) / q.denominator / mp.factorial(k - 1))
            if all(x == 0 for x in ser):
                out.append(1 if i == j else 0)
                continue
            M = (len(ser) - 1) // 2
            while True:
                try:
                    p, qd = mp.pade(ser, len(ser) - 1 - M, M)
                    break
                except ZeroDivisionError:
                    # degenerate (e.g. terminating or rational) Borel transform: lower the denominator degree
                    M -= 1
                    if M < 0:
                        raise
            ph = mp.expj(theta)

            def integrand(t):
                zeta = t * ph
                return mp.exp(-z * zeta) * mp.polyval(p[::-1], zeta) / mp.polyval(qd[::-1], zeta) * ph
            val = mp.quad(integrand, [0, 1, 4, 16, mp.inf])
            out.append((1 if i == j else 0) + val)
        return out


def borel_pade_stokes(chart, R=6, dps=40, terms=None):
    """Numerical S_0 and S_pi from lateral Borel-Pade-Laplace sums (2x2)."""
    import mpmath as mp
    if chart['rank'] != 2:
        raise ValueError('2x2 system required')
    with mp.workdps(dps):
        lam = [_qf(x) for x in chart['eigenvalues']]
        lp = [_qf(x) for x in chart['formal_exponents']]

        def G(z, theta):
            c0 = borel_pade_column(chart, 0, z, theta, dps, terms)
            c1 = borel_pade_column(chart, 1, z, theta, dps, terms)
            return mp.matrix([[c0[0], c1[0]], [c0[1], c1[1]]])

        def conj(S, z, argz):
            # S_ij -> S_ij * e^{(lambda_j-lambda_i) z} z^{lambda'_j-lambda'_i}, z^. with arg argz
            out = mp.matrix(2, 2)
            for i in range(2):
                for k in range(2):
                    out[i, k] = S[i, k] * mp.exp(_mq(lam[k] - lam[i]) * z) * mp.exp(_mq(lp[k] - lp[i]) * (mp.log(abs(z)) + 1j * argz))
            return out
        zr = mp.mpf(R)
        S0 = conj(mp.inverse(G(zr, -mp.pi / 4)) * G(zr, mp.pi / 4), zr, 0)
        Sp = conj(mp.inverse(G(-zr, -3 * mp.pi / 4)) * G(-zr, 3 * mp.pi / 4), -zr, mp.pi)
        return dict(S0=S0, S_pi=Sp, s0=S0[0, 1], s_pi=Sp[1, 0], radius=R)


def numerical_monodromy(A, z0, radius_steps=48, dps=40, tol=None):
    """Transport matrix of Y'=(sum A_j z^-j)Y once counterclockwise around |z|=|z0| (numerical Taylor)."""
    import mpmath as mp
    with mp.workdps(dps):
        As = [mp.matrix([[mp.mpf(Q(x).numerator) / Q(x).denominator for x in row] for row in a]) for a in A]
        n = As[0].rows
        J = len(As) - 1
        tol = mp.mpf(10) ** (-dps + 5) if tol is None else tol
        T = mp.eye(n)
        r = abs(z0)
        th0 = mp.arg(z0)
        pts = [r * mp.expj(th0 + 2 * mp.pi * k / radius_steps) for k in range(radius_steps + 1)]
        pts[-1] = pts[0]
        for c, d in zip(pts, pts[1:]):
            T = _taylor_step(As, J, c, d - c, tol) * T
        return T


def _taylor_step(As, J, c, h, tol):
    """Fundamental matrix at c+h with value I at c for z^J Y'=(sum_j A_j z^{J-j}) Y."""
    import mpmath as mp
    from math import comb
    n = As[0].rows
    q = [comb(J, l) * c ** (J - l) for l in range(J + 1)]  # z^J=(c+h)^J
    Rl = []
    for l in range(J + 1):
        M = mp.matrix(n, n)
        for j in range(J + 1):
            e = J - j
            if l <= e:
                M += As[j] * (comb(e, l) * c ** (e - l))
        Rl.append(M)
    Y = [mp.eye(n)]
    total = mp.eye(n)
    hp = mp.mpf(1)
    nrm_small = 0
    for m in range(0, 4000):
        acc = mp.matrix(n, n)
        for l in range(J + 1):
            if m - l >= 0:
                acc += Rl[l] * Y[m - l]
        for l in range(1, J + 1):
            if m - l + 1 >= 0:
                acc -= Y[m - l + 1] * (q[l] * (m - l + 1))
        Ynew = acc / (q[0] * (m + 1))
        Y.append(Ynew)
        hp = hp * h
        term = Ynew * hp
        total += term
        if mp.mnorm(term, 1) < tol * mp.mnorm(total, 1):
            nrm_small += 1
            if nrm_small >= 3:
                return total
        else:
            nrm_small = 0
    raise ArithmeticError('Taylor step did not converge')


# ------------------------------------------------------------- 3. certified Kummer Stokes data
def kummer_system(a, b):
    """Y=(w,w'), z w''+(b-z)w'-a w=0:  Y'=(A_0+A_1/z)Y."""
    a, b = Q(a), Q(b)
    return [[[0, 1], [0, 1]], [[0, 0], [a, -b]]]


def kummer_closed_forms(a, b, prec=128):
    """s_0=2 pi i/(Gamma(1-a)Gamma(b-a)), s_pi=-2 pi i e^{i pi(b-2a)}/(Gamma(a)Gamma(1+a-b))."""
    from flint import acb, ctx
    old = ctx.prec
    ctx.prec = prec
    try:
        A, B = _acbq(a), _acbq(b)
        two_pi_i = 2 * acb.pi() * acb(0, 1)
        s0 = two_pi_i * (1 - A).rgamma() * (B - A).rgamma()
        sp = -two_pi_i * (acb.pi() * acb(0, 1) * (B - 2 * A)).exp() * A.rgamma() * (1 + A - B).rgamma()
        return s0, sp
    finally:
        ctx.prec = old


def _acbq(x):
    from flint import acb, arb, fmpq
    x = Q(x)
    return acb(arb(fmpq(x.numerator, x.denominator)))


def _acbg(z):
    from flint import acb, arb, fmpq
    re, im = Q(z[0]), Q(z[1])
    return acb(arb(fmpq(re.numerator, re.denominator)), arb(fmpq(im.numerator, im.denominator)))


def _certified_step(A0, A1, normA0, normA1, c, h, tol_exp=None):
    """Certified fundamental matrix at c+h (value I at c) for Y'=(A_0+A_1/z)Y.

    c, h Gaussian rationals with |h|<=|c|/3.  Coefficients obey
    c(n+1)Y_{n+1}=(A_0 c+A_1-n)Y_n+A_0 Y_{n-1}; the majorant
    B << K/(1-h/rho), K=||A_0||+||A_1||/rho, rho=|c|, gives
    ||Y_n|| <= (kappa)_n/(n! rho^n), kappa=K rho, and the tail beyond N is at most
    T_N/(1-theta), T_N=(kappa)_N/N! x^N, x=|h|/rho, theta=max(1,(kappa+N)/(N+1)) x.
    """
    from flint import acb, arb, acb_mat, ctx
    from math import isqrt
    c2 = c[0] ** 2 + c[1] ** 2
    h2 = h[0] ** 2 + h[1] ** 2
    if not 9 * h2 <= c2:
        raise ValueError('step longer than |c|/3')
    # exact rational lower bound for rho=|c| and upper bound for |h|
    rho_lo = Q(isqrt(int(c2 * 10 ** 12)), 10 ** 6)
    hs_up = Q(isqrt(int(h2 * 10 ** 12)) + 1, 10 ** 6)
    x = hs_up / rho_lo
    kappa = normA0 * rho_lo + normA1 + 1  # +1: rho_lo<=rho slack for K*rho with K evaluated at rho_lo
    kappa = normA0 * (rho_lo + Q(1, 10 ** 6)) + normA1
    C = _acbg(c)
    H = _acbg(h)
    n = 2
    I = acb_mat([[1, 0], [0, 1]])
    M0 = acb_mat([[_acbq(A0[i][j]) for j in range(n)] for i in range(n)])
    M1 = acb_mat([[_acbq(A1[i][j]) for j in range(n)] for i in range(n)])
    Mc = M0 * C + M1
    target = Q(2) ** (-(ctx.prec + 10))
    # choose N with the exact tail below 2^-(prec+10)
    N = 8
    TN = Q(1)
    poch = Q(1)
    while True:
        poch = Q(1)
        for k in range(N):
            poch = poch * (kappa + k) / (k + 1)
        TN = poch * x ** N
        theta = max(Q(1), (kappa + N) / (N + 1)) * x
        if theta < 1 and TN / (1 - theta) < target:
            break
        N += 8
        if N > 4000:
            raise ArithmeticError('tail bound not reached')
    tail = TN / (1 - theta)
    Yprev = acb_mat(2, 2)
    Y = I
    total = I
    hp = acb(1)
    for m in range(0, N - 1):
        Ynext = (Mc * Y - Y * acb(m) + M0 * Yprev) * (1 / (C * (m + 1)))
        Yprev, Y = Y, Ynext
        hp = hp * H
        total = total + Y * hp
    from flint import fmpq
    rad = arb(0, arb(fmpq(tail.numerator, tail.denominator)).upper())
    err = acb(rad, rad)
    return acb_mat([[total[i, j] + err for j in range(2)] for i in range(2)]), N


def certified_transport(A, path):
    """Certified transport matrix along a polygon of Gaussian-rational points (steps <= |c|/3)."""
    from flint import acb_mat
    A0, A1 = A
    nA0 = max(sum(abs(Q(x)) for x in row) for row in A0)
    nA1 = max(sum(abs(Q(x)) for x in row) for row in A1)
    T = acb_mat([[1, 0], [0, 1]])
    orders = []
    for c, d in zip(path, path[1:]):
        h = (Q(d[0]) - Q(c[0]), Q(d[1]) - Q(c[1]))
        S, N = _certified_step(A0, A1, nA0, nA1, (Q(c[0]), Q(c[1])), h)
        T = S * T
        orders.append(N)
    return T, orders


def _arc(r, th0, th1, steps):
    """Gaussian-rational points near the arc of radius r from angle th0 to th1 (inclusive)."""
    import math
    pts = []
    for k in range(steps + 1):
        th = th0 + (th1 - th0) * k / steps
        pts.append((Q(round(r * math.cos(th) * 2 ** 20), 2 ** 20), Q(round(r * math.sin(th) * 2 ** 20), 2 ** 20)))
    return pts


def certified_kummer_stokes(a, b, prec=128, radius=4, steps_per_quarter=6):
    """Arb enclosures of the Kummer Stokes matrices S_0, S_pi and of the loop monodromy."""
    from flint import acb, acb_mat, ctx
    import math
    a, b = Q(a), Q(b)
    old = ctx.prec
    ctx.prec = prec
    try:
        A = kummer_system(a, b)
        A_, B_ = _acbq(a), _acbq(b)
        I = acb(0, 1)
        pi = acb.pi()

        def U(alpha, beta, z):
            return z.hypgeom_u(alpha, beta)

        def col_u(z, phase=acb(1)):
            # phase*U(a,b,z) and derivative -a U(a+1,b+1,z); z given on the principal branch
            return [phase * U(A_, B_, z), phase * (-A_) * U(A_ + 1, B_ + 1, z)]

        def col_e(z, phase):
            # phase*e^z U(b-a,b,-z); derivative phase*e^z [U(b-a,b,-z)+(b-a)U(b-a+1,b+1,-z)]
            w = -z
            u0 = U(B_ - A_, B_, w)
            u1 = U(B_ - A_ + 1, B_ + 1, w)
            ez = z.exp()
            return [phase * ez * u0, phase * ez * (u0 + (B_ - A_) * u1)]

        def mat(c1, c2):
            return acb_mat([[c1[0], c2[0]], [c1[1], c2[1]]])
        r = radius
        zu = (Q(0), Q(r))       # arg pi/2
        zd = (Q(0), Q(-r))      # arg -pi/2 (for Y_0) or 3pi/2 (for Y_2)
        Zu, Zd = _acbg(zu), _acbg(zd)
        Y1_up = mat(col_u(Zu), col_e(Zu, (I * pi * (A_ - B_)).exp()))
        Y0_dn = mat(col_u(Zd), col_e(Zd, (-I * pi * (A_ - B_)).exp()))
        Y2_dn = mat(col_u(Zd, (-2 * pi * I * A_).exp()), col_e(Zd, (I * pi * (A_ - B_)).exp()))
        n = 2 * steps_per_quarter
        cw = _arc(r, math.pi / 2, -math.pi / 2, n)
        cw[0], cw[-1] = zu, zd
        ccw = _arc(r, math.pi / 2, 3 * math.pi / 2, n)
        ccw[0], ccw[-1] = zu, zd
        loop = _arc(r, math.pi / 2, math.pi / 2 + 2 * math.pi, 2 * n)
        loop[0], loop[-1] = zu, zu
        Tcw, o1 = certified_transport(A, cw)
        Tccw, o2 = certified_transport(A, ccw)
        Tloop, o3 = certified_transport(A, loop)
        S0 = (Tcw * Y1_up).inv() * Y0_dn
        Sp = (Tccw * Y1_up).inv() * Y2_dn
        M = Y1_up.inv() * Tloop * Y1_up
        E = acb_mat([[(2 * pi * I * (-A_)).exp(), 0], [0, (2 * pi * I * (A_ - B_)).exp()]])
        cyc = S0 * E * Sp.inv()
        s0_cf, sp_cf = kummer_closed_forms(a, b, prec)
        checks = dict(
            S0_unipotent_upper=bool(S0[0, 0].overlaps(acb(1)) and S0[1, 1].overlaps(acb(1)) and S0[1, 0].overlaps(acb(0))),
            S_pi_unipotent_lower=bool(Sp[0, 0].overlaps(acb(1)) and Sp[1, 1].overlaps(acb(1)) and Sp[0, 1].overlaps(acb(0))),
            s0_contains_closed_form=bool(S0[0, 1].overlaps(s0_cf)),
            s_pi_contains_closed_form=bool(Sp[1, 0].overlaps(sp_cf)),
            cyclic_relation_overlaps=all(M[i, j].overlaps(cyc[i, j]) for i in range(2) for j in range(2)),
            trace_matches_local_exponents_at_0=bool((M[0, 0] + M[1, 1]).overlaps(1 + (-2 * pi * I * B_).exp())),
            det_matches=bool((M[0, 0] * M[1, 1] - M[0, 1] * M[1, 0]).overlaps((-2 * pi * I * B_).exp())))
        def s(x):
            return x.str(radius=True) if hasattr(x, 'str') else str(x)
        out = dict(schema=SCHEMA, equation='z w\'\'+(b-z)w\'-a w=0', a=str(a), b=str(b), precision_bits=prec,
                   formal_exponents=[str(-a), str(a - b)], eigenvalues=['0', '1'], loop_radius=r,
                   taylor_orders=dict(clockwise=o1, counterclockwise=o2, loop=o3),
                   s0=s(S0[0, 1]), s_pi=s(Sp[1, 0]), s0_closed_form=s(s0_cf), s_pi_closed_form=s(sp_cf),
                   s0_radius=float(S0[0, 1].rad()), s_pi_radius=float(Sp[1, 0].rad()),
                   monodromy=[[s(M[i, j]) for j in range(2)] for i in range(2)],
                   monodromy_max_radius=max(float(M[i, j].rad()) for i in range(2) for j in range(2)),
                   checks=checks, certified=all(checks.values()),
                   sectorial_solutions=dict(Y1='[U(a,b,z), e^{i pi(a-b)} e^z U(b-a,b,z e^{-i pi})] on arg z in (-0,pi+0)',
                                            Y0='[U(a,b,z), e^{-i pi(a-b)} e^z U(b-a,b,z e^{i pi})] on arg z in (-pi-0,0+0)',
                                            Y2='Y0(z e^{-2 pi i}) exp(2 pi i L)'),
                   conventions='Y0=Y1 S0 across arg z=0, Y2=Y1 S_pi across arg z=pi, Y1(z e^{2 pi i})=Y1(z) M')
        return out, dict(S0=S0, S_pi=Sp, M=M)
    finally:
        ctx.prec = old


def numerical_cyclic_relation(A, chart, R=6, dps=40, steps=64):
    """Numerical check of M = S_0 exp(2 pi i Lambda') S_pi^{-1} for a 2x2 system (Borel-Pade + Taylor transport)."""
    import mpmath as mp
    with mp.workdps(dps):
        bp = borel_pade_stokes(chart, R=R, dps=dps)
        lam = [_qf(x) for x in chart['eigenvalues']]
        lp = [_qf(x) for x in chart['formal_exponents']]
        z1 = mp.mpc(0, R)
        c0 = borel_pade_column(chart, 0, z1, -mp.pi / 2, dps)
        c1 = borel_pade_column(chart, 1, z1, -mp.pi / 2, dps)
        G = mp.matrix([[c0[0], c1[0]], [c0[1], c1[1]]])
        D = mp.diag([mp.exp(_mq(lam[j]) * z1) * mp.exp(_mq(lp[j]) * (mp.log(R) + 1j * mp.pi / 2)) for j in range(2)])
        P = mp.matrix([[_mq(Q(x)) for x in row] for row in chart['eigenframe']])
        Y1 = P * G * D
        T = numerical_monodromy(A, z1, radius_steps=steps, dps=dps)
        M = mp.inverse(Y1) * T * Y1
        E = mp.diag([mp.expj(2 * mp.pi * _mq(lp[j])) for j in range(2)])
        cyc = bp['S0'] * E * mp.inverse(bp['S_pi'])
        diff = mp.mnorm(M - cyc, 1)
        return dict(monodromy=M, product=cyc, max_difference=diff, s0=bp['s0'], s_pi=bp['s_pi'],
                    trace=M[0, 0] + M[1, 1])
