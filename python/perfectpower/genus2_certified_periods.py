"""Certified period packet of a split genus-two curve with real branch points.

Curve C: y^2=P(z)=Q(z^2), Q(u)=(u-u1)(u-u2)(u-u3), 0<u1<u2<u3 rational, so
the six branch points e_1<...<e_6 are -sqrt(u3),-sqrt(u2),-sqrt(u1),sqrt(u1),
sqrt(u2),sqrt(u3). Quotients (curve_structure): E1: v^2=Q(u) by (u,v)=(z^2,y)
and E2: w^2=u Q(u) by (u,w)=(z^2,z y), with exact pullbacks
  phi1^*(du/v)=2 z dz/y,   phi2^*(du/w)=2 dz/y.

Cycles. gamma_j is the closed lift of a loop around [e_j,e_{j+1}]; it equals
2 int_{e_j}^{e_{j+1}} omega/y_u, where y_u is the boundary value from the
upper half plane of the branch y~z^3 at infinity: y_u=i^{6-j} sqrt|P| there.
Every integral is reduced, by z=a+(b-a)(1-cos t)/2, to an integrand analytic
on a neighbourhood of [0,pi], and evaluated by Arb's rigorous integration
(python-flint acb.integral), so all results are balls with proven radii.

The same construction applies to the elliptic quotients (branch points
u1<u2<u3 and the point at infinity for E1; 0<u1<u2<u3 for E2).
"""
from fractions import Fraction as Q
from flint import acb, arb, arb_mat, acb_mat, ctx

ctx.prec = 200


def _sqrt_ball(x):
    return arb(x).sqrt()


def segment_integral(roots, a_index, f_power, *, extra=None):
    """2 int_{e_a}^{e_{a+1}} z^f_power dz/y_u for y^2=prod(z-e_k) (sorted roots).

    extra multiplies the integrand by a polynomial in z (list of coefficients) if given.
    Returns an acb ball. Requires the roots to be real and distinct.
    """
    e = [arb(r) for r in roots]
    n = len(e)
    a, b = e[a_index], e[a_index + 1]
    others = [e[k] for k in range(n) if k not in (a_index, a_index + 1)]
    above = n - (a_index + 1)  # number of roots strictly above the interval
    # sqrt|P| = sqrt((z-a)(b-z)) * sqrt(|R(z)|), R the product of the other factors.
    # sign of R on the interval: (-1)^(number of other roots above).
    above_others = above - 1
    half = (b - a)/2
    mid = (a + b)/2

    def integrand(t, analytic):
        z = mid - half*t.cos()
        R = acb(1)
        for r in others:
            R *= (z - r)
        Rabs = R if above_others % 2 == 0 else -R
        val = z**f_power
        if extra is not None:
            val = val*sum((acb(c)*z**i for i, c in enumerate(extra)), acb(0))
        return val/Rabs.sqrt(analytic=analytic)
    I = acb.integral(integrand, 0, arb.pi())
    # y_u = i^above * sqrt|P| on (e_a, e_{a+1}).
    phase = [acb(1), acb(0, 1), acb(-1), acb(0, -1)][above % 4]
    return 2*I/phase


def genus2_roots(u):
    s = [_sqrt_ball(x) for x in u]
    return [-s[2], -s[1], -s[0], s[0], s[1], s[2]]


def genus2_cycle_periods(u):
    """Periods of eta_0=dz/y and eta_1=z dz/y over gamma_1..gamma_5."""
    roots = genus2_roots(u)
    return [[segment_integral(roots, j, p) for j in range(5)] for p in (0, 1)]


# Symplectic basis in terms of the chain gamma_1..gamma_4 (gamma_j.gamma_{j+1}=sigma):
# a1=gamma1, a2=gamma3, b1=gamma2+gamma4, b2=gamma4.
BASIS = {'a1': (1, 0, 0, 0, 0), 'a2': (0, 0, 1, 0, 0), 'b1': (0, 1, 0, 1, 0), 'b2': (0, 0, 0, 1, 0)}


def chain_intersection(sigma=1):
    """Intersection matrix of gamma_1..gamma_5 on the chain: gamma_j.gamma_{j+1}=sigma."""
    M = [[0]*5 for _ in range(5)]
    for j in range(4):
        M[j][j + 1] = sigma
        M[j + 1][j] = -sigma
    return M


def combine(periods, coeffs):
    return [sum((c*p[j] for j, c in enumerate(coeffs)), acb(0)) for p in periods]


def period_matrix(u):
    """Normalised Omega=A^{-1}B and the certified Riemann checks."""
    P = genus2_cycle_periods(u)
    cols = {k: combine(P, c) for k, c in BASIS.items()}
    A = acb_mat([[cols['a1'][0], cols['a2'][0]], [cols['a1'][1], cols['a2'][1]]])
    B = acb_mat([[cols['b1'][0], cols['b2'][0]], [cols['b1'][1], cols['b2'][1]]])
    Om = A.solve(B)
    sym = Om[0, 1] - Om[1, 0]
    im = [[Om[i, j].imag for j in range(2)] for i in range(2)]
    det = im[0][0]*im[1][1] - im[0][1]*im[1][0]
    return {'cycle_periods': P, 'A': A, 'B': B, 'Omega': Om, 'symmetry_defect': sym,
            'Im_Omega': im, 'Im_trace': im[0][0] + im[1][1], 'Im_det': det}


def elliptic_lattice(roots_sorted, include_infinity):
    """Two generating periods of du/sqrt(f) for a cubic (with infinity) or quartic with real roots.

    For v^2=(u-r1)(u-r2)(u-r3): gamma_1 around [r1,r2] and gamma_2 around [r2,r3].
    For w^2=u(u-u1)(u-u2)(u-u3): roots 0,u1,u2,u3, gamma_1 around [0,u1], gamma_2 around [u1,u2].
    """
    w1 = segment_integral(roots_sorted, 0, 0)
    w2 = segment_integral(roots_sorted, 1, 0)
    return w1, w2


def integer_coordinates(value, w1, w2):
    """Solve value=m w1+n w2 over the reals (2x2 ball system) and certify the unique integers."""
    M = arb_mat([[w1.real, w2.real], [w1.imag, w2.imag]])
    rhs = arb_mat([[value.real], [value.imag]])
    sol = M.solve(rhs)
    out = []
    for i in range(2):
        x = sol[i, 0]
        lo, hi = x.lower(), x.upper()
        cands = [k for k in range(int(lo.floor().unique_fmpz()) - 1, int(hi.ceil().unique_fmpz()) + 2) if lo <= k <= hi]
        if len(cands) != 1:
            raise ArithmeticError('integer coordinate not certified: %s' % x)
        out.append((cands[0], x))
    return out


def cycle_map(u):
    """Certified integer images of gamma_1..gamma_5 in H1(E1,Z) and H1(E2,Z)."""
    P = genus2_cycle_periods(u)
    r = sorted(u)
    E1 = elliptic_lattice([arb(x) for x in r], True)
    E2 = elliptic_lattice([arb(0)] + [arb(x) for x in r], False)
    maps = {'E1': [], 'E2': []}
    for j in range(5):
        # phi1^*(du/v)=2 eta_1, phi2^*(du/w)=2 eta_0.
        m1 = integer_coordinates(2*P[1][j], *E1)
        m2 = integer_coordinates(2*P[0][j], *E2)
        maps['E1'].append([m[0] for m in m1]); maps['E2'].append([m[0] for m in m2])
    return {'maps': maps, 'E1_lattice': E1, 'E2_lattice': E2, 'genus2_periods': P}


def polarization_identity(maps, sigma, eps1, eps2):
    """Check sum_k phi_k* x . phi_k* y = 2 x.y on the chain gamma_1..gamma_5.

    eps_k is the elliptic intersection number of that curve's (gamma_1,gamma_2) basis.
    Returns the maximum absolute defect over all pairs.
    """
    C = chain_intersection(sigma)
    def ell(m, n, eps):
        return eps*(m[0]*n[1] - m[1]*n[0])
    worst = 0
    for i in range(5):
        for j in range(5):
            lhs = ell(maps['E1'][i], maps['E1'][j], eps1) + ell(maps['E2'][i], maps['E2'][j], eps2)
            worst = max(worst, abs(lhs - 2*C[i][j]))
    return worst


def agm_periods(r1, r2, r3):
    """Independent closed forms for v^2=(u-r1)(u-r2)(u-r3), r1<r2<r3 real.

    int_{r1}^{r2} du/sqrt|f| = pi/AGM(sqrt(r3-r1), sqrt(r3-r2)) and
    int_{r2}^{r3} du/sqrt|f| = pi/AGM(sqrt(r3-r1), sqrt(r2-r1)).
    """
    r1, r2, r3 = arb(r1), arb(r2), arb(r3)
    I12 = arb.pi()/((r3 - r1).sqrt().agm((r3 - r2).sqrt()))
    I23 = arb.pi()/((r3 - r1).sqrt().agm((r2 - r1).sqrt()))
    return I12, I23


def loop_integral(roots, a_index, f_power, radius):
    """Clockwise circle around [e_a,e_{a+1}] with y continued analytically: independent of segment_integral.

    On the disc, sqrt((z-a)(z-b))=(z-m)sqrt(1-h^2/(z-m)^2) (principal, |z-m|>h),
    sqrt(z-r)=i sqrt(r-z) for roots r above and principal for roots below.
    This branch equals y_u on the upper edge, and the clockwise loop equals
    2 int_a^b omega/y_u. The circle must exclude every other root.
    """
    e = [arb(r) for r in roots]
    a, b = e[a_index], e[a_index + 1]
    m, h = (a + b)/2, (b - a)/2
    R = arb(radius)
    others = [(e[k], k > a_index + 1) for k in range(len(e)) if k not in (a_index, a_index + 1)]
    if not (R > h and all(abs(r - m) > R for r, _ in others)):
        raise ValueError('circle must enclose the segment and exclude other branch points')

    def integrand(t, analytic):
        z = m + R*(acb(0, -1)*t).exp()  # clockwise
        dz = -acb(0, 1)*(z - m)
        x = z - m
        root = x*(1 - h*h/(x*x)).sqrt(analytic=analytic)
        for r, above in others:
            root *= acb(0, 1)*(r - z).sqrt(analytic=analytic) if above else (z - r).sqrt(analytic=analytic)
        return z**f_power*dz/root
    return acb.integral(integrand, 0, 2*arb.pi())


def node_family(delta):
    """Q=(u-1)(u-4)(u-4-delta): the branch-point pairs (2,sqrt(4+delta)) and their mirrors collide."""
    return [arb(1), arb(4), arb(4) + arb(delta)]


def picard_lefschetz(deltas, f_power=0):
    """Certified local monodromy at the node: P4+(P5/(pi i)) log delta converges as delta->0.

    As delta circles 0 the branch point sqrt(4+delta) makes one full turn around 2,
    a full twist sigma^2 of the base. By the Birman-Hilden lift a half twist is the
    Dehn twist T_v about the vanishing cycle v=gamma_5, so the monodromy is T_v^2
    and the dual period gamma_4 shifts by 2 P5 per turn: P4=-(P5/(pi i)) log delta+hol.
    Composition: b1=gamma_2+gamma_4 meets gamma_1 with b1.gamma_1=-1 and gamma_5
    with b1.gamma_5=+1, so T_{gamma_1}^2 T_{gamma_5}^2 b1=b1-2gamma_1+2gamma_5. By the
    z->-z symmetry P(gamma_1)=P(gamma_5), so the period of b1 has no logarithm. Also returns the free log
    coefficient fitted between consecutive deltas, divided by P5/(2 pi i).
    """
    rows = []
    prev = None
    for d in deltas:
        P = [segment_integral(genus2_roots(node_family(d)), j, f_power) for j in range(5)]
        L = arb(d).log()
        pi_i = arb.pi()*acb(0, 1)
        row = {'delta': d, 'P_vanishing': P[4], 'P_mirror_vanishing': P[0], 'P_dual': P[3],
               'regularised': P[3] + P[4]/pi_i*L,
               # b1.gamma_1=gamma_2.gamma_1=-1 and b1.gamma_5=gamma_4.gamma_5=+1: opposite twists.
               'regularised_b1': (P[1] + P[3]) + (P[4] - P[0])/pi_i*L,
               'b1_period': P[1] + P[3],
               'half_coefficient': P[3] + P[4]/(2*pi_i)*L}
        if prev is not None:
            c = (P[3] - prev[1][3])/(L - prev[0])
            row['fitted_coefficient_over_P5_2pii'] = c/(P[4]/(2*pi_i))
        rows.append(row)
        prev = (L, P)
    return rows


def omega_from_quotients(u):
    """Rebuild A, B and Omega from the elliptic lattices and the certified integer cycle map.

    eta_0=(1/2)phi2^*(du/w) and eta_1=(1/2)phi1^*(du/v), so the period of eta_0 over
    gamma_j is (m w1+n w2)/2 with (m,n) its E2 image, and similarly for eta_1 and E1.
    """
    cm = cycle_map(u)
    W = cm['E1_lattice']; w = cm['E2_lattice']
    def per(j, k):
        if k == 0:
            m, n = cm['maps']['E2'][j]; return (m*w[0] + n*w[1])/2
        m, n = cm['maps']['E1'][j]; return (m*W[0] + n*W[1])/2
    cols = {name: [sum((c*per(j, k) for j, c in enumerate(coeffs)), acb(0)) for k in (0, 1)] for name, coeffs in BASIS.items()}
    A = acb_mat([[cols['a1'][0], cols['a2'][0]], [cols['a1'][1], cols['a2'][1]]])
    B = acb_mat([[cols['b1'][0], cols['b2'][0]], [cols['b1'][1], cols['b2'][1]]])
    return {'cycle_map': cm, 'Omega': A.solve(B), 'tau_E1': W[1]/W[0], 'tau_E2': w[1]/w[0]}


def ball(x):
    return str(x)
