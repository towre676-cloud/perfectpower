"""Arb-certified spectral gap of the certified whole-line wall.

Input: the interval certificate of wall_profile_intervals (a C2 trial profile
a(x) and an exact solution w with ||w-a||_Q <= eta, ||w-a||_inf <= eps).

Claim certified here (x=sqrt(lambda/2) rho, operator L/k2, k2=lambda/2,
half-line reflection sectors). For every f in H1 with f orthogonal to the
translation mode Phi'=w',
    <f,(L/k2) f> >= gamma ||f||^2,   gamma>0 an Arb lower bound,
so L>=0, ker L=span(Phi'), and the radial spectrum below gamma k2 v^2 is {0}.

Proof skeleton (each numerical inequality is an outward-rounded Arb test):
  1. Pointwise Schur/Young bound of the Hessian form at the exact solution:
       q(f) >= q_ref(f_u) - E||f_u||^2 + F_y||f_y||^2 + F_h||f_h||^2,
     q_ref = -d^2+6 tanh^2-2 on the source component.
  2. q_ref has spectrum {0,3} u [4,inf) on the line (exact SUSY chain);
     on the Neumann (translation) half-line it is {0} u [4,inf) with ground
     state sech^2, on the Dirichlet (opposite) half-line it is {3} u [4,inf).
  3. Orthogonality to w' controls the sech^2 component:
       |<e0,f_u>| <= Delta ||f||,  Delta^2=(3/2)(||a_u'-sech^2||+||a_y'||+... +eta/sqrt d)^2.
  4. gamma=min(4-E,F_y,F_h)-4 Delta^2 (translation) and min(3-E,F_y,F_h)
     (opposite sector).
The infinite tail x>22 is analytic: the trial is the exact vacuum there.
"""
from fractions import Fraction
from flint import arb, arb_poly, ctx
from .wall_profile_intervals import ball, bernstein_range, absolute_bound, force, quintic, check_seed

TANH_SECOND_MAX = '0.7699'   # max|tanh''| = 4/(3 sqrt 3) = 0.76980...
SECH2_SECOND_MAX = '2'       # max|(sech^2)''| = max sech^2|6 tanh^2-2| = 2 (at x=0)


def _arb_from_string(s):
    """Arb's printed ball contains the printed-from ball, so parsing is outward."""
    return arb(s)


def _cell_taylor_gap(p, f0, f1, dx, second_max):
    """sup_t |p(t)-f(x_m+dx(t-1/2))| from a first-order Taylor model plus remainder."""
    lin = arb_poly([f0 - f1*dx/2, f1*dx])
    return absolute_bound(p - lin) + ball(Fraction(second_max))/2*(dx/2)**2


def certify_gap(seed, *, precision=160, tau='0.001', theta='0.001'):
    """Return Arb bounds proving the translation-complement gap of the certified wall."""
    old = ctx.prec
    ctx.prec = precision
    try:
        base = check_seed(seed, precision=precision)
        return _certify(seed, base, ball(tau), ball(theta))
    finally:
        ctx.prec = old


def _certify(seed, base, tau, theta):
    P = {n: ball(q) for n, q in seed['parameters'].items()}
    for name, rad in seed.get('parameter_radii', {}).items():
        P[name] = arb(P[name], ball(rad))
    l, a, m, H, h0, kap = [P[k] for k in ['lambda', 'alpha', 'mu', 'lambda_H', 'h0', 'kappa']]
    k2 = l/2
    R = ball(seed['radius']); n = seed['segments']; dx = R/n
    rows = [[ball(Fraction.from_float(float.fromhex(v))) for v in row] for row in seed['values_hex']]
    rows[0][0] = arb(0); rows[0][4] = arb(0); rows[0][5] = arb(0)
    rows[-1][0] = arb(1); rows[-1][1] = -a/m**2; rows[-1][2] = h0
    rows[-1][3:] = [arb(0), arb(0), arb(0)]
    dd = [force(row[:3], P) for row in rows]

    umax = hmax = rsmax = rhmax = diff = arb(0)
    hhh_min = arb(10)**6
    L2 = {'du_minus_sech2': arb(0), 'dy': arb(0), 'dh': arb(0)}
    for j in range(n):
        u, y, h = [quintic((rows[j][i], rows[j][i+3]), (rows[j+1][i], rows[j+1][i+3]), dd[j][i], dd[j+1][i], dx)
                   for i in range(3)]
        xm = dx*j + dx/2
        umax = max(umax, absolute_bound(u)); hmax = max(hmax, absolute_bound(h))
        rsmax = max(rsmax, absolute_bound(y + (a/m**2)*u*u))
        rhmax = max(rhmax, absolute_bound(h*h - h0**2 + kap/H*(u*u - 1)))
        lo, _ = bernstein_range(H*(3*h*h - h0*h0) + kap*(u*u - 1))
        hhh_min = min(hhh_min, lo)
        t, s = xm.tanh(), xm.sech()**2
        diff = max(diff, _cell_taylor_gap(u, t, s, dx, TANH_SECOND_MAX).upper())
        du = u.derivative()*(1/dx)
        g = _cell_taylor_gap(du, s, -2*s*t, dx, SECH2_SECOND_MAX)
        L2['du_minus_sech2'] += dx*g*g
        L2['dy'] += dx*absolute_bound(y.derivative()*(1/dx))**2
        L2['dh'] += dx*absolute_bound(h.derivative()*(1/dx))**2
    # Tail x>=R: trial is the exact vacuum. |1-tanh x|<=2e^{-2x}; int_R^inf sech^4<=4e^{-4R};
    # H_hh(vacuum)=2 lambda_H h0^2.
    diff = max(diff, (2*(-2*R).exp()).upper())
    hhh_min = min(hhh_min, (2*H*h0*h0).lower())
    A2 = L2['du_minus_sech2'] + 4*(-4*R).exp() + L2['dy'] + L2['dh']

    B = base['bounds_Arb']
    eps = _arb_from_string(B['uniform_solution_error_upper']).upper()
    ey = _arb_from_string(B['singlet_solution_error_upper']).upper()
    res_L2 = _arb_from_string(B['residual_L2_upper']).upper()
    d, c = ball('0.25'), ball('0.5')
    eta = res_L2/c.sqrt()                      # ||w-a||_Q <= eta
    Bu, Bh = umax + eps, hmax + eps
    dev = diff + eps                           # |u-tanh| on the whole half-line
    source_dev = 6*dev*(2 + dev)
    rs = rsmax + ey + a/m**2*(2*umax + eps)*eps
    rh = rhmax + (2*hmax + eps)*eps + kap/H*(2*umax + eps)*eps
    hhh = hhh_min - 3*H*(2*hmax + eps)*eps - kap*(2*umax + eps)*eps
    BH = hhh/k2
    if not BH > 0:
        raise ArithmeticError('Higgs Hessian floor not positive')
    mediator_penalty = 4*a*a*Bu*Bu/(m*m*k2)*tau/(1 - tau)
    Higgs_penalty = (2*kap*Bu*Bh/k2)**2/(theta*BH)
    E = source_dev + 2*a*rs/k2 + kap*rh/k2 + mediator_penalty + Higgs_penalty
    Fy = tau*m*m/k2
    Fh = (1 - theta)*BH
    Delta2 = ball(Fraction(3, 2))*(A2.sqrt() + eta/d.sqrt())**2
    low = lambda *vals: min(v.lower() for v in vals)   # exact endpoints: comparisons are decidable
    gamma_translation = low(4 - E, Fy, Fh) - (4*Delta2).upper()
    gamma_opposite = low(3 - E, Fy, Fh)
    gamma = low(gamma_translation, gamma_opposite)
    if not gamma > 0:
        raise ArithmeticError('gap certificate failed')
    edge = 2*H*h0*h0/k2                        # Rayleigh upper bound for the essential-spectrum edge
    v = ball(30000)
    out = {'source_reference_deviation_upper': dev, 'source_error_E_upper': E,
           'source_dev_term': source_dev, 'singlet_residual_term': 2*a*rs/k2, 'Higgs_residual_term': kap*rh/k2,
           'mediator_Schur_penalty': mediator_penalty, 'Higgs_Schur_penalty': Higgs_penalty,
           'singlet_floor_Fy': Fy, 'Higgs_floor_Fh': Fh, 'Higgs_Hessian_min_over_k2': BH,
           'zero_mode_leakage_Delta2_upper': Delta2, 'trial_L2_sq_du_minus_sech2': L2['du_minus_sech2'],
           'trial_L2_sq_dy': L2['dy'], 'trial_L2_sq_dh': L2['dh'], 'eta_Q_error_upper': eta,
           'gamma_translation_sector_lower': gamma_translation, 'gamma_opposite_sector_lower': gamma_opposite,
           'gamma_lower': gamma, 'essential_edge_upper': edge, 'gamma_over_edge_lower': gamma/edge,
           'gap_GeV2_lower': gamma*k2*v*v, 'gap_GeV_lower': (gamma*k2).sqrt()*v,
           'Higgs_threshold_GeV': (2*H).sqrt()*h0*v, 'source_shape_mode_GeV_reference': (3*k2).sqrt()*v}
    return {'format': 'pp-wall-certified-gap/1', 'precision_bits': ctx.prec,
            'tau': str(tau), 'theta': str(theta),
            'base_certificate_flags': {k: base[k] for k in ('continuous_whole_line_wall_existence_certified',
                                                            'P5_Higgs_positive', 'whole_line_asymptotic_vacuum_certified')},
            'bounds_Arb': {k: str(v) for k, v in out.items()},
            'bounds_display_float': {k: float(v.mid()) for k, v in out.items()},
            'kernel_is_translation_only_certified': True,
            'nonnegative_certified': True,
            'gap_certified_positive': True}


def exact_identities():
    """SymPy checks of the analytic ingredients (SUSY chain, Young/Schur, zero-mode norm)."""
    import sympy as s
    x = s.Symbol('x', real=True)
    f = s.Function('f')(x)
    t, sc = s.tanh(x), 1/s.cosh(x)
    A = lambda g: s.diff(g, x) + 2*t*g
    Ad = lambda g: -s.diff(g, x) + 2*t*g
    Bm = lambda g: s.diff(g, x) + t*g
    Bd = lambda g: -s.diff(g, x) + t*g
    checks = {
        'AdA_is_kink_operator': Ad(A(f)) - (-s.diff(f, x, 2) + (6*t**2 - 2)*f),
        'AAd_is_4_minus_2sech2': A(Ad(f)) - (-s.diff(f, x, 2) + (4 - 2*sc**2)*f),
        'BdB_is_1_minus_2sech2': Bd(Bm(f)) - (-s.diff(f, x, 2) + (1 - 2*sc**2)*f),
        'BBd_is_free_plus_1': Bm(Bd(f)) - (-s.diff(f, x, 2) + f),
        'zero_mode_sech2': A(sc**2),
        'shape_mode_sech_tanh_eigen_3': -s.diff(sc*t, x, 2) + (6*t**2 - 2)*sc*t - 3*sc*t,
        'sech_ground_state_of_minus_2sech2': -s.diff(sc, x, 2) - 2*sc**2*sc + sc,
        'sech2_second_derivative': s.diff(sc**2, x, 2) - sc**2*(6*t**2 - 2),
        'tanh_second_derivative': s.diff(t, x, 2) + 2*sc**2*t,
    }
    out = {k: s.simplify(v.rewrite(s.exp)) for k, v in checks.items()}
    out['half_line_sech4_integral'] = s.integrate(sc**4, (x, 0, s.oo)) - s.Rational(2, 3)
    # Young: 2|b f g| <= (1-tau) M g^2 + b^2 f^2/((1-tau) M); excess over b^2/M is b^2 tau/((1-tau)M).
    b, M, tau = s.symbols('b M tau', positive=True)
    out['Schur_excess'] = s.simplify(b**2/((1 - tau)*M) - b**2/M - b**2*tau/((1 - tau)*M))
    # max |tanh''| = 4/(3 sqrt3) at tanh^2=1/3 and |(sech^2)''|<=2.
    out['tanh_second_max'] = s.simplify(2*(1 - s.Rational(1, 3))*s.sqrt(s.Rational(1, 3)) - 4/(3*s.sqrt(3)))
    if any(v != 0 for v in out.values()):
        raise ArithmeticError('identity failed: %s' % out)
    return {k: str(v) for k, v in out.items()}
