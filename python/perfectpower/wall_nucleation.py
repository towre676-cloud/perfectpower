"""Finite-temperature character of the CP transition and nucleation of the biased vacua.

Two questions for the supplied spectator model:

1. Is the CP (Z2) transition near 60 TeV first order? phi is a gauge
   singlet, so its effective potential is gauge independent up to
   kappa-suppressed Higgs loops. The leading Arnold-Espinosa resummed
   high-temperature potential along phi is
   V=(cT^2-lam v^2)phi^2/2+lam phi^4/4-(T/12 pi)(cT^2-lam v^2+3 lam phi^2)^{3/2},
   with c the one-loop Debye coefficient. Its self-loop "barrier" is
   tested for perturbative control.

2. Can the late bias h remove the false vacuum by bubble nucleation? The
   biased source potential lam/4(phi^2-v_T^2)^2-h phi is reduced to
   V=(phi^2-1)^2/4-eps phi with eps=h/(lam v_T^3), v_T^2=v^2-cT^2/lam.
   O(3) and O(4) bounces are computed by shooting. Then S3=(v_T/sqrt lam) s3
   and S4=s4/lam. A Coleman-Glaser-Martin reduced-functional argument
   bounds the full three-field action by the single-field one.

Floating-point bounces with virial and thin-wall checks; the fluctuation
determinant is replaced by a declared prefactor band, not computed.
"""
from math import pi, sqrt, log, gamma
import numpy as np
from scipy.integrate import solve_ivp, quad
from scipy.optimize import brentq
from scipy.special import iv, ive

EPS_SPINODAL = 2/(3*sqrt(3))


def reduced_vacua(eps):
    """Ordered real roots of phi^3-phi-eps: false vacuum, barrier top, true vacuum."""
    if not 0 < eps < EPS_SPINODAL:
        raise ValueError('0<eps<2/(3 sqrt 3) required for two minima')
    r = np.sort(np.roots([1., 0., -1., -eps]).real)
    return r[0], r[1], r[2]


def V(x, eps):
    return (x*x - 1)**2/4 - eps*x


def bounce(eps, d, *, rtol=1e-11, iterations=200):
    """Radial O(d) bounce of V=(phi^2-1)^2/4-eps*phi from the false vacuum near -1.

    Shooting on phi(0) between the exit point (V=V_f on the true side) and the
    true vacuum, parametrised as phi(0)=phi_t-(phi_t-phi_e)exp(-x) so that the
    exponentially thin-walled limit is reachable. Overshoot means crossing
    phi_f; undershoot means phi'=0 before it. Returns s_d and checks.
    """
    if d not in (3, 4):
        raise ValueError('d=3 (thermal) or d=4 (quantum) bounces only')
    f, b, t = reduced_vacua(eps)
    Vf = V(f, eps)
    e = brentq(lambda x: V(x, eps) - Vf, b, t)
    dV = lambda x: x*x*x - x - eps

    kap = sqrt(3*t*t - 1)
    if d == 3:
        g = lambda z: np.sinh(z)/z if z > 1e-8 else 1 + z*z/6
        gp = lambda z: (np.cosh(z)/z - np.sinh(z)/z**2) if z > 1e-4 else z/3
        logg = lambda z: z + np.log1p(-np.exp(-2*z)) - np.log(2*z) if z > 1e-4 else np.log1p(z*z/6)
    else:
        g = lambda z: 2*iv(1, z)/z if z > 1e-8 else 1 + z*z/8
        gp = lambda z: 2*iv(2, z)/z if z > 1e-4 else z/4
        logg = lambda z: np.log(2*ive(1, z)) + z - np.log(z) if z > 1e-4 else np.log1p(z*z/8)

    def shoot(x, dense=False):
        # Linearised solution about the true vacuum, phi-t=-delta*g(kap r),
        # followed analytically until |phi-t| reaches 1e-4 (or from r0=1e-6).
        delta = (t - e)*np.exp(-x)
        z = 1e-6*kap
        if delta*g(z) < 1e-4:
            z = brentq(lambda z: logg(z) + np.log(delta) - np.log(1e-4), 1e-6*kap, 800.)
        r0 = z/kap
        y0 = [t - delta*g(z), -delta*kap*gp(z)]
        over = lambda r, y: y[0] - f
        over.terminal = True; over.direction = -1
        under = lambda r, y: y[1]
        under.terminal = True; under.direction = 1
        rhs = lambda r, y: [y[1], dV(y[0]) - (d - 1)/r*y[1]]
        sol = solve_ivp(rhs, (r0, 1e4), y0, method='DOP853', rtol=rtol, atol=1e-14,
                        events=(over, under), dense_output=dense)
        if sol.t_events[0].size:
            return 1, sol
        if sol.t_events[1].size:
            return -1, sol
        return 0, sol

    lo, hi = 0., 1.
    while shoot(hi)[0] < 0:
        lo, hi = hi, 2*hi + 1
        if hi > 600:
            raise ArithmeticError('thin-wall limit beyond the shooting range')
    for _ in range(iterations):
        mid = (lo + hi)/2
        if shoot(mid)[0] > 0:
            hi = mid
        else:
            lo = mid
        if hi - lo < 1e-15*max(1., hi):
            break
    _, sol = shoot(lo, dense=True)
    # Integrate up to the turning region; beyond it the tail is exponentially small.
    rmax = sol.t[-1]
    rs = np.linspace(sol.t[0], rmax, 40001)
    y = sol.sol(rs)
    keep = (y[0] - f) > 1e-7*(t - f)
    rs, y = rs[keep], y[:, keep]
    w = rs**(d - 1)
    omega = 2*pi**(d/2)/gamma(d/2)
    T = omega*np.trapezoid(w*y[1]**2/2, rs)
    # Interior ball skipped by the linearised start: phi=t to 1e-4 there.
    r0 = sol.t[0]
    U = omega*(np.trapezoid(w*(V(y[0], eps) - Vf), rs) + r0**d/d*(V(t, eps) - Vf))
    S = (2/d)*T
    return {'eps': eps, 'd': d, 's': S, 'kinetic': T, 'potential': U,
            'virial_defect': ((d - 2)*T + d*U)/T, 'phi0': float(y[0][0]),
            'false': f, 'true': t, 'delta_V': Vf - V(t, eps),
            'radius_half_point': float(rs[np.argmin(abs(y[0] - (f + t)/2))]),
            'profile_r': rs[::200].tolist(), 'profile_phi': y[0][::200].tolist()}


def thin_wall(eps, d):
    """Thin-wall action with sigma=2 sqrt2/3 and the exact vacuum energy difference."""
    f, b, t = reduced_vacua(eps)
    dv = V(f, eps) - V(t, eps)
    sig = 2*sqrt(2)/3
    return 16*pi*sig**3/(3*dv*dv) if d == 3 else 27*pi*pi*sig**4/(2*dv**3)


def lifting_ratio(prof_r, prof_phi, d, a, mu, beta, h0, vT_over_v):
    """delta in S1<=S3<=S1(1+delta)^{d/2}: extra kinetic share of the valley lift.

    S=-a u^2/mu^2 gives S'^2=(4a^2u^2/mu^4)u'^2; eta^2=h0^2-beta(u^2-1)
    gives eta'^2=beta^2 u^2 u'^2/eta^2, with u=(v_T/v) phi.
    """
    r = np.asarray(prof_r); u = vT_over_v*np.asarray(prof_phi)
    du = np.gradient(u, r)
    eta2 = h0*h0 - beta*(u*u - 1)
    if np.any(eta2 <= 0):
        raise ValueError('lifted Higgs branch leaves eta^2>0')
    w = r**(d - 1)*du*du
    extra = w*(4*a*a*u*u/mu**4 + beta*beta*u*u/eta2)
    return float(np.trapezoid(extra, r)/np.trapezoid(w, r))


def nucleation_threshold(d, scale, H, *, prefactor_band=0.):
    """Reduced-action value s* at which one bubble nucleates per Hubble volume and time.

    d=3: Gamma=T^4 (S3/2piT)^{3/2} exp(-S3/T) with S3/T=scale*s3, scale=v_T/(sqrt(lam) T).
    d=4: Gamma=v_T^4 (S4/2pi)^2 exp(-S4) with S4=scale*s4, scale=1/lam.
    The unknown determinant ratio is the declared factor exp(prefactor_band).
    H is in units of T (d=3) or v_T (d=4). Solves Gamma=H^4 by fixed point.
    """
    S = 100.
    for _ in range(100):
        p = 1.5 if d == 3 else 2.
        S_new = 4*log(1/H) + p*log(S/(2*pi)) + prefactor_band
        if abs(S_new - S) < 1e-12:
            break
        S = S_new
    return S/scale, S


def cubic_bounce(d, *, rtol=1e-12):
    """Universal O(d) bounce action of w^2/2-w^3/3 (false vacuum w=0), by shooting."""
    omega = 2*pi**(d/2)/gamma(d/2)
    rhs = lambda r, y: [y[1], y[0] - y[0]**2 - (d - 1)/r*y[1]]

    def shoot(w0, dense=False):
        r0 = 1e-6; a = (w0 - w0*w0)/d
        over = lambda r, y: y[0]; over.terminal = True; over.direction = -1
        under = lambda r, y: y[1]; under.terminal = True; under.direction = 1
        sol = solve_ivp(rhs, (r0, 200.), [w0 + a*r0*r0/2, a*r0], method='DOP853', rtol=rtol, atol=1e-15,
                        events=(over, under), dense_output=dense)
        return (1 if sol.t_events[0].size else -1), sol
    lo, hi = 1.5, 50.
    for _ in range(200):
        mid = (lo + hi)/2
        if shoot(mid)[0] > 0:
            hi = mid
        else:
            lo = mid
        if hi - lo < 1e-15*hi:
            break
    _, sol = shoot(lo, dense=True)
    rs = np.linspace(sol.t[0], sol.t[-1], 40001)
    y = sol.sol(rs)
    keep = y[0] > 1e-9
    T = omega*np.trapezoid(rs[keep]**(d - 1)*y[1][keep]**2/2, rs[keep])
    return {'s': 2*T/d, 'w0': lo}


def spinodal_constant_exact(d):
    """C_d=(2*3^{1/4})^{(6-d)/2} s_cubic(d)/3 from the cubic reduction at eps_sp-Delta.

    About the merging point x_s=-1/sqrt3, V'=Delta-sqrt3 y^2+y^3, so the false
    vacuum has m^2=2*3^{1/4} Delta^{1/2} and cubic coefficient alpha=sqrt3, and
    S=m^{6-d} s_cubic/alpha^2.
    """
    return (2*3**.25)**((6 - d)/2)*cubic_bounce(d)['s']/3


SPINODAL_CONSTANT = {}


def spinodal_constant(d, deltas=(1e-4, 1e-5, 1e-6)):
    """C_d in s_d=C_d (eps_sp-eps)^{(6-d)/4}, from bounces approaching the spinodal."""
    if d not in SPINODAL_CONSTANT:
        vals = [bounce(EPS_SPINODAL - x, d)['s']/x**((6 - d)/4) for x in deltas]
        SPINODAL_CONSTANT[d] = {'deltas': list(deltas), 'ratios': vals, 'C': vals[-1]}
    return SPINODAL_CONSTANT[d]


def critical_eps(target, d):
    """eps at which the reduced bounce action equals target (s_d decreases in eps).

    Below the action of the bounce at eps_sp-1e-6 the near-spinodal law is
    inverted instead, and the result is flagged as asymptotic.
    """
    lo, hi = 1e-2, EPS_SPINODAL - 1e-6
    g = lambda e: log(bounce(e, d)['s']) - log(target)
    if g(lo) < 0:
        raise ValueError('target below the eps=1e-2 action; use the thin-wall formula')
    if g(hi) > 0:
        C = spinodal_constant_exact(d)
        return EPS_SPINODAL - (target/C)**(4/(6 - d)), 'near_spinodal_asymptotic'
    return brentq(g, lo, hi, xtol=1e-13, rtol=1e-11), 'bounce'


def spinodal_action(eps, d):
    """Near-spinodal scaling check: s_d ~ C (eps_sp-eps)^{(6-d)/4}."""
    return (EPS_SPINODAL - eps)**((6 - d)/4)


def resummed_potential(phi, T, lam, v, c):
    """Leading Arnold-Espinosa resummed high-T potential along phi (single dof)."""
    m2 = c*T*T - lam*v*v + 3*lam*phi*phi
    return (c*T*T - lam*v*v)*phi*phi/2 + lam*phi**4/4 - T/(12*pi)*np.maximum(m2, 0)**1.5


def perturbative_transition(lam, v, c):
    """Degenerate-minimum temperature of the resummed potential and its loop parameter.

    Stationarity: phi[(cT^2-lam v^2)+lam phi^2-(3 lam T/4 pi) m(phi)]=0 with
    m^2=cT^2-lam v^2+3 lam phi^2. Returns T_c, phi_c/T_c, m/T at the broken
    minimum and g=lam T/(8 pi m). In the leading cubic approximation
    m/T=3 lam/(2 pi), so g=1/12 for every lam: the barrier is never
    parametrically perturbative.
    """
    T0 = v*sqrt(lam/c)

    def broken(T):
        A = c*T*T - lam*v*v
        g = lambda p: A + lam*p*p - 3*lam*T/(4*pi)*sqrt(max(A + 3*lam*p*p, 0.))
        hi = v + T
        grid = np.linspace(1e-9*T, hi, 4001)
        vals = np.array([g(p) for p in grid])
        idx = np.flatnonzero(np.sign(vals[:-1]) != np.sign(vals[1:]))
        if not idx.size:
            return None, np.inf
        j = idx[-1]
        p = brentq(g, grid[j], grid[j + 1], xtol=1e-14*T)
        return p, resummed_potential(p, T, lam, v, c) - resummed_potential(0., T, lam, v, c)

    lo, hi = T0, T0*1.01
    while broken(hi)[1] < 0:
        hi *= 1.01
    Tc = brentq(lambda T: broken(T)[1] if np.isfinite(broken(T)[1]) else 1., lo, hi, xtol=1e-12*T0)
    phic = broken(Tc)[0]
    m = sqrt(c*Tc*Tc - lam*v*v + 3*lam*phic*phic)
    return {'T0': T0, 'Tc': Tc, 'Tc_over_T0_minus_1': Tc/T0 - 1, 'phic_over_Tc': phic/Tc,
            'm_over_T': m/Tc, 'loop_parameter': lam*Tc/(8*pi*m), 'cubic_E': (3*lam)**1.5/(12*pi)}
