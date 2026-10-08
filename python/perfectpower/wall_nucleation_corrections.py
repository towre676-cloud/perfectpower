"""Radiative corrections to the biased-vacuum bounces of wall_nucleation.

Reduced variables follow wall_nucleation: x=phi/v_T, potential in units of
lam v_T^4, U_tree=(x^2-1)^2/4-eps x, with v_T^2=v^2-cT^2/lam the declared
mean-field vev. Write r=v/v_T and tau=T/v_T. Added pieces (all Z2-even,
so the bias term is untouched):

1. Zero-temperature one-loop Coleman-Weinberg, on-shell (zero-momentum)
   scheme. With M=m^2(phi)/(lam v_T^2)=3x^2-r^2 and M_v=2r^2,
     V_CW=(lam/64 pi^2)[M^2(log|M/M_v|-3/2)+2 M M_v],
   which keeps V'(v)=0 and V''(v)=2 lam v^2 at T=0 (tree vev and curvature
   mass kept). Re-part prescription (log|M|) where m^2<0. The heavy mediator
   (M_S^2=M^2+4g^2phi^2/M^2) is added in the same scheme; Higgs loops enter
   through kappa=1e-7 and are bounded, not added.
   An MS-bar variant at mu^2=m_v^2 (tree parameters held, so the vev and mass
   move at O(lam/16 pi^2)) is a scheme comparison.
2. One-loop thermal function beyond the high-T truncation:
     V_T=(T^4/2 pi^2) Re J_B(m^2/T^2) - (lam/4) T^2 phi^2/2,
   i.e. the phi self-loop part of the declared cT^2 mass is replaced by the
   full Bose function. Used where |m^2|/T^2<4 pi^2 on the bounce domain
   (Re J_B is then free of the tachyonic log|sin| singularities); otherwise
   the declared high-T term and its complete removal (Boltzmann limit)
   bracket it. Where Re J_B is used, the daisy-shifted J_B(m^2/T^2+lam/4)
   (phi self-energy cT^2 with c=lam/4) is the alternative.
3. Two-loop thermal estimates for the scalar sector (lambda_std=6 lam):
   figure-eight (lambda_std/8) I_T^2 and sunset magnitude
   (lambda_std^2 phi^2/12)(T^2/16 pi^2)(|log(3m/T)|+1) rho, rho=I_T(m)/I_T(0);
   zero-temperature two loops bracketed by (beta_lam/lam)=18 lam/16 pi^2
   times the one-loop CW action shift. These enter the bracket only.
4. Thermal vector free energy per area dF (another wall's TE determinant)
   as a positive tension shift: dS3/T=dF*4 pi R^2/T, R the bubble radius.

Floating-point bounces (as in wall_nucleation); no fluctuation determinant.
"""
from math import pi, sqrt, gamma, log
import numpy as np
from scipy.integrate import solve_ivp, quad
from scipy.interpolate import CubicSpline
from scipy.optimize import brentq
from scipy.special import iv, ive

from . import wall_nucleation as wn

LOOP = 1/(64*pi*pi)


# ---------- thermal functions ----------
def re_JB(y):
    """Re J_B(y)=Re int_0^inf x^2 log(1-exp(-sqrt(x^2+y))) dx, smooth substitutions."""
    if y >= 0:
        return quad(lambda s: sqrt(max(s*s - y, 0.))*s*np.log(-np.expm1(-s)), sqrt(y), np.inf, limit=200)[0]
    ay = sqrt(-y)
    hi = quad(lambda s: sqrt(s*s - y)*s*np.log(-np.expm1(-s)), 0, np.inf, limit=200)[0]
    pts = [2*pi*k for k in range(1, int(ay/(2*pi)) + 1)]
    lo = quad(lambda a: sqrt(max(-y - a*a, 0.))*a*np.log(abs(2*np.sin(a/2))), 0, ay,
              points=pts or None, limit=400)[0]
    return lo + hi


def tadpole_i(y):
    """i(y)=int x^2/(e (e^e-1)) dx, e=sqrt(x^2+y), y>=0; I_T=(T^2/2 pi^2) i, i(0)=pi^2/6."""
    if y < 0:
        raise ValueError('y>=0')
    with np.errstate(over='ignore'):   # 1/expm1(s)=0 for s beyond the double range
        return quad(lambda s: sqrt(max(s*s - y, 0.))/np.expm1(s) if s > 0 else 0., sqrt(y), np.inf, limit=200)[0]


class ThermalSpline:
    """Cubic splines of Re J_B and i(|y|) on [ymin, ymax]."""

    def __init__(self, ymin, ymax, n=601, *, with_J=True):
        self.J = None
        if with_J:
            if ymin < -4*pi*pi:
                raise ValueError('Re J_B beyond the first tachyonic singularity')
            ys = np.unique(np.r_[np.linspace(ymin, ymax, n), np.linspace(max(ymin, -2.), min(ymax, 2.), 201)])
            self.J = CubicSpline(ys, [re_JB(y) for y in ys])
        top = max(abs(ymin), abs(ymax))
        ya = np.unique(np.r_[0., np.geomspace(1e-6, min(top, 3e3), n)])
        self.i = CubicSpline(ya, [tadpole_i(y) for y in ya])
        self.range = (ymin, ymax)

    def i_of(self, y):
        """i(y) for y>=0; exponentially small (set to zero) beyond the spline range y>3000."""
        y = np.asarray(y, float)
        return np.where(y <= self.i.x[-1], self.i(np.minimum(y, self.i.x[-1])), 0.)


# ---------- corrected reduced potential ----------
class Corrected:
    """U(x)=U_tree+sum of selected corrections; units lam v_T^4.

    parts: subset of {'cw','cw_msbar','heavy','thermal1','thermal1_removal'}.
    """

    def __init__(self, lam, r=1., tau=0., parts=('cw',), heavy=None, spline=None, M_IR=0., y_shift=0.):
        self.lam, self.r, self.tau, self.parts, self.M_IR = lam, r, tau, tuple(parts), M_IR
        self.y_shift = y_shift      # daisy variant: Re J_B(m^2/T^2+y_shift)
        self.heavy = heavy          # (A0, A2): M_S^2/(lam v_T^2)=A0+A2 x^2
        self.spline = spline
        if 'thermal1' in self.parts and spline is None:
            raise ValueError('thermal1 needs a ThermalSpline')

    def _M(self, x):
        return 3*x*x - self.r**2

    def delta(self, x):
        x = np.asarray(x, float); lam, r, tau = self.lam, self.r, self.tau
        out = np.zeros_like(x)
        M = self._M(x); Mv = 2*r*r
        if 'cw' in self.parts:
            L = np.log((np.abs(M) + self.M_IR)/(Mv + self.M_IR) + 1e-300)
            out += lam*LOOP*(M*M*(L - 1.5) + 2*M*Mv)
        if 'cw_msbar' in self.parts:
            out += lam*LOOP*M*M*(np.log(np.abs(M)/Mv + 1e-300) - 1.5)
        if 'heavy' in self.parts:
            A0, A2 = self.heavy
            Ms = A0 + A2*x*x; Msv = A0 + A2*r*r
            out += lam*LOOP*(Ms*Ms*(np.log(Ms/Msv) - 1.5) + 2*Ms*Msv)
        if 'thermal1' in self.parts:
            y = lam*M/tau**2 + self.y_shift
            out += tau**4/(2*pi*pi*lam)*self.spline.J(y) - tau*tau*x*x/8
        if 'thermal1_removal' in self.parts:
            out += -tau*tau*x*x/8
        return out

    def ddelta(self, x):
        x = np.asarray(x, float); lam, r, tau = self.lam, self.r, self.tau
        out = np.zeros_like(x)
        M = self._M(x); Mv = 2*r*r
        L = np.log(np.abs(M)/Mv + 1e-300)
        if 'cw' in self.parts:
            Lr = np.log((np.abs(M) + self.M_IR)/(Mv + self.M_IR) + 1e-300)
            out += lam*LOOP*(2*M*Lr + M*np.abs(M)/(np.abs(M) + self.M_IR + 1e-300) - 3*M + 2*Mv)*6*x
        if 'cw_msbar' in self.parts:
            out += lam*LOOP*(2*M*L - 2*M)*6*x
        if 'heavy' in self.parts:
            A0, A2 = self.heavy
            Ms = A0 + A2*x*x; Msv = A0 + A2*r*r
            out += lam*LOOP*(2*Ms*np.log(Ms/Msv) - 2*Ms + 2*Msv)*2*A2*x
        if 'thermal1' in self.parts:
            y = lam*M/tau**2 + self.y_shift
            out += tau*tau/(2*pi*pi)*self.spline.J(y, 1)*6*x - tau*tau*x/4
        if 'thermal1_removal' in self.parts:
            out += -tau*tau*x/4
        return out

    def scalar_dU(self, eps):
        """Fast scalar U' for the ODE right-hand side (same formulas as ddelta)."""
        from math import log as _log
        lam, r, tau, parts, MIR = self.lam, self.r, self.tau, self.parts, self.M_IR
        Mv = 2*r*r
        A0, A2 = self.heavy if self.heavy else (1., 0.)
        Msv = A0 + A2*r*r
        J1 = self.spline.J.derivative() if 'thermal1' in parts else None
        ys = self.y_shift

        def f(x):
            out = x*x*x - x - eps
            M = 3*x*x - r*r
            aM = abs(M) + 1e-300
            if 'cw' in parts:
                Lr = _log((aM + MIR)/(Mv + MIR))
                out += lam*LOOP*(2*M*Lr + M*aM/(aM + MIR) - 3*M + 2*Mv)*6*x
            if 'cw_msbar' in parts:
                out += lam*LOOP*(2*M*_log(aM/Mv) - 2*M)*6*x
            if 'heavy' in parts:
                Ms = A0 + A2*x*x
                out += lam*LOOP*(2*Ms*_log(Ms/Msv) - 2*Ms + 2*Msv)*2*A2*x
            if 'thermal1' in parts:
                out += tau*tau/(2*pi*pi)*float(J1(lam*M/tau**2 + ys))*6*x - tau*tau*x/4
            if 'thermal1_removal' in parts:
                out += -tau*tau*x/4
            return out
        return f

    def U(self, x, eps):
        return wn.V(np.asarray(x, float), eps) + self.delta(x)

    def dU(self, x, eps):
        x = np.asarray(x, float)
        return x**3 - x - eps + self.ddelta(x)


def two_loop_thermal(x, lam, tau, spline):
    """(figure-eight, |sunset| estimate) in units lam v_T^4; m^2 taken as |m0^2|."""
    x = np.asarray(x, float)
    M = np.abs(3*x*x - 1.)
    y = lam*M/tau**2
    i = spline.i_of(y)
    fig8 = 3/16*tau**4*i*i/pi**4
    rho = 6*i/(pi*pi)
    logt = np.abs(np.log(3*np.sqrt(np.maximum(lam*M, 1e-300))/tau))
    sunset = 3*lam*x*x*tau*tau*(logt + 1)*rho/(16*pi*pi)
    return fig8, sunset


# ---------- generic O(d) bounce ----------
def stationary_points(pot, eps):
    """False vacuum, barrier, true vacuum: the three sign changes of pot.dU on [-1.6,1.6]."""
    g = lambda x: float(pot.dU(x, eps))
    xs = np.linspace(-1.6, 1.6, 64001); vals = pot.dU(xs, eps)
    idx = np.flatnonzero(np.sign(vals[:-1]) != np.sign(vals[1:]))
    if idx.size != 3:
        raise ValueError('corrected potential has no barrier at this bias')
    return tuple(brentq(g, xs[j], xs[j + 1], xtol=1e-15) for j in idx)


def bounce(pot, eps, d, *, rtol=1e-11, iterations=200):
    """O(d) bounce of pot.U(.,eps) by the log-space overshoot/undershoot of wall_nucleation."""
    f, b, t = stationary_points(pot, eps)
    Uf = float(pot.U(f, eps))
    e = brentq(lambda x: float(pot.U(x, eps)) - Uf, b, t, xtol=1e-15)
    h = 1e-6
    kap = sqrt((float(pot.dU(t + h, eps)) - float(pot.dU(t - h, eps)))/(2*h))
    if d == 3:
        g = lambda z: np.sinh(z)/z if z > 1e-8 else 1 + z*z/6
        gp = lambda z: (np.cosh(z)/z - np.sinh(z)/z**2) if z > 1e-4 else z/3
        logg = lambda z: z + np.log1p(-np.exp(-2*z)) - np.log(2*z) if z > 1e-4 else np.log1p(z*z/6)
    elif d == 4:
        g = lambda z: 2*iv(1, z)/z if z > 1e-8 else 1 + z*z/8
        gp = lambda z: 2*iv(2, z)/z if z > 1e-4 else z/4
        logg = lambda z: np.log(2*ive(1, z)) + z - np.log(z) if z > 1e-4 else np.log1p(z*z/8)
    else:
        raise ValueError('d=3 or 4')
    dU = pot.scalar_dU(eps)

    def shoot(xx, dense=False):
        delta = (t - e)*np.exp(-xx)
        z = 1e-6*kap
        if delta*g(z) < 1e-4:
            z = brentq(lambda z: logg(z) + np.log(delta) - np.log(1e-4), 1e-6*kap, 800.)
        r0 = z/kap
        y0 = [t - delta*g(z), -delta*kap*gp(z)]
        over = lambda r, y: y[0] - f
        over.terminal = True; over.direction = -1
        under = lambda r, y: y[1]
        under.terminal = True; under.direction = 1
        rhs = lambda r, y: [y[1], dU(y[0]) - (d - 1)/r*y[1]]
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
    rs = np.linspace(sol.t[0], sol.t[-1], 40001)
    y = sol.sol(rs)
    keep = (y[0] - f) > 1e-7*(t - f)
    rs, y = rs[keep], y[:, keep]
    w = rs**(d - 1)
    omega = 2*pi**(d/2)/gamma(d/2)
    T = omega*np.trapezoid(w*y[1]**2/2, rs)
    r0 = sol.t[0]
    U = omega*(np.trapezoid(w*(pot.U(y[0], eps) - Uf), rs) + r0**d/d*(float(pot.U(t, eps)) - Uf))
    return {'eps': eps, 'd': d, 's': (2/d)*T, 'kinetic': T, 'potential': U,
            'virial_defect': ((d - 2)*T + d*U)/T, 'false': f, 'true': t, 'phi0': float(y[0][0]),
            'radius_half_point': float(rs[np.argmin(abs(y[0] - (f + t)/2))]),
            'radius_core': float(rs[np.argmax(y[0] <= (f + y[0][0])/2)]), 'r': rs, 'phi': y[0]}


def first_order_shift(b, dV, d):
    """Omega_d int r^{d-1}[dV(phi_b)-dV(phi_f)] dr and the same with |.|: first-order action shifts."""
    omega = 2*pi**(d/2)/gamma(d/2)
    w = b['r']**(d - 1)
    diff = dV(b['phi']) - dV(np.array([b['false']]))[0]
    return float(omega*np.trapezoid(w*diff, b['r'])), float(omega*np.trapezoid(w*abs(diff), b['r']))


def critical_eps(pot, target, d, *, lo=.2, hi=None):
    """eps with bounce action s_d=target for the corrected potential."""
    if hi is None:
        hi = corrected_spinodal(pot)['eps_sp'] - 2e-4
    g = lambda e: log(bounce(pot, e, d)['s']) - log(target)
    glo, ghi = g(lo), g(hi)
    if glo < 0 or ghi > 0:
        raise ValueError('target outside [lo,hi] bracket')
    return brentq(g, lo, hi, xtol=1e-11, rtol=1e-10)


def corrected_spinodal(pot):
    """Spinodal of the corrected potential: U0''(x_s)=0 near -1/sqrt3, eps_sp=U0'(x_s).

    Near it U'=Delta-a z^2+..., m^2=2 sqrt(a Delta), S_d=m^{6-d} s_cubic/a^2, so
    C_d=(2 sqrt a)^{(6-d)/2} s_cubic(d)/a^2 (reduces to wall_nucleation for a=sqrt3).
    """
    d1 = lambda x: float(pot.dU(x, 0.))
    h = 1e-7
    d2 = lambda x: (d1(x + h) - d1(x - h))/(2*h)
    cands = []
    xs = np.linspace(-0.75, -0.4, 3500*2 + 1) + 1.234567e-7   # grid avoids the m^2=0 point exactly
    vals = np.array([d2(x) for x in xs])
    for j in np.flatnonzero((vals[:-1] > 0) & (vals[1:] <= 0)):
        xr = brentq(d2, xs[j], xs[j + 1], xtol=1e-13)
        cands.append((d1(xr), xr))
    if not cands:
        raise ArithmeticError('no inflection point')
    eps_sp, xs_ = max(cands)
    a = abs((d2(xs_ + 1e-5) - d2(xs_ - 1e-5))/2e-5)/2
    C = {d: (2*sqrt(a))**((6 - d)/2)*wn.cubic_bounce(d)['s']/a**2 for d in (3, 4)}
    return {'eps_sp': eps_sp, 'x_s': xs_, 'cubic_a': a, 'C': C}
