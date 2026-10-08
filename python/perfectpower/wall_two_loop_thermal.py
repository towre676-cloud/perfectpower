"""Computed two-loop thermal effective potential of the singlet sector of wall_nucleation.

Model (as in wall_nucleation_corrections): V_tree=lam/4(phi^2-v^2)^2+c T^2 phi^2/2-h phi,
field-dependent mass x=m^2(phi)=lam(3 phi^2-v^2), lam_s=6 lam (lam_s/4! phi^4 normalisation),
cubic vertex lam_s phi. Units GeV; kappa=1/16 pi^2.

Two-loop vacuum diagrams (Euclidean, MS-bar, d=4-2 eps)

    V_2 = (lam_s/8) I(x)^2 - (lam_s^2 phi^2/12) H(x),

with I=Sigma-int 1/(P^2+x) and H the equal-mass sunset. Both are split exactly into T=0 and
thermal parts:

    I = kappa A(x) + I_T(x),          A(x)=x(log(x/mu^2)-1)
    H = kappa^2 I_sun(x) + 3 I_T(x) B_on(x) + H_2(x),

where I_sun(x)=x(-3/2 L^2+6L-15/2+2 sqrt3 Cl_2(pi/3)) (L=log(x/mu^2), Ford-Jack-Jones), B_on is the
renormalised T=0 bubble at on-shell external momentum, B_on=kappa(log(mu^2/x)+2-pi/sqrt3), and
H_2 is the UV-finite part with two Bose factors. The decomposition follows from the Matsubara sum

    T^2 sum_{n1,n2} prod_i 1/(w_i^2+E_i^2) = [1/(E1+E2+E3) + sum_i n_i(1/(E1+E2+E3)+1/(E_j+E_k-E_i))
        + sum_{i<j} n_i n_j(1/(E1+E2+E3)-1/(E_i+E_j-E_k)+1/(E_j+E_k-E_i)+1/(E_k+E_i-E_j))]/(4E1E2E3)

(no n1 n2 n3 term). After the exact angular integration

    H_2 = 3/(32 pi^4) int_m^inf dE1 int_m^inf dE2 n(E1) n(E2) Lambda(E1,E2),
    Lambda = log[(2E1E2-x+2pq)(2E1E2+x-2pq)/((2E1E2-x-2pq)(2E1E2+x+2pq))],  p,q=sqrt(E^2-x).

The 1/eps poles proportional to I_T cancel between the figure-eight cross term, the sunset
subdivergence and the one-loop MS-bar coupling counterterm (coefficients -1, -2, +3 in units
lam_s^2 phi^2 I_T/(128 pi^2 eps)), so the finite pieces above are the complete MS-bar result.

Tachyonic masses (x<0): every function is the boundary value at x+i0 (Weinberg-Wu); the potential
is Re of the continued V. Thermal integrals use the contour E=sqrt(x+i0)+u^2, which for x<0 is the
horizontal line Im E=sqrt(-x), avoiding the Bose poles on the imaginary axis.

Scheme conversion to the on-shell (zero-momentum) scheme of wall_nucleation_corrections: with
OS parameters (lam, v) held fixed, the MS-bar parameters are lam+delta_lam, m0^2+delta_m0^2 with
delta_lam=9 kappa lam^2 L_v, delta_m0^2=3 kappa lam^2 v^2(2-L_v), L_v=log(mu^2/m_v^2), m_v^2=2 lam v^2,
i.e. the field-dependent mass shift delta x(phi)=delta_m0^2+3 delta_lam phi^2. The OS potential is

    V_OS = V_tree + V_CW^OS(x) + V_1T + (1/2)[kappa A(x)+I_T] delta x + V_2 + a2 phi^2 + a4 phi^4,

with (a2, a4) restoring V'(v)=0, V''(v)=m_v^2 at T=0 at two loops. It is mu-independent: the
non-polynomial log mu dependence cancels identically (checked numerically).

Daisy resummation (Parwani type, thermal parts, Boltzmann-exact thermal mass): with
Pi(phi)=(lam_s/2) Re I_T(x) and M^2=x+Pi, the thermal parts are evaluated at M^2 and
-(1/2) Pi I_T(M^2) is added. Expanding in Pi, the O(lam) figure-eight appears once; the first
change is the three-loop ring term +(1/4) Pi^2 dI_T/dm^2.

IR: near M^2=0 the thermal sunset has the zero-mode log -(kappa/2) T^2 log|M^2/T^2|. It is
regulated as log|y| -> (1/2) log(y^2+y_IR^2), y_IR=Pi/T^2 by default (the zero-mode thermal mass
scale); the regulator dependence is reported as an uncertainty.
"""
from math import pi, sqrt, log
import numpy as np
from scipy.interpolate import CubicSpline

KAPPA = 1/(16*pi*pi)
CL2_PI_3 = 1.0149416064096536250      # Clausen Cl_2(pi/3)
C_SUN = -7.5 + 2*sqrt(3)*CL2_PI_3      # I_sun(x)/x at L=0  (= -3.98413914196581...)
B_ON_CONST = 2 - pi/sqrt(3)
ZETA_RATIO = 1.9850530759826468        # zeta'(-1)/zeta(-1)
# Small-m limit of H_2/T^2 + log(m/T)/(32 pi^2), from the 3d sunset (Arnold-Espinosa) and the
# O(eps) part of the d-dimensional thermal tadpole: kappa*[log(4pi)/2-log3-zeta'(-1)/(2 zeta(-1))-1/2+pi/(4 sqrt3)].
H2_SMALL_M_CONST = KAPPA*(0.5*log(4*pi) - log(3) - 0.5*ZETA_RATIO - 0.5 + pi/(4*sqrt(3)))


# ---------------- thermal integrals (T=1 units), boundary values at y+i0 ----------------
def _nodes(panels, k, umin=1e-6, umax=8.):
    x, w = np.polynomial.legendre.leggauss(k)
    edges = np.r_[0., np.geomspace(umin, umax, panels)]
    U = np.concatenate([(b - a)/2*x + (a + b)/2 for a, b in zip(edges[:-1], edges[1:])])
    W = np.concatenate([(b - a)/2*w for a, b in zip(edges[:-1], edges[1:])])
    return U, W


NODES_1D = _nodes(44, 16)
NODES_2D = _nodes(30, 12)


def _contour(y, nodes):
    U, W = nodes
    e0 = sqrt(y) if y >= 0 else 1j*sqrt(-y)
    E = e0 + U*U
    dE = 2*U*W
    p = np.sqrt(E*E - y + 0j)
    with np.errstate(over='ignore'):
        n = 1/np.expm1(E)
    return E, p, n, dE


def J_B(y, nodes=NODES_1D):
    """J_B(y)=int_0^inf k^2 log(1-exp(-sqrt(k^2+y))) dk at y+i0 (complex for y<0)."""
    E, p, n, dE = _contour(y, nodes)
    return complex(np.sum(p*E*np.log(-np.expm1(-E))*dE))


def i_T(y, nodes=NODES_1D):
    """I_T/T^2=(1/2 pi^2) int k^2 n(E)/E dk at y+i0."""
    E, p, n, dE = _contour(y, nodes)
    return complex(np.sum(p*n*dE)/(2*pi*pi))


def h_2(y, nodes=NODES_2D):
    """H_2/T^2: the two-Bose-factor part of the thermal sunset at y+i0."""
    E, p, n, dE = _contour(y, nodes)
    A = 2*E[:, None]*E[None, :]
    P = 2*p[:, None]*p[None, :]
    lam = np.log(A - y + P) + np.log(A + y - P) - np.log(A - y - P) - np.log(A + y + P)
    g = n*dE
    return complex(3/(32*pi**4)*np.sum(g[:, None]*g[None, :]*lam))


def h_2_direct(y, nodes=NODES_2D, nc=48):
    """Same as h_2 with the angular integral done numerically (independent check)."""
    E, p, n, dE = _contour(y, nodes)
    c, wc = np.polynomial.legendre.leggauss(nc)
    E1, E2 = E[:, None, None], E[None, :, None]
    p1, p2 = p[:, None, None], p[None, :, None]
    K = -1/(y + 2*E1*E2 - 2*p1*p2*c) + 1/(2*E1*E2 + 2*p1*p2*c - y)
    g = n*dE
    f = np.sum(K*wc, axis=2)*(p[:, None]*p[None, :])*g[:, None]*g[None, :]
    return complex(3/(16*pi**4)*np.sum(f))


def J_B_highT(y, terms=30):
    """Convergent high-T series of J_B for |y|<4 pi^2 at y+i0."""
    from math import gamma as G, factorial
    from scipy.special import zeta
    yc = complex(y) + 0j
    if y < 0:
        sq = 1j*sqrt(-y); lg = log(-y) + 1j*pi
    else:
        sq = sqrt(y) if y > 0 else 0.; lg = log(y) if y > 0 else 0.
    ab = 16*pi*pi*np.exp(1.5 - 2*np.euler_gamma)
    out = -pi**4/45 + pi*pi*yc/12 - pi*yc*sq/6 - yc*yc/32*(lg - log(ab))
    for l in range(1, terms + 1):
        out -= 2*pi**3.5*(-1)**l*zeta(2*l + 1)/factorial(l + 2)*G(l + 0.5)*(yc/(4*pi*pi))**(l + 2)
    return out


def matsubara_sunset_check(E1, E2, E3, T=1., N=3000):
    """Brute-force T^2 sum_{n1,n2} prod 1/(w^2+E^2) against the decomposition used for H (fixed momenta)."""
    w = 2*pi*T*np.arange(-N, N + 1)
    d2 = 1/(w*w + E2*E2)
    brute = T*T*sum(np.sum(d2/((w1 + w)**2 + E3*E3))/(w1*w1 + E1*E1) for w1 in w)
    n = lambda E: 1/np.expm1(E/T)
    n1, n2, n3 = n(E1), n(E2), n(E3)
    s = E1 + E2 + E3
    lin = sum(ni*(1/s + 1/(Ej + Ek - Ei)) for ni, Ei, Ej, Ek in ((n1, E1, E2, E3), (n2, E2, E3, E1), (n3, E3, E1, E2)))
    quad = sum(ni*nj*(1/s - 1/(Ei + Ej - Ek) + 1/(Ej + Ek - Ei) + 1/(Ek + Ei - Ej))
               for ni, nj, Ei, Ej, Ek in ((n1, n2, E1, E2, E3), (n2, n3, E2, E3, E1), (n3, n1, E3, E1, E2)))
    return brute, (1/s + lin + quad)/(4*E1*E2*E3)


def parwani_linear_coefficient(s, ls, resummed=True):
    """Coefficient of M T^3 (odd zero-mode term) in V_1T(M)-Pi I_T(M)/2+(lam_s/8) I_T(M)^2 (T=1).

    Extracted as Im F(-s^2)/s at small s (odd powers of M become imaginary at M^2=-s^2+i0).
    With the high-T Pi=lam_s/24 the coefficient vanishes (no double counting); without
    resummation it is -lam_s/(192 pi) (the first daisy, carried by the figure-eight).
    """
    y = -s*s
    Pi = ls/24 if resummed else 0.
    F = J_B(y)/(2*pi*pi) - 0.5*Pi*i_T(y) + ls/8*i_T(y)**2
    return F.imag/s


# ---------------- tables ----------------
def _sub_log(y):
    return np.log(np.abs(y) + 1e-300) + 1j*pi*(y < 0)


class ThermalTables:
    """Splines of J_B, i_T and h_T(y)=3 i_T kappa(-log y+2-pi/sqrt3)+h_2 on [ymin,ymax].

    Known logarithms are subtracted (y^2 log y/32, y log y/16 pi^2, -(kappa/2) log y) and the
    remainders are splined in t=sqrt|y| separately for y<0 and y>0 (real and imaginary parts).
    Beyond ymax the functions are Boltzmann suppressed below 1e-30 relative and set to their
    asymptotic zero.
    """

    def __init__(self, ymin, ymax, *, n_geo=50, dt=0.06):
        self.range = (ymin, ymax)
        self.sides = {}
        for sgn, ext in ((1., ymax), (-1., -ymin)):
            if ext <= 0:
                continue
            tmax = sqrt(ext)*1.0001 + 0.05
            t = np.unique(np.r_[0., np.geomspace(1e-4, min(1., tmax), n_geo), np.arange(1., tmax + dt, dt)])
            ys = sgn*t*t
            vals = []
            for y in ys:
                if y == 0.:
                    vals.append(None); continue
                jb, it, h2 = J_B(y), i_T(y), h_2(y)
                L = complex(_sub_log(np.array([y]))[0])
                hT = 3*it*KAPPA*(-L + B_ON_CONST) + h2
                vals.append((jb + y*y/32*L, it + y/(16*pi*pi)*L, hT + KAPPA/2*L))
            # t=0 limits by quadratic extrapolation in t from the next three nodes
            arr = np.array([v for v in vals if v is not None])
            tt = t[1:4]
            v0 = [np.polyval(np.polyfit(tt, arr[:3, k], 2), 0.) for k in range(3)]
            arr = np.vstack([v0, arr])
            self.sides[sgn] = [(CubicSpline(t, arr[:, k].real), CubicSpline(t, arr[:, k].imag)) for k in range(3)]
            self.sides[sgn].append(t[-1])

    def _eval(self, y, k):
        y = np.asarray(y, float)
        out = np.zeros(y.shape, complex)
        for sgn, spl in self.sides.items():
            mask = (np.sign(y) == sgn) | ((y == 0) & (sgn > 0))
            if not mask.any():
                continue
            t = np.sqrt(np.abs(y[mask]))
            inside = t <= spl[3]
            tt = np.minimum(t, spl[3])
            out[mask] = np.where(inside, spl[k][0](tt) + 1j*spl[k][1](tt), 0.)
        return out

    def JB(self, y):
        y = np.asarray(y, float); L = _sub_log(y)
        r = self._eval(y, 0) - y*y/32*L
        return np.where(y <= self.range[1]*1.0001 + 0.05, r, 0.)

    def iT(self, y):
        y = np.asarray(y, float); L = _sub_log(y)
        r = self._eval(y, 1) - y/(16*pi*pi)*L
        return np.where(y <= self.range[1]*1.0001 + 0.05, r, 0.)

    def hT(self, y, y_IR=0.):
        """h_T with the zero-mode log regulated: -(kappa/2)[log(y+i0)] -> -(kappa/4) log(y^2+y_IR^2) (+ i pi part kept)."""
        y = np.asarray(y, float); L = _sub_log(y)
        if y_IR > 0:
            L = L - np.log(np.abs(y) + 1e-300) + 0.5*np.log(y*y + y_IR*y_IR)
        r = self._eval(y, 2) - KAPPA/2*L
        return np.where(y <= self.range[1]*1.0001 + 0.05, r, 0.)


# ---------------- zero-temperature pieces (x+i0) ----------------
def _L(x, mu2):
    x = np.asarray(x, float)
    return np.log((np.where(x == 0, 1e-300, x) + 0j)/mu2)


def A0(x, mu2):
    return x*(_L(x, mu2) - 1)


def V1_msbar(x, mu2):
    return KAPPA/4*x*x*(_L(x, mu2) - 1.5)


def V_CW_OS(x, mv2):
    """Re of the one-loop OS Coleman-Weinberg potential of wall_nucleation_corrections."""
    x = np.asarray(x, float)
    return (KAPPA/4*(x*x*(np.log(np.abs(x)/mv2 + 1e-300) - 1.5) + 2*x*mv2))


def I_sun(x, mu2):
    L = _L(x, mu2)
    return x*(-1.5*L*L + 6*L + C_SUN)


def B_on(x, mu2):
    return KAPPA*(-_L(x, mu2) + B_ON_CONST)


# ---------------- the potential ----------------
class TwoLoopPotential:
    """Two-loop thermal effective potential of the singlet (physical units).

    thermal: include thermal loops (False = Boltzmann limit, thermal pieces dropped).
    resum: Parwani-type resummation of thermal parts with Pi=(lam_s/2) Re I_T.
    yIR_factor: regulator y_IR=yIR_factor*Pi(0)/T^2 for the zero-mode sunset log (0: none).
    """

    def __init__(self, lam, v, T, *, tables=None, thermal=True, resum=True, yIR_factor=1., mu=None):
        self.lam, self.v, self.T = lam, v, T
        self.ls = 6*lam
        self.mv2 = 2*lam*v*v
        self.mu2 = (mu if mu is not None else sqrt(self.mv2))**2
        self.thermal = thermal and T > 0
        self.resum = resum
        self.tables = tables
        if self.thermal and tables is None:
            raise ValueError('thermal loops need ThermalTables')
        Lv = log(self.mu2/self.mv2)
        self.dlam = 9*KAPPA*lam*lam*Lv
        self.dm02 = 3*KAPPA*lam*lam*v*v*(2 - Lv)
        self.yIR = 0.
        if self.thermal:
            Pi0 = 0.5*self.ls*T*T*float(tables.iT(np.array([0.]))[0].real)
            self.yIR = yIR_factor*Pi0/T**2
        self.a2, self.a4 = self._os_polynomial()

    # mass functions
    def x(self, phi):
        return self.lam*(3*np.asarray(phi, float)**2 - self.v**2)

    def dx(self, phi):
        return self.dm02 + 3*self.dlam*np.asarray(phi, float)**2

    def _pieces(self, phi, x):
        """Loop pieces at mass argument x (array): resummed one-loop thermal, I, figure-eight, sunset."""
        T = self.T
        if self.thermal:
            y = x/T**2
            Pi = 0.5*self.ls*T*T*self.tables.iT(y).real if self.resum else np.zeros_like(x)
            yM = (x + Pi)/T**2
            IT = T*T*self.tables.iT(yM)
            V1T = T**4/(2*pi*pi)*self.tables.JB(yM).real - 0.5*Pi*IT.real
            V1T_bare = T**4/(2*pi*pi)*self.tables.JB(y).real
            HT = T*T*(self.tables.hT(yM, self.yIR) + 3*self.tables.iT(yM)*KAPPA*log(self.mu2/T**2))
        else:
            IT = HT = np.zeros_like(x) + 0j
            V1T = V1T_bare = np.zeros_like(x)
        I = KAPPA*A0(x, self.mu2) + IT
        fig8 = (self.ls/8*I*I).real
        sun = (-(self.ls**2)*phi*phi/12*(KAPPA**2*I_sun(x, self.mu2) + HT)).real
        return {'V1T': V1T, 'V1T_bare': V1T_bare, 'I': I, 'fig8': fig8, 'sun': sun}

    def two_loop_parts(self, phi):
        """Real pieces (GeV^4) added to tree + V_CW^OS(x) + V_1T(x) (unresummed one loop)."""
        phi = np.asarray(phi, float)
        x = self.x(phi)
        P = self._pieces(phi, x)
        return {'resummation': P['V1T'] - P['V1T_bare'],
                'scheme_conversion': 0.5*(P['I']*self.dx(phi)).real,
                'figure_eight': P['fig8'], 'sunset': P['sun'],
                'os_polynomial': self.a2*phi*phi + self.a4*phi**4}

    def delta(self, phi):
        return sum(self.two_loop_parts(phi).values())

    def os_loops(self, phi):
        """All loop terms of the two-loop OS potential (V_CW^OS + resummed V_1T + two-loop), GeV^4."""
        phi = np.asarray(phi, float)
        x = self.x(phi)
        return V_CW_OS(x, self.mv2) + self._pieces(phi, x)['V1T_bare'] + self.delta(phi)

    def msbar_loops(self, phi):
        """Loop terms of the MS-bar two-loop potential at scale mu with one-loop matched couplings.

        tree_MS - tree_OS = P1 (polynomial); V_1 and V_2 are evaluated at the MS-bar mass x+delta x.
        No two-loop matching: V_MS - V_OS is two-loop polynomial plus three-loop order.
        """
        phi = np.asarray(phi, float)
        x = self.x(phi); xm = x + self.dx(phi)
        P1 = KAPPA/4*(x*x*log(self.mu2/self.mv2) + 2*x*self.mv2)
        P = self._pieces(phi, xm)
        return P1 + V1_msbar(xm, self.mu2).real + P['V1T'] + P['fig8'] + P['sun']

    def one_loop_msbar_minus_os(self, phi):
        """One-loop MS-bar with tree-level (OS-valued) parameters minus one-loop OS."""
        x = self.x(np.asarray(phi, float))
        return V1_msbar(x, self.mu2).real - V_CW_OS(x, self.mv2)

    def _os_polynomial(self):
        """(a2,a4): T=0 two-loop V'(v)=0 and V''(v)=0 restored (zero-momentum OS conditions)."""
        import mpmath as mp
        with mp.workdps(40):
            return self._os_polynomial_mp(mp)

    def _os_polynomial_mp(self, mp):
        lam, v, ls, mu2 = mp.mpf(self.lam), mp.mpf(self.v), mp.mpf(self.ls), mp.mpf(self.mu2)
        K = 1/(16*mp.pi**2)
        dlam, dm02 = mp.mpf(self.dlam), mp.mpf(self.dm02)
        Cs = -mp.mpf(15)/2 + 2*mp.sqrt(3)*mp.clsin(2, mp.pi/3)

        def F(p):
            x = lam*(3*p*p - v*v)
            L = mp.log(x/mu2)
            A = x*(L - 1)
            return K*A*(dm02 + 3*dlam*p*p)/2 + ls/8*(K*A)**2 - ls**2*p*p/12*K**2*x*(-1.5*L*L + 6*L + Cs)
        D1, D2 = mp.diff(F, v, 1), mp.diff(F, v, 2)
        a4 = (D1/v - D2)/(8*v*v)
        a2 = -D1/(2*v) - 2*a4*v*v
        return float(a2), float(a4)


# ---------------- reduced potential for the bounce code of wall_nucleation_corrections ----------------
class ReducedTwoLoop:
    """U(x)=base.U(x)+d(x), d=delta_phys(x v_T)/(lam v_T^4) as a piecewise cubic with explicit breakpoints.

    base is a wall_nucleation_corrections.Corrected (tree+one-loop); delta_phys a vectorised function
    of phi in GeV returning GeV^4. Breakpoints (where m^2 or M^2 vanish) are knots across which only
    continuity is imposed; nodes cluster geometrically towards them.
    """

    def __init__(self, base, delta_phys, vT, lam, breakpoints=(), xlim=(-1.75, 1.75), n_uniform=500, n_geo=45,
                 smooth=()):
        from scipy.interpolate import PPoly
        self.base, self.vT, self.lam = base, vT, lam
        self.parts = base.parts
        self.r, self.tau = base.r, base.tau
        self.smooth = tuple(smooth)
        bks = sorted(b for b in set(breakpoints) if xlim[0] < b < xlim[1])
        edges = [xlim[0]] + bks + [xlim[1]]
        xs_all, cs = [], []
        for a, b in zip(edges[:-1], edges[1:]):
            w = b - a
            g = np.geomspace(1e-11*max(1., abs(a)), w/3, n_geo)
            nodes = np.unique(np.r_[np.linspace(a, b, max(8, int(n_uniform*w/(xlim[1] - xlim[0])))),
                                    a + g if a > xlim[0] else [], b - g if b < xlim[1] else []])
            for c, s in self.smooth:
                if a < c - 7*s and c + 7*s < b:
                    nodes = np.unique(np.r_[nodes, np.linspace(c - 7*s, c + 7*s, 141)])
            vals = np.asarray(delta_phys(nodes*vT), float)/(lam*vT**4)
            for c, s in self.smooth:
                m = np.abs(nodes - c) <= 7*s
                if m.any():
                    z = np.linspace(c - 12*s, c + 12*s, 24*40 + 1) + 1e-3*s/40*np.pi   # off-centre: no node at c
                    dz = np.asarray(delta_phys(z*vT), float)/(lam*vT**4)
                    G = np.exp(-0.5*((nodes[m][:, None] - z[None, :])/s)**2)
                    vals[m] = (G @ dz)/G.sum(axis=1)
            sp = CubicSpline(nodes, vals)
            xs_all.append(sp.x[:-1])
            cs.append(sp.c)
        knots = np.r_[np.concatenate(xs_all), xlim[1]]
        self.pp = PPoly(np.concatenate(cs, axis=1), knots)
        self.dpp = self.pp.derivative()
        self._k = knots
        self._dc = self.dpp.c

    def delta(self, x):
        return self.pp(np.asarray(x, float))

    def ddelta(self, x):
        return self.dpp(np.asarray(x, float))

    def U(self, x, eps):
        return self.base.U(x, eps) + self.delta(x)

    def dU(self, x, eps):
        return self.base.dU(x, eps) + self.ddelta(x)

    def scalar_dU(self, eps):
        import bisect
        f0 = self.base.scalar_dU(eps)
        kl = self._k.tolist()
        c0, c1, c2 = (self._dc[j].tolist() for j in range(3))
        n = len(kl) - 2

        def f(x):
            i = min(max(bisect.bisect_right(kl, x) - 1, 0), n)
            t = x - kl[i]
            return f0(x) + (c0[i]*t + c1[i])*t + c2[i]
        return f


def spinodal_eps(pot, lo=-0.85, hi=-0.3):
    """eps_sp=max of U0'(x) on the left branch (the false vacuum disappears when eps exceeds it)."""
    from scipy.optimize import minimize_scalar
    xs = np.linspace(lo, hi, 200001)
    g = pot.dU(xs, 0.)
    j = int(np.argmax(g))
    res = minimize_scalar(lambda x: -float(pot.dU(np.array([x]), 0.)[0]),
                          bounds=(xs[max(j - 1, 0)], xs[min(j + 1, len(xs) - 1)]), method='bounded',
                          options={'xatol': 1e-13})
    return max(-res.fun, float(g[j])), float(res.x)


def singular_points(tp, vT):
    """Reduced x where m^2(phi)=0 (T=0 logs: knots) and, for thermal loops, where the resummed
    M^2=-(2 pi k T)^2, k=0,1,.. (zero-mode/massless-mode non-analyticities: Gaussian-smoothed in M^2
    over the width y_IR T^2, the IR regulator). Returns (knots, [(centre, sigma_x)])."""
    from scipy.optimize import brentq
    v, lam = tp.v, tp.lam
    knots = [v/sqrt(3)/vT, -v/sqrt(3)/vT]
    smooth = []
    if tp.thermal and tp.yIR > 0:
        T = tp.T

        def M2(phi):
            x = tp.x(np.array([phi]))
            Pi = 0.5*tp.ls*T*T*tp.tables.iT(x/T**2).real if tp.resum else 0.
            return float((x + Pi)[0])
        targets = [0.] + [-(2*pi*k*T)**2 for k in range(1, 6) if (2*pi*k*T)**2 < lam*v*v]
        for tgt in targets:
            g = lambda p: M2(p) - tgt
            if g(0.) < 0 < g(1.6*vT):
                rt = brentq(g, 0., 1.6*vT, xtol=1e-12*vT)
                slope = (M2(rt*(1 + 1e-7)) - M2(rt*(1 - 1e-7)))/(2e-7*rt)*vT     # dM^2/dx
                sig = tp.yIR*T*T/abs(slope)
                smooth += [(rt/vT, sig), (-rt/vT, sig)]
    return knots, smooth
