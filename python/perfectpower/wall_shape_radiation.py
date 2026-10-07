"""Second-harmonic (nonlinear) radiation of the wall shape mode.

Fluctuations obey eta_tt+H eta+(1/2)V3[eta,eta]+O(eta^3)=0 in units of v,
with V3 the third derivative of the three-field potential along the wall.
For eta_1=A psi cos(omega t), psi the full-line normalised shape state,
(1/2)V3[eta_1,eta_1]=(A^2/4)J(1+cos 2 omega t) with J=V3[psi,psi]. The
second harmonic X e^{-2i omega t} obeys (H-4 omega^2)X=-(A^2/4)J with
outgoing/decaying conditions in every channel. Each open channel j carries
time-averaged power Omega q_j |B_j|^2/2 per side, so the full-line loss is
P=P1 A^4 and the energy E=omega^2 A^2/2 decays at the rate
Gamma_NL(A)=2 P1 A^2/omega^2. The static A^2 part does not radiate.
Floating-point finite elements; leading order in A, not an enclosure.
"""
from math import sqrt
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import spsolve
from .wall_jost_scattering import _constants, hessian, vacuum_channels, channel_momenta


def _profile(wall, rho):
    lam, a, m, h0, kap, lH = _constants(wall)
    rho = np.asarray(rho, float)
    z = np.empty((3, rho.size))
    inside = rho <= wall['L']
    z[:, inside] = wall['solution'].sol(rho[inside])[:3]
    z[:, ~inside] = np.array([[1.], [-a/m**2], [h0]])
    return z


def cubic_vertex(wall, rho):
    """V_ijk in (phi/v, S/v, eta/v); every component not listed is zero.

    V_uuu=6 lam u+12 a^2 u/mu^2+6 kappa beta u, V_uuy=2a, V_uuh=2 kappa h,
    V_uhh=2 kappa u, V_hhh=6 lam_H h, with beta=kappa/lam_H.
    """
    lam, a, m, h0, kap, lH = _constants(wall)
    u, y, h = _profile(wall, rho)
    b = kap/lH
    T = np.zeros((u.size, 3, 3, 3))
    T[:, 0, 0, 0] = 6*lam*u + 12*a*a*u/m**2 + 6*kap*b*u
    for i, j, k in ((0, 0, 1), (0, 1, 0), (1, 0, 0)):
        T[:, i, j, k] = 2*a
    for i, j, k in ((0, 0, 2), (0, 2, 0), (2, 0, 0)):
        T[:, i, j, k] = 2*kap*h
    for i, j, k in ((0, 2, 2), (2, 0, 2), (2, 2, 0)):
        T[:, i, j, k] = 2*kap*u
    T[:, 2, 2, 2] = 6*lH*h
    return T


def state_values(state, rho):
    """Exact quadratic-element values of the (phi,S) shape state (half-line normalised)."""
    edges, nodes = state['edges'], state['nodes']
    rho = np.asarray(rho, float)
    j = np.clip(np.searchsorted(edges, rho, side='right') - 1, 0, len(edges) - 2)
    s = 2*(rho - edges[j])/(edges[j + 1] - edges[j]) - 1
    N = np.array([s*(s - 1)/2, 1 - s*s, s*(s + 1)/2])
    vals = sum(N[r][:, None]*nodes[2*j + r] for r in range(3))
    vals[rho > edges[-1]] = 0.
    return vals


def second_harmonic(wall, state, *, R=150., spacing=.02, order=5):
    """Outgoing second-harmonic field per unit A^2 and the radiated power P1 (A=1).

    Opposite reflection sector (phi Dirichlet, S and eta Neumann at 0): J is
    odd in phi and even in S and eta. The Robin condition eta'=iQ eta at R
    with Q=V diag(q) V^T is exact for the constant vacuum, with q=i sqrt(mu-E)
    in closed channels.
    """
    omega2 = state['E']
    Omega2 = 4*omega2
    edges = np.linspace(0., R, int(round(R/spacing)) + 1)
    x = np.sort(np.r_[edges, (edges[:-1] + edges[1:])/2])
    n = len(x)
    g, w = np.polynomial.legendre.leggauss(order)
    I3 = np.eye(3)
    rr, cc, vv, fi, fv = [], [], [], [], []
    d = edges[1] - edges[0]
    K0 = np.kron(np.array([[7, -8, 1], [-8, 16, -8], [1, -8, 7]])/(3*d), I3)
    M0 = np.kron(d*np.array([[4, 2, -1], [2, 16, 2], [-1, 2, 4]])/30, I3)
    pts = (edges[:-1, None] + (g[None, :] + 1)*d/2).ravel()
    Hq = hessian(wall, pts, decouple=False).reshape(len(edges) - 1, order, 3, 3)
    psi = np.zeros((pts.size, 3))
    psi[:, :2] = state_values(state, pts)/sqrt(2)  # full-line normalisation
    J = np.einsum('nijk,nj,nk->ni', cubic_vertex(wall, pts), psi, psi).reshape(len(edges) - 1, order, 3)
    Ns = np.array([g*(g - 1)/2, 1 - g*g, g*(g + 1)/2])  # (3, order)
    for e in range(len(edges) - 1):
        K = K0 - Omega2*M0
        for s in range(order):
            K = K + w[s]*d/2*np.kron(np.outer(Ns[:, s], Ns[:, s]), Hq[e, s])
        ids = np.arange(6*e, 6*e + 9)
        rr.extend(np.repeat(ids, 9)); cc.extend(np.tile(ids, 9)); vv.extend(K.ravel())
        f = -0.25*d/2*np.einsum('rs,s,si->ri', Ns, w, J[e])  # (nodes, fields), node-major
        fi.extend(ids); fv.extend(f.ravel())
    Nd = 3*n
    A = coo_matrix((np.asarray(vv, complex), (rr, cc)), shape=(Nd, Nd)).tolil()
    F = np.zeros(Nd, complex)
    np.add.at(F, fi, fv)
    mu, V = vacuum_channels(wall)
    q, open_ = channel_momenta(np.array([Omega2]), mu)
    q, open_ = q[0], open_[0]
    Q = V@np.diag(q)@V.T
    last = np.arange(Nd - 3, Nd)
    for i in range(3):
        for j in range(3):
            A[last[i], last[j]] -= 1j*Q[i, j]
    keep = np.array([j for j in range(Nd) if j != 0])  # phi Dirichlet at rho=0
    A = A.tocsr()[keep][:, keep]
    X = np.zeros(Nd, complex)
    X[keep] = spsolve(A.tocsc(), F[keep])
    X = X.reshape(n, 3)
    c = V.T@X[-1]
    B = np.where(open_, c*np.exp(-1j*np.where(open_, q, 0)*R), 0)
    Omega = sqrt(Omega2)
    power = np.where(open_, Omega*q.real*abs(B)**2, 0.)
    P1 = float(power.sum())
    return {'Omega2': Omega2, 'thresholds': mu.tolist(), 'open_channels': np.flatnonzero(open_).tolist(),
            'q': q.tolist(), 'outgoing_amplitudes': B.tolist(), 'channel_power': power.tolist(), 'P1': P1,
            'Gamma_NL_over_A2': 2*P1/omega2, 'x': x, 'X': X}


def crossover(P1, omega2, Gamma_E_linear):
    """Amplitude where nonlinear and linear energy-loss rates are equal.

    Linear: dE/dt=-(Gamma_E/(2 omega)) E. Nonlinear: dE/dt=-(2 P1 A^2/omega^2) E.
    Starting far above A_c, d(1/A^2)/dt=2P1/omega^2 holds until A reaches A_c,
    after a time t_c=omega^2/(2 P1 A_c^2), equal to one linear e-folding time.
    """
    gamma_lin = Gamma_E_linear/(2*sqrt(omega2))
    A2 = gamma_lin*omega2/(2*P1)
    return {'A_c': sqrt(A2), 'linear_rate': gamma_lin, 't_c': 1/gamma_lin}


def kink_time_domain(lam, A, *, half_width=500., dx=.05, t_end=800., sponge=120., samples=4000):
    """Independent nonlinear check: pure phi^4 kink u_tt=u_xx-lam u(u^2-1).

    Starts from tanh(kx)+A psi(x) at rest, psi the full-line normalised shape
    mode, with leapfrog steps and a damping sponge. Returns the projection
    a(t)=<u-tanh, psi> sampled in time.
    """
    k = sqrt(lam/2)
    x = np.arange(-half_width, half_width + dx/2, dx)
    psi = sqrt(1.5*k)/np.cosh(k*x)*np.tanh(k*x)
    uk = np.tanh(k*x)
    u = uk + A*psi
    dt = .4*dx
    gamma = np.where(abs(x) > half_width - sponge, .5*((abs(x) - half_width + sponge)/sponge)**2, 0.)
    def acc(u):
        a = np.empty_like(u)
        a[1:-1] = (u[2:] - 2*u[1:-1] + u[:-2])/dx**2
        a[0] = a[-1] = 0.
        return a - lam*u*(u*u - 1)
    v = .5*dt*acc(u)
    steps = int(round(t_end/dt))
    every = max(1, steps//samples)
    ts, a = [], []
    for s in range(steps):
        u = u + dt*v
        v = (v*(1 - .5*dt*gamma) + dt*acc(u))/(1 + .5*dt*gamma)
        if s % every == 0:
            ts.append((s + 1)*dt); a.append(float(np.sum((u - uk)*psi)*dx))
    return np.array(ts), np.array(a)


def kink_closed_form(lam):
    """Exact leading second-harmonic loss of the pure phi^4 kink shape mode.

    Projecting -(1/4)J=-(9 lam k/4) tanh^3 sech^2 (x=k rho) on the exact
    Poschl-Teller continuum (3 tanh^2-1-q^2-3iq tanh) e^{iqx} at q=2 sqrt2
    gives I=int(3T^2-1-q^2+3iqT)T^3 sech^2 e^{-iqx}dx=-12 pi i/sinh(sqrt2 pi),
    using int sech^2 e^{i nu x}=pi nu/sinh(pi nu/2) and its recursions. Then
    P1=(27 sqrt6/32) pi^2 lam^2/sinh^2(sqrt2 pi) and
    Gamma_NL/A^2=2P1/omega^2=(9 sqrt6/8) pi^2 lam/sinh^2(sqrt2 pi).
    """
    s2 = np.sinh(sqrt(2)*np.pi)**2
    return {'I_abs': 12*np.pi/np.sinh(sqrt(2)*np.pi),
            'P1': 27*sqrt(6)/32*np.pi**2*lam**2/s2,
            'Gamma_NL_over_A2': 9*sqrt(6)/8*np.pi**2*lam/s2,
            'radiated_momentum_over_k': 2*sqrt(2)}


def envelope(t, a, period):
    """Half peak-to-peak amplitude of a(t) over successive periods."""
    out, t0 = [], t[0]
    while t0 + period < t[-1]:
        m = (t >= t0) & (t < t0 + period)
        out.append((t0 + period/2, (a[m].max() - a[m].min())/2))
        t0 += period
    return np.array(out)
