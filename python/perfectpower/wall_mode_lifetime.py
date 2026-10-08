"""Real-time decay of the localized radial wall mode: classical and pair channels.

Reduced theory. The heavy singlet (M=300000 GeV) is eliminated by its
static constraint S=-g phi^2/M^2, which removes it exactly from the static
wall and from the zero-frequency Hessian; the dynamical remainder is
O(omega^2/M^2)~1e-7 (Hessian shift ~1e-5 relative to k^2). The remaining
fields are the source u=phi/v and the real four-component Higgs doublet in
units of its vacuum value, Phi/(v_H)=(h,pi_1,pi_2,pi_3). With x=k v z,
t->k v t, k=sqrt(lam/2), the planar 3+1 action is

    S=(1/k^2) int d^4X [ (du)^2/2 + h0^2 |dPhi|^2/2 - V/(v^4 k^2) ],
    V/v^4 = lam (u^2-1)^2/4 + lam_H X^2/4,  X=h0^2(|Phi|^2-1)+b(u^2-1),

with h0=v_H/v and b=kappa/lam_H. Equations of motion are

    u_tt = u_xx - 2u(u^2-1) - c_k u X,      c_k = kappa/k^2,
    Phi_tt = Phi_xx - (lam_H/k^2) X Phi.

hbar=1 in these units for the canonical fields u/k and h0 Phi/k: the source
sector carries hbar_eff=k^2, the Higgs sector k^2/h0^2. Classical dynamics
never contains hbar; it enters only through seeded vacuum fluctuations.

Lattice: half line x_j=j dx, j=0..N-1, fourth-order Laplacian with parity
ghosts at x=0 and fixed vacuum ghosts beyond the last site. Velocity Verlet.
All results are floating-point lattice numerics, not enclosures.
"""
from math import sqrt, pi, sinh
import numpy as np
from scipy.sparse import diags, csr_matrix, bmat
from scipy.sparse.linalg import spsolve

HBAR_GEV_S = 6.582119569e-25

# Declared inputs of the main-branch candidate (wall_embedded_states.json,
# fixed_Higgs_parameters_source_quartic_candidates[0]); not re-derived here.
CANDIDATE = {'v_GeV': 30000., 'v_H_GeV': 246., 'lambda_H': .13, 'kappa': 1e-7,
             'source_lambda': 1.7618816494787725e-05, 'heavy_mass_GeV': 300000.,
             'source_current_GeV': 3000., 'main_mode_mass_GeV': 154.22502415713,
             'main_Gamma_GG_GeV': 3.83233455848e-8, 'main_Gamma_GG_even_GeV': 3.10403359118e-8,
             'main_Gamma_GG_odd_GeV': 7.28300967296e-9}


def couplings(v_GeV=CANDIDATE['v_GeV'], v_H_GeV=CANDIDATE['v_H_GeV'], lambda_H=CANDIDATE['lambda_H'],
              kappa=CANDIDATE['kappa'], source_lambda=CANDIDATE['source_lambda']):
    """Dimensionless reduced couplings. Only h0, cH, ck and b enter the dynamics."""
    if min(v_GeV, v_H_GeV, lambda_H, source_lambda) <= 0 or kappa < 0:
        raise ValueError('positive scales and quartics, nonnegative portal required')
    k = sqrt(source_lambda/2); h0 = v_H_GeV/v_GeV
    return {'k': k, 'kv_GeV': k*v_GeV, 'h0': h0, 'h02': h0*h0, 'b': kappa/lambda_H,
            'cH': lambda_H/k**2, 'ck': kappa/k**2, 'Higgs_mass2': 2*lambda_H*h0*h0/k**2,
            'hbar_source': k*k, 'hbar_Higgs': k*k/(h0*h0)}


def laplacian_matrix(N, dx, parity):
    """Fourth-order half-line Laplacian (sparse) acting on sites j=0..N-1.

    parity +1: even (f_{-j}=f_j); -1: odd (f_0=0 kept by the stencil).
    Zero ghosts beyond the end: deviations vanish at x=N dx (Dirichlet).
    """
    if parity not in (1, -1) or N < 6 or dx <= 0:raise ValueError('parity +-1, N>=6, dx>0 required')
    c = np.array([-1., 16., -30., 16., -1.])/(12*dx*dx)
    A = diags([np.full(N-abs(o), c[o+2]) for o in range(-2, 3)], list(range(-2, 3)), format='lil')
    # Ghost f_{-1}=s f_1, f_{-2}=s f_2.
    A[0, 1] += parity*c[1]; A[0, 2] += parity*c[0]; A[1, 1] += parity*c[0]
    if parity == -1:
        A[0, :] = 0.
    return A.tocsr()


def _lap(f, dx, parity, right):
    """Apply the same stencil to f[...,N] with a constant right ghost value."""
    g = np.empty(f.shape[:-1]+(f.shape[-1]+4,))
    g[..., 2:-2] = f
    g[..., 1] = parity*f[..., 1]; g[..., 0] = parity*f[..., 2]
    g[..., -2:] = right
    out = (-g[..., :-4]+16*g[..., 1:-3]-30*g[..., 2:-2]+16*g[..., 3:-1]-g[..., 4:])/(12*dx*dx)
    if parity == -1:out[..., 0] = 0.
    return out


def static_wall(c, N, dx, *, tol=1e-13, maxiter=60):
    """Newton solution of the lattice static wall (u odd, h even, pi=0)."""
    x = dx*np.arange(N)
    u = np.tanh(x); h = np.ones(N)
    lu, lh = laplacian_matrix(N, dx, -1), laplacian_matrix(N, dx, 1)
    # Ghost contributions of the fixed vacuum values u=h=1 beyond the end.
    gu = np.zeros(N); gu[-2] = -1/(12*dx*dx); gu[-1] = 15/(12*dx*dx)
    gh = gu.copy()
    for it in range(maxiter):
        X = c['h02']*(h*h-1)+c['b']*(u*u-1)
        Ru = lu@u+gu-2*u*(u*u-1)-c['ck']*u*X
        Rh = lh@h+gh-c['cH']*X*h
        Ru[0] = u[0]
        r = max(abs(Ru).max(), abs(Rh).max())
        if r < tol:break
        Juu = lu-diags(2*(3*u*u-1)+c['ck']*X+2*c['ck']*c['b']*u*u)
        Juh = diags(-2*c['ck']*c['h02']*u*h)
        Jhu = diags(-2*c['cH']*c['b']*u*h)
        Jhh = lh-diags(c['cH']*(X+2*c['h02']*h*h))
        J = bmat([[Juu, Juh], [Jhu, Jhh]]).tolil()
        J[0, :] = 0.; J[0, 0] = 1.
        d = spsolve(J.tocsc(), -np.r_[Ru, Rh])
        u = u+d[:N]; h = h+d[N:]
    else:
        raise ArithmeticError('static lattice wall did not converge')
    X = c['h02']*(h*h-1)+c['b']*(u*u-1)
    return {'x': x, 'u': u, 'h': h, 'X': X, 'Goldstone_potential': c['cH']*X, 'residual': float(r), 'iterations': it,
            'Ward_zero_mode_residual': float(abs(lh@h+gh-c['cH']*X*h).max())}


def localized_mode(c, wall, dx):
    """Lattice shape mode: odd source eigenvector plus driven even-Higgs response.

    The Higgs component solves (K_h-omega^2)psi_h=-2 ck u h psi_u with an
    outgoing Robin row at the last site; |B| is the radiating amplitude from
    residual node detuning in the reduced lattice theory. The backreaction
    of psi_h on the source equation (coefficient ck h0^2~1e-6) is iterated.
    """
    u, h, X = wall['u'], wall['h'], wall['X']; N = len(u)
    lu, lh = laplacian_matrix(N, dx, -1), laplacian_matrix(N, dx, 1)
    w = np.ones(N); w[0] = .5
    Kuu = -lu+diags(2*(3*u*u-1)+c['ck']*X+2*c['ck']*c['b']*u*u)
    Khh = -lh+diags(c['cH']*(X+2*c['h02']*h*h))
    # Odd sector: drop site 0; symmetric after weights (w=1 there).
    from scipy.sparse.linalg import eigsh
    A = Kuu[1:, 1:]
    vals, vecs = eigsh(A.tocsc(), k=1, sigma=3., which='LM')
    om2 = float(vals[0]); pu = np.zeros(N); pu[1:] = vecs[:, 0]
    pu /= sqrt(2*dx*np.sum(w*pu*pu))
    if pu[np.argmax(abs(pu))] < 0:pu = -pu
    q = sqrt(om2-c['Higgs_mass2'])
    M = (Khh-om2*diags(np.ones(N))).astype(complex).tolil()
    # Outgoing row at the last site: f_N = f_{N-1} e^{iq dx}.
    rhs = (-2*c['ck']*u*h*pu).astype(complex); rhs[-1] = 0.
    M[N-1, :] = 0.; M[N-1, N-1] = 1.; M[N-1, N-2] = -np.exp(1j*q*dx)
    ph = spsolve(M.tocsc(), rhs)
    # First-order Higgs backreaction on the source eigenvalue (ck h0^2 ~ 1e-6).
    om2 = om2+float(2*dx*np.sum(w*pu*(2*c['ck']*c['h02']*u*h*ph.real)))
    B = abs(ph[-1])
    norm = 2*dx*np.sum(w*(pu*pu+c['h02']*abs(ph)**2))
    # energy loss of the linear Higgs leak: two sides, flux omega q|B|^2/2 (A=1)
    leak = 2*(.5*sqrt(om2)*q*B*B*c['h02'])/(.5*om2*norm)
    return {'omega2': om2, 'omega': sqrt(om2), 'psi_u': pu, 'psi_h': ph.real, 'psi_h_imag_max': float(abs(ph.imag).max()),
            'radiating_Higgs_amplitude': float(B), 'Higgs_momentum': q, 'canonical_norm': float(norm),
            'linear_leak_energy_rate': float(leak)}


def evolve_background(c, wall, mode, A, *, dt, steps, record_every=1, sponge=None, store_X=True):
    """Nonlinear classical (u, h) evolution with pi=0; returns X(t) and a(t).

    A is the source amplitude of the full-line normalised mode (x units).
    sponge=(start, strength) adds damping gamma(x) on x>start (absorbing).
    """
    x = wall['x']; dx = x[1]-x[0]; N = len(x)
    u = wall['u']+A*mode['psi_u']; h = wall['h']+A*mode['psi_h']
    vu = np.zeros(N); vh = np.zeros(N)
    gamma = np.zeros(N)
    if sponge is not None:
        s0, s1 = sponge; m = x > s0
        gamma[m] = s1*((x[m]-s0)/(x[-1]-s0))**2
    w = np.ones(N); w[0] = .5
    def acc(u, h):
        X = c['h02']*(h*h-1)+c['b']*(u*u-1)
        au = _lap(u, dx, -1, 1.)-2*u*(u*u-1)-c['ck']*u*X
        au[0] = 0.  # odd source: u(0)=0 is a constraint, not a dynamical site
        return au, _lap(h, dx, 1, 1.)-c['cH']*X*h, X
    au, ah, X = acc(u, h)
    Xs, amp, ts = [X.copy()], [], []
    proj = lambda u:float(2*dx*np.sum(w*(u-wall['u'])*mode['psi_u']))
    amp.append(proj(u)); ts.append(0.)
    for n in range(1, steps+1):
        vu += .5*dt*au; vh += .5*dt*ah
        if sponge is not None:
            vu *= 1-dt*gamma/2; vh *= 1-dt*gamma/2
        u = u+dt*vu; h = h+dt*vh
        au, ah, X = acc(u, h)
        vu += .5*dt*au; vh += .5*dt*ah
        if sponge is not None:
            vu *= 1-dt*gamma/2; vh *= 1-dt*gamma/2
        if n % record_every == 0:
            amp.append(proj(u)); ts.append(n*dt)
            if store_X:Xs.append(X.copy())
    return {'t': np.array(ts), 'X': np.array(Xs), 'a': np.array(amp), 'u': u, 'h': h}


def goldstone_pair_power(c, wall, X_history, *, dt, p, parity, window, ramp_steps=0, keep_energy=False):
    """Exact Gaussian (quantum = infinite classical-statistical ensemble) evolution.

    One real Goldstone component of transverse momentum p in the given parity
    sector, initially in the static-wall vacuum, driven by the recorded
    background X(t). Mode functions start on the eigenvectors of the
    velocity-Verlet map, so the undriven energy is constant to rounding.
    The coupling to the oscillation is switched on as
    X_s+r(t)(X(t)-X_s), r=sin^2(pi n/(2 ramp_steps)), which removes the
    sudden-quench pair burst and the slow infrared relaxation it causes.
    window=(i0,i1,nT): power from one-period energy means at i0 and i1.
    Energies are full-line, in units of k v, with hbar=1 for this field.
    """
    x = wall['x']; dx = x[1]-x[0]; N = len(x)
    L = -laplacian_matrix(N, dx, parity)
    w = np.ones(N); w[0] = .5
    sl = slice(1, None) if parity == -1 else slice(None)
    s = np.sqrt(w[sl]); L = L[sl][:, sl]
    Ls = (diags(s)@L@diags(1/s)).tocsr()
    Ls = (.5*(Ls+Ls.T)).toarray()
    Xs = wall['X']
    r = np.ones(len(X_history))
    if ramp_steps > 0:
        n = np.arange(min(ramp_steps, len(r)))
        r[:len(n)] = np.sin(.5*pi*n/ramp_steps)**2
    U0 = p*p+c['cH']*Xs[sl]
    K0 = Ls+np.diag(U0)
    om2, Q = np.linalg.eigh(K0)
    if om2.min() <= 0:raise ArithmeticError('static Goldstone operator not positive')
    om = np.sqrt(om2); hh = om*dt
    if hh.max() >= 2:raise ValueError('Verlet stability requires omega_max dt<2')
    omp = om*np.sqrt(1-hh*hh/4)
    a = 1/np.sqrt(2*omp)
    # real and imaginary parts stacked as 2n columns
    G = np.hstack((Q*a, np.zeros_like(Q)))
    V = np.hstack((np.zeros_like(Q), -Q*(omp*a)))
    Lsp = csr_matrix(Ls)
    def force(G, n):
        return -(Lsp@G)-(p*p+c['cH']*(Xs+r[n]*(X_history[n]-Xs))[sl])[:, None]*G
    def energy(G, V):
        return float(.5*np.sum(V*V)+.5*np.sum(G*(K0@G)))
    F = force(G, 0)
    E0 = energy(G, V)
    i0, i1, nT = window
    if not 0 < i0 < i1-nT or i1 >= len(X_history):raise ValueError('window (i0,i1,period_steps) inside history required')
    early, late, trace = [], [], []
    for n in range(1, i1+1):
        V += .5*dt*F
        G += dt*V
        F = force(G, n)
        V += .5*dt*F
        if keep_energy:trace.append(energy(G, V)-E0)
        if i0 <= n < i0+nT:early.append(energy(G, V)-E0 if not keep_energy else trace[-1])
        if i1-nT < n <= i1:late.append(energy(G, V)-E0 if not keep_energy else trace[-1])
    span = (i1-i0-(nT-1))*dt
    out = {'power': float((np.mean(late)-np.mean(early))/span), 'E0': E0,
           'period_mean_energy_gain': [float(np.mean(early)), float(np.mean(late))], 'span': span}
    if keep_energy:out['energy'] = np.array(trace)
    return out


def kink_second_harmonic_rate():
    """Energy decay rate per A^2 in x,t units (A full-line normalised in x).

    From wall_shape_radiation.kink_closed_form: Gamma/A_rho^2=(9 sqrt6/8) pi^2 lam/sinh^2(sqrt2 pi)
    in 1/v units with A_rho^2=A_x^2/k; with lam=2k^2 this is (9 sqrt6/4) pi^2/sinh^2(sqrt2 pi).
    """
    return 9*sqrt(6)/4*pi*pi/sinh(sqrt(2)*pi)**2


def vacuum_sample_matrices(c, wall, *, dt, p=0., parity=-1):
    """Static Goldstone normal modes on the half line in the Verlet-eigen form.

    Returns site mode shapes f_n (full-line normalised, values at sites),
    discrete frequencies omega'_n and the slice of dynamical sites.
    """
    x = wall['x']; dx = x[1]-x[0]; N = len(x)
    w = np.ones(N); w[0] = .5
    sl = slice(1, None) if parity == -1 else slice(None)
    L = -laplacian_matrix(N, dx, parity)[sl][:, sl]
    s = np.sqrt(w[sl])
    Ls = (diags(s)@L@diags(1/s)).toarray(); Ls = .5*(Ls+Ls.T)
    K0 = Ls+np.diag(p*p+c['cH']*wall['X'][sl])
    om2, Q = np.linalg.eigh(K0)
    om = np.sqrt(om2); omp = om*np.sqrt(1-(om*dt)**2/4)
    f = Q/(s[:, None]*sqrt(2*dx))
    return {'modes': f, 'omega_prime': omp, 'K0_symmetric': K0, 'weights_sqrt': s, 'slice': sl, 'dx': dx}


def classical_statistical_run(c, wall, mode, A, *, dt, steps, samples, noise_fraction, seed, parity=-1, record=()):
    """Fully nonlinear classical-statistical evolution of (u, h, pi) on the half line.

    One Goldstone component pi in the given parity sector (pi^2 is even, so
    the truncation is consistent with u odd, h even) carries Gaussian
    vacuum noise of noise_fraction times the half-quantum variance of the
    canonical field h0 pi/k (hbar=1 in kv units). All nonlinear terms,
    including pi backreaction on u and h, are kept. Returns the canonical
    Goldstone quadratic energy (static operator) per sample at `record`
    step indices. Same seed and A=0 give common-random-number controls.
    """
    if samples < 1 or noise_fraction < 0:raise ValueError('at least one sample and nonnegative noise required')
    vm = vacuum_sample_matrices(c, wall, dt=dt, parity=parity)
    f, omp, sl, dx = vm['modes'], vm['omega_prime'], vm['slice'], vm['dx']
    rng = np.random.default_rng(seed)
    xi = rng.standard_normal((samples, len(omp))); eta = rng.standard_normal((samples, len(omp)))
    scale = sqrt(noise_fraction)*sqrt(c['hbar_Higgs'])  # pi = (k/h0) Pi
    N = len(wall['x'])
    pi_ = np.zeros((samples, N)); vp = np.zeros((samples, N))
    pi_[:, sl] = scale*(xi/np.sqrt(2*omp))@f.T
    vp[:, sl] = scale*(eta*np.sqrt(omp/2))@f.T
    u = np.tile(wall['u']+A*mode['psi_u'], (samples, 1)); h = np.tile(wall['h']+A*mode['psi_h'], (samples, 1))
    vu = np.zeros_like(u); vh = np.zeros_like(h)
    K0 = vm['K0_symmetric']; s = vm['weights_sqrt']
    def acc(u, h, q):
        X = c['h02']*(h*h+q*q-1)+c['b']*(u*u-1)
        au = _lap(u, dx, -1, 1.)-2*u*(u*u-1)-c['ck']*u*X; au[:, 0] = 0.
        aq = _lap(q, dx, parity, 0.)-c['cH']*X*q
        if parity == -1:aq[:, 0] = 0.
        return au, _lap(h, dx, 1, 1.)-c['cH']*X*h, aq
    def energy(q, vq):
        g = q[:, sl]*s*sqrt(2*dx); gv = vq[:, sl]*s*sqrt(2*dx)
        return (.5*np.sum(gv*gv, 1)+.5*np.sum(g*(g@K0), 1))/c['hbar_Higgs']
    au, ah, aq = acc(u, h, pi_)
    out = {}
    if 0 in record:out[0] = energy(pi_, vp)
    for n in range(1, steps+1):
        vu += .5*dt*au; vh += .5*dt*ah; vp += .5*dt*aq
        u += dt*vu; h += dt*vh; pi_ += dt*vp
        au, ah, aq = acc(u, h, pi_)
        vu += .5*dt*au; vh += .5*dt*ah; vp += .5*dt*aq
        if n in record:out[n] = energy(pi_, vp)
    return out


def second_harmonic_envelope(c, wall, mode, A, *, dt, steps, sponge, period_steps):
    """Noise-free nonlinear run with an absorbing layer: per-period envelope.

    Returns rows (t, half peak-to-peak of a(t)=<u-u_wall,psi_u>).
    """
    r = evolve_background(c, wall, mode, A, dt=dt, steps=steps, sponge=sponge, record_every=1, store_X=False)
    a = r['a']; t = r['t']
    env = []
    for j in range(0, len(a)-period_steps, period_steps):
        seg = a[j:j+period_steps]
        env.append((t[j]+.5*period_steps*dt, .5*(seg.max()-seg.min())))
    return np.array(env)


def pair_width_scan(c, *, dx, L, dt, A, nodes, t_ramp, t0, t1, wall=None, mode=None):
    """Planar 3+1 pair width from 1+1 real-time runs at transverse momenta p.

    Each real Goldstone component decomposes exactly (at quadratic order in
    the Goldstones) into independent 1+1 fields of mass p. Emission per
    unit wall area is n_G int d^2p/(2pi)^2 P_1D(p) = (n_G/2pi) int p P_1D dp
    over 0<p<omega/2 (Gauss-Legendre), summed over both parity sectors.
    The energy decay rate is Gamma=P_area/E_area, E_area=omega^2 A^2 N/(2k^2).
    """
    N = int(round(L/dx))
    wall = wall or static_wall(c, N, dx)
    mode = mode or localized_mode(c, wall, dx)
    om = mode['omega']; nT = int(round(2*pi/om/dt))
    i0, i1, ir = int(round(t0/dt)), int(round(t1/dt)), int(round(t_ramp/dt))
    bg = evolve_background(c, wall, mode, A, dt=dt, steps=i1)
    g, w = np.polynomial.legendre.leggauss(nodes)
    ps = (g+1)*om/4; w = w*om/4
    rows = []
    for p in ps:
        row = {'p': float(p)}
        for name, par in (('even', 1), ('odd', -1)):
            r = goldstone_pair_power(c, wall, bg['X'], dt=dt, p=p, parity=par, window=(i0, i1, nT), ramp_steps=ir)
            row[name+'_power_over_A2'] = r['power']/A**2
        rows.append(row)
    scale = 3/(2*pi)*2*c['k']**2/(om**2*mode['canonical_norm'])*c['kv_GeV']
    even = scale*sum(wi*r['p']*r['even_power_over_A2'] for wi, r in zip(w, rows))
    odd = scale*sum(wi*r['p']*r['odd_power_over_A2'] for wi, r in zip(w, rows))
    return {'Gamma_GG_GeV': even+odd, 'even_GeV': even, 'odd_GeV': odd, 'nodes': rows,
            'mode_omega': om, 'mode_mass_GeV': om*c['kv_GeV'], 'A': A, 'dx': dx, 'L': L, 'dt': dt,
            'window': [t0, t1], 'ramp': t_ramp, 'period_steps': nT,
            'max_drive_frequency_pairs_p_limit': om/2}
