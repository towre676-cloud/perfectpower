"""Press-Ryden-Spergel lattice simulation of the Z2 wall network.

The walls of the supplied model are phi^4 kinks to 1e-6 (mediator and Higgs
corrections; see the tension sandwich), so the network is simulated for
V=(lam/4)(phi^2-1)^2-eps(tau) phi in comoving units with a=tau (radiation).
PRS evolves
  phi''+alpha (dln a/dln tau) phi'/tau-lap phi=-a^beta dV/dphi
with alpha=3, beta=0, which keeps the comoving wall width fixed while
conserving wall momentum (Press, Ryden and Spergel 1989).

With beta=0 the ratio of bias pressure to curvature force is
eps(tau) R_c/sigma_hat. Physically it is Delta V a R_c/sigma, so the bias
must grow as eps(tau)=eps1*tau to represent a constant physical Delta V.
Then sigma/Delta V=sigma_hat/(2 eps1) and t=tau^2/2.

The area parameter is A=rho_wall t/sigma=(comoving area density) tau/2.
Area is estimated by counting sign-changing links, times (2/3)dx^2 for
isotropic orientations (Scherrer and Vilenkin). Floating-point lattice
evolution in a periodic box. Finite resolution and box size are reported as
controls, not removed.
"""
from math import sqrt, pi
import numpy as np


def laplacian(f, dx):
    out = f*f.dtype.type(-2*f.ndim)
    for ax in range(f.ndim):
        out += np.roll(f, 1, ax)
        out += np.roll(f, -1, ax)
    if dx != 1:
        out /= f.dtype.type(dx*dx)
    return out


def wall_area(f, dx):
    """Comoving wall area by link counting, (2/3) dx^2 per sign-changing link (3D)."""
    s = f > 0
    links = sum(np.count_nonzero(s != np.roll(s, 1, ax)) for ax in range(f.ndim))
    factor = 2/3 if f.ndim == 3 else pi/4
    return factor*links*dx**(f.ndim - 1)


def initial_field(N, ndim, seed, *, kmax_frac=.25, amplitude=.1):
    """Gaussian random field with a sharp spectral cutoff, zero mean, given rms."""
    rng = np.random.default_rng(seed)
    f = rng.standard_normal((N,)*ndim)
    F = np.fft.fftn(f)
    k = np.sqrt(sum(np.meshgrid(*[np.fft.fftfreq(N)**2]*ndim, indexing='ij')))
    F[k > kmax_frac*.5] = 0
    F.flat[0] = 0
    f = np.fft.ifftn(F).real
    return (amplitude*f/f.std()).astype(np.float32)


def evolve(N, *, ndim=3, lam=.5, dx=1., dt=.2, tau_i=1., tau_f=None, seed=0,
           eps1=0., alpha=None, record_every=5, field=None):
    """PRS evolution from a random initial field; returns time series of A and fractions."""
    alpha = ndim if alpha is None else alpha
    tau_f = N*dx/2 if tau_f is None else tau_f
    phi = initial_field(N, ndim, seed) if field is None else field.copy()
    vel = np.zeros_like(phi)
    tau = tau_i
    vol = (N*dx)**ndim
    rows = []
    step = 0
    while tau < tau_f - 1e-12:
        d = .5*alpha*dt/tau
        force = laplacian(phi, dx)
        force -= np.float32(lam)*phi*(phi*phi - 1)
        if eps1:
            force += np.float32(eps1*tau)
        vel *= np.float32(1 - d)
        vel += np.float32(dt)*force
        vel /= np.float32(1 + d)
        phi += np.float32(dt)*vel
        tau += dt
        step += 1
        if step % record_every == 0:
            area = wall_area(phi, dx)
            rows.append((tau, area/vol*tau/2, float(np.mean(phi < 0)), area/vol))
    return {'tau': np.array([r[0] for r in rows]), 'A': np.array([r[1] for r in rows]),
            'false_fraction': np.array([r[2] for r in rows]), 'area_density': np.array([r[3] for r in rows]),
            'final_field': phi}


def kink_tension(lam):
    """sigma_hat=(2 sqrt2/3) sqrt(lam) for V=(lam/4)(phi^2-1)^2 with v=1."""
    return 2*sqrt(2)/3*sqrt(lam)


def lattice_kink_check(lam=.5, dx=1., dt=.2, N=64, steps=400):
    """A planar lattice kink under PRS: its position and discrete energy stay put."""
    x = (np.arange(N) - N/2 + .5)*dx
    w = sqrt(2/lam)
    phi = np.tanh(x/w)
    # periodic box: add the antikink at the edge
    phi = np.tanh(x/w)*np.tanh((N*dx/2 - abs(x))/w)
    def energy(p):
        g = (np.roll(p, -1) - p)/dx
        return float(np.sum(g*g/2 + lam/4*(p*p - 1)**2)*dx)
    e0 = energy(phi); vel = np.zeros_like(phi); tau = 10.
    for _ in range(steps):
        d = 1.5*dt/tau
        force = laplacian(phi, dx) - lam*phi*(phi*phi - 1)
        vel = ((1 - d)*vel + dt*force)/(1 + d); phi = phi + dt*vel; tau += dt
    return {'continuum_two_walls': 2*kink_tension(lam), 'lattice_initial': e0, 'lattice_final': energy(phi),
            'max_velocity': float(abs(vel).max())}


def fit_plateau(tau, A, lo):
    m = tau >= lo
    return float(np.mean(A[m])), float(np.std(A[m])), float(np.polyfit(np.log(tau[m]), np.log(A[m]), 1)[0])


def annihilation_time(res, A_scaling, *, threshold=.5):
    """After the network has formed (A first above threshold*A_scaling), the first tau
    where A falls back below it; and the first tau where the false fraction is <1%."""
    tau, A = res['tau'], res['A']
    formed = np.flatnonzero(A >= threshold*A_scaling)
    t1 = np.nan
    if formed.size:
        later = np.flatnonzero((A < threshold*A_scaling) & (np.arange(len(A)) > formed[0]))
        t1 = tau[later[0]] if later.size else np.nan
    ff = np.minimum(res['false_fraction'], 1 - res['false_fraction'])
    t2 = tau[np.argmax(ff < .01)] if np.any(ff < .01) else np.nan
    return float(t1), float(t2)


def C_ann(tau_ann, eps1, lam, A_scaling):
    """C_ann=t_ann Delta V/(A sigma) with t=tau^2/2, Delta V/sigma=2 eps1/sigma_hat."""
    return tau_ann**2/2*2*eps1/(A_scaling*kink_tension(lam))


def _gradients(f, dx):
    return [(np.roll(f, -1, ax) - np.roll(f, 1, ax))/f.dtype.type(2*dx) for ax in range(3)]


PAIRS = ((0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2))


def gw_energy_spectrum(du, dx, nbins=48):
    """Transverse-traceless energy of the tensor velocity u'_ij, total and per log k bin.

    With P=1-k k/k^2, Lambda u=PuP-(1/2)P tr(PuP), and
    sum|Lambda u|^2=sum|PuP|^2-(1/2)|tr(PuP)|^2, tr(PuP)=tr u-khat.u.khat.
    Returns <h'_ij h'_ij> (spatial mean) and its distribution in |k|.
    """
    N = du[0].shape[0]
    U = {p: np.fft.rfftn(du[i]) for i, p in enumerate(PAIRS)}
    def comp(i, j):
        return U[(i, j)] if (i, j) in U else U[(j, i)]
    kx = np.fft.fftfreq(N, d=dx)*2*np.pi
    kz = np.fft.rfftfreq(N, d=dx)*2*np.pi
    K = np.meshgrid(kx, kx, kz, indexing='ij')
    kk = np.sqrt(K[0]**2 + K[1]**2 + K[2]**2)
    safe = np.where(kk > 0, kk, 1.)
    kh = [k/safe for k in K]
    w = [sum(comp(i, l)*kh[l] for l in range(3)) for i in range(3)]
    s = sum(kh[i]*w[i] for i in range(3))
    tot = 0.
    for i in range(3):
        for j in range(3):
            v = comp(i, j) - kh[i]*w[j] - w[i]*kh[j] + kh[i]*kh[j]*s
            tot = tot + abs(v)**2
    tr = comp(0, 0) + comp(1, 1) + comp(2, 2) - s
    dens = tot - .5*abs(tr)**2
    dens[kk == 0] = 0.
    # rfft weights: interior z-planes count twice.
    wgt = np.full(kz.shape, 2.); wgt[0] = 1.
    if N % 2 == 0:
        wgt[-1] = 1.
    dens = dens*wgt[None, None, :]
    mean = float(dens.sum())/N**6
    edges = np.geomspace(2*np.pi/(N*dx), np.pi/dx*sqrt(3), nbins + 1)
    idx = np.digitize(kk.ravel(), edges) - 1
    ok = (idx >= 0) & (idx < nbins)
    spec = np.bincount(idx[ok], weights=dens.ravel()[ok], minlength=nbins)/N**6
    centers = np.sqrt(edges[:-1]*edges[1:])
    return mean, centers, spec/np.log(edges[1:]/edges[:-1])


def evolve_physical_gw(N, *, w_final=2., dx=1., dt=.2, tau_i=10., tau_f=None, seed=0, measure_every=10.):
    """Physical (non-PRS) radiation-era walls with linear tensor modes sourced by d_i phi d_j phi.

    phi''+2 phi'/tau-lap phi=-tau^2 lam phi(phi^2-1), a=tau, with
    lam=2/(w_final*tau_f)^2 so the comoving width is w_final at tau_f.
    u_ij''+2u_ij'/tau-lap u_ij=16 pi G d_i phi d_j phi with G=1 (h is linear
    in G). GW energy rho_gw=<h'h'>/(32 pi G a^2); the efficiency is
    eps_gw=rho_gw/(G A^2 sigma^2), sigma=(2 sqrt2/3)sqrt(lam) physical.
    """
    tau_f = N*dx/2 if tau_f is None else tau_f
    lam = 2/(w_final*tau_f)**2
    sigma = kink_tension(lam)
    phi = initial_field(N, 3, seed)
    vel = np.zeros_like(phi)
    u = [np.zeros_like(phi) for _ in PAIRS]
    du = [np.zeros_like(phi) for _ in PAIRS]
    tau = tau_i
    vol = (N*dx)**3
    rows, next_measure = [], tau_i + measure_every
    f32 = np.float32
    while tau < tau_f - 1e-9:
        d = dt/tau  # (1/2)*2/tau*dt
        force = laplacian(phi, dx)
        force -= f32(tau*tau*lam)*phi*(phi*phi - 1)
        vel *= f32(1 - d); vel += f32(dt)*force; vel /= f32(1 + d)
        g = _gradients(phi, dx)
        for n, (i, j) in enumerate(PAIRS):
            src = laplacian(u[n], dx)
            src += f32(16*np.pi)*g[i]*g[j]
            du[n] *= f32(1 - d); du[n] += f32(dt)*src; du[n] /= f32(1 + d)
            u[n] += f32(dt)*du[n]
        phi += f32(dt)*vel
        tau += dt
        if tau >= next_measure - 1e-9:
            next_measure += measure_every
            area = wall_area(phi, dx)
            A = area/vol*tau/2
            hh, k, spec = gw_energy_spectrum(du, dx)
            rho = hh/(32*np.pi*tau*tau)
            rows.append({'tau': tau, 'A': A, 'rho_gw': rho, 'eps_gw': rho/(A*A*sigma*sigma),
                         'k': k.tolist(), 'drho_dlnk': (np.array(spec)/(32*np.pi*tau*tau)).tolist(),
                         'width_comoving': sqrt(2/lam)/tau})
    return {'lam': lam, 'sigma': sigma, 'rows': rows}
