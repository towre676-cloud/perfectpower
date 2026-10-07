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
