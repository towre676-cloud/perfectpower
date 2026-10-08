"""Annihilation-phase gravitational waves from a biased physical wall network.

Extends wall_network.evolve_physical_gw (radiation era, a=tau, physical
equation, Garcia-Bellido-Figueroa-Sastre tensor modes) by a vacuum bias that
is switched on after the network has formed:

  V(phi) = (lam/4)(phi^2-1)^2 + eps s(tau) (phi^3/3 - phi),
  dV/dphi = (phi^2-1)(lam phi + eps s(tau)).

The cubic bias leaves both minima exactly at phi=+-1 (dV/dphi vanishes there
for every eps<lam) and splits them by Delta V = V(-1)-V(+1) = 4 eps/3, so
phi=+1 is the true vacuum and phi<0 marks the false vacuum. The ramp s(tau)
is a C^1 smoothstep from 0 at tau_on to 1 at tau_on+ramp; eps is a constant
physical energy density, the physically natural bias (no PRS rescaling).

Field equation (comoving lattice units, a=tau, H=1/tau^2, t=tau^2/2):
  phi''+2 phi'/tau-lap phi=-tau^2 dV/dphi,
  u_ij''+2 u_ij'/tau-lap u_ij=16 pi G d_i phi d_j phi  (G=1, TT part measured).
GW energy: rho_kin=<h'h'>/(32 pi G a^2) (convention of wall_gw.json) and the
oscillation-averaged rho_avg=(<h'h'>+<grad h grad h>)/(64 pi G a^2), the
latter with the lattice dispersion k_eff^2=sum_i (2 sin(k_i dx/2)/dx)^2.
For freely propagating sub-horizon tensor modes rho_avg a^4 is constant.

Floating-point float32 lattice evolution in a periodic box. Nothing here is a
certified integration; the box and resolution limits are reported as such.
"""
from math import sqrt, pi
import numpy as np
import scipy.fft as sfft
from . import wall_network as wn

PAIRS = wn.PAIRS
F32 = np.float32


# --- allocation-free stencils -------------------------------------------------

def _sl(ax, s):
    idx = [slice(None)]*3
    idx[ax] = s
    return tuple(idx)


def laplacian_into(f, out):
    """out = sum_ax f(x+e)+f(x-e)-2f(x) with dx=1 and periodic boundaries (no temporaries)."""
    np.multiply(f, F32(-6), out=out)
    for ax in range(3):
        out[_sl(ax, slice(1, None))] += f[_sl(ax, slice(None, -1))]
        out[_sl(ax, slice(0, 1))] += f[_sl(ax, slice(-1, None))]
        out[_sl(ax, slice(None, -1))] += f[_sl(ax, slice(1, None))]
        out[_sl(ax, slice(-1, None))] += f[_sl(ax, slice(0, 1))]
    return out


def gradient_into(f, ax, out):
    """Central difference (f(x+e)-f(x-e))/2 along ax, periodic, dx=1."""
    np.subtract(f[_sl(ax, slice(2, None))], f[_sl(ax, slice(None, -2))], out=out[_sl(ax, slice(1, -1))])
    np.subtract(f[_sl(ax, slice(1, 2))], f[_sl(ax, slice(-1, None))], out=out[_sl(ax, slice(0, 1))])
    np.subtract(f[_sl(ax, slice(0, 1))], f[_sl(ax, slice(-2, -1))], out=out[_sl(ax, slice(-1, None))])
    out *= F32(.5)
    return out


# --- TT projection with kinetic and gradient parts -----------------------------

def _tt_density(fields, N):
    """Per-mode |Lambda u|^2 on the rfft half-grid (weights for doubled planes included)."""
    U = {p: sfft.rfftn(fields[i], workers=1) for i, p in enumerate(PAIRS)}
    def comp(i, j):
        return U[(i, j)] if (i, j) in U else U[(j, i)]
    kx = np.fft.fftfreq(N)*2*np.pi
    kz = np.fft.rfftfreq(N)*2*np.pi
    K = np.meshgrid(kx, kx, kz, indexing='ij', sparse=True)
    kk = np.sqrt(K[0]**2 + K[1]**2 + K[2]**2)
    safe = np.where(kk > 0, kk, 1.)
    kh = [(k/safe).astype(np.float32) for k in K]
    w = [sum(comp(i, l)*kh[l] for l in range(3)) for i in range(3)]
    s = sum(kh[i]*w[i] for i in range(3))
    tot = 0.
    for i in range(3):
        for j in range(i, 3):
            v = comp(i, j) - kh[i]*w[j] - w[i]*kh[j] + kh[i]*kh[j]*s
            tot = tot + (1 if i == j else 2)*(v.real**2 + v.imag**2)
    tr = comp(0, 0) + comp(1, 1) + comp(2, 2) - s
    dens = tot - .5*(tr.real**2 + tr.imag**2)
    dens = np.broadcast_to(dens, (N, N, kz.size)).copy()
    kk = np.broadcast_to(kk, dens.shape)
    dens[kk == 0] = 0.
    wgt = np.full(kz.shape, 2.); wgt[0] = 1.
    if N % 2 == 0:
        wgt[-1] = 1.
    dens *= wgt[None, None, :]
    keff2 = sum(np.broadcast_to((2*np.sin(k/2))**2, dens.shape) for k in K)
    return dens, kk, keff2


def tt_spectra(u, du, nbins=48):
    """Return <h'h'>, <grad h grad h> (spatial means) and their spectra per ln k (dx=1)."""
    N = du[0].shape[0]
    dk, kk, keff2 = _tt_density(du, N)
    dg, _, _ = _tt_density(u, N)
    dg *= keff2
    edges = np.geomspace(2*np.pi/N, np.pi*sqrt(3), nbins + 1)
    idx = np.digitize(kk.ravel(), edges) - 1
    ok = (idx >= 0) & (idx < nbins)
    dl = np.log(edges[1:]/edges[:-1])
    out = []
    for d in (dk, dg):
        spec = np.bincount(idx[ok], weights=d.ravel()[ok], minlength=nbins)/N**6
        out.append((float(d.sum(dtype=np.float64))/N**6, spec/dl))
    return out[0][0], out[1][0], np.sqrt(edges[:-1]*edges[1:]), out[0][1], out[1][1]


# --- the evolution ----------------------------------------------------------

def bias_ramp(tau, tau_on, ramp):
    if tau <= tau_on:
        return 0.
    if ramp <= 0 or tau >= tau_on + ramp:
        return 1.
    x = (tau - tau_on)/ramp
    return x*x*(3 - 2*x)


def potential_parameters(lam, eps):
    """Exact minima, Delta V and the leading-order tension of the biased potential."""
    if not 0 <= eps < lam:
        raise ValueError('need 0 <= eps < lam so that phi=-1 stays a local minimum')
    return {'minima': [-1., 1.], 'maximum': -eps/lam, 'DeltaV': 4*eps/3,
            'sigma_unbiased': wn.kink_tension(lam)}


def evolve_biased_gw(N, *, eps=0., tau_on=40., ramp=5., w_ref=2., tau_ref=None, dt=.2, tau_i=10., tau_f=None,
                     seed=0, measure_every=4., nbins=48, spectra=True, gw=True, amplitude=.1,
                     field=None, tensors=None):
    """Physical radiation-era Z2 network with a switched-on cubic bias and linear tensor modes.

    lam=2/(w_ref tau_ref)^2 makes the comoving wall width w_ref at tau_ref (default N/2).
    Returns parameters and measurement rows (area parameter, false fraction, GW energies, spectra).
    gw=False skips the tensor modes (network-only runs). field (initial phi, zero velocity) and
    tensors=(u, u') override the random field and the zero initial tensor modes (used by the tests).
    """
    tau_ref = N/2 if tau_ref is None else tau_ref
    tau_f = N/2 if tau_f is None else tau_f
    lam = 2/(w_ref*tau_ref)**2
    pp = potential_parameters(lam, eps)
    sigma = pp['sigma_unbiased']
    phi = wn.initial_field(N, 3, seed, amplitude=amplitude) if field is None else np.array(field, np.float32)
    vel = np.zeros_like(phi)
    if tensors is None:
        u = [np.zeros_like(phi) for _ in PAIRS]
        du = [np.zeros_like(phi) for _ in PAIRS]
    else:
        u = [np.array(x, np.float32) for x in tensors[0]]
        du = [np.array(x, np.float32) for x in tensors[1]]
    force = np.empty_like(phi); tmp = np.empty_like(phi); src = np.empty_like(phi)
    g = [np.empty_like(phi) for _ in range(3)]
    tau = tau_i
    vol = float(N)**3
    rows, next_measure = [], tau_i + measure_every
    nsteps = int(round((tau_f - tau_i)/dt))
    for step in range(1, nsteps + 1):
        d = dt/tau
        e = eps*bias_ramp(tau, tau_on, ramp)
        laplacian_into(phi, force)
        # -tau^2 (phi^2-1)(lam phi+e)
        np.multiply(phi, phi, out=tmp); tmp -= F32(1)
        np.multiply(phi, F32(lam), out=src); src += F32(e)
        tmp *= src; tmp *= F32(tau*tau)
        force -= tmp
        vel *= F32(1 - d); force *= F32(dt); vel += force; vel *= F32(1/(1 + d))
        if gw:
            for ax in range(3):
                gradient_into(phi, ax, g[ax])
        for n, (i, j) in enumerate(PAIRS if gw else ()):
            laplacian_into(u[n], src)
            np.multiply(g[i], g[j], out=tmp); tmp *= F32(16*pi)
            src += tmp
            du[n] *= F32(1 - d); src *= F32(dt); du[n] += src; du[n] *= F32(1/(1 + d))
            np.multiply(du[n], F32(dt), out=tmp); u[n] += tmp
        np.multiply(vel, F32(dt), out=tmp); phi += tmp
        tau = tau_i + step*dt
        if tau >= next_measure - 1e-9 or step == nsteps:
            next_measure += measure_every
            area = wn.wall_area(phi, 1.)
            A = area/vol*tau/2
            row = {'tau': tau, 'A': A, 'false_fraction': float(np.mean(phi < 0)), 'bias_on': e/eps if eps else 0.,
                   'mean_phi': float(phi.mean(dtype=np.float64)),
                   'width_comoving': sqrt(2/lam)/tau}
            if spectra and gw:
                hk, hg, k, sk, sg = tt_spectra(u, du, nbins)
                a2 = tau*tau
                row.update({'rho_gw': hk/(32*pi*a2), 'rho_gw_avg': (hk + hg)/(64*pi*a2),
                            'k': k.tolist(), 'drho_dlnk': (sk/(32*pi*a2)).tolist(),
                            'drho_avg_dlnk': ((sk + sg)/(64*pi*a2)).tolist()})
            rows.append(row)
    return {'lam': lam, 'eps': eps, 'sigma': sigma, 'DeltaV': pp['DeltaV'], 'tau_on': tau_on, 'ramp': ramp,
            'rows': rows}


# --- analysis helpers ---------------------------------------------------------

def annihilation_times(rows, A_ref, tau_on, *, ff_threshold=.01, A_frac=.5):
    """First tau after the switch-on where the false fraction is below ff_threshold,
    and where A falls below A_frac*A_ref; linear interpolation between measurements."""
    tau = np.array([r['tau'] for r in rows]); A = np.array([r['A'] for r in rows])
    ff = np.array([min(r['false_fraction'], 1 - r['false_fraction']) for r in rows])
    def cross(y, level):
        m = np.flatnonzero((tau > tau_on) & (y < level))
        if not m.size:
            return float('nan')
        j = m[0]
        if j == 0 or y[j - 1] < level:
            return float(tau[j])
        t0, t1, y0, y1 = tau[j - 1], tau[j], y[j - 1], y[j]
        return float(t0 + (y0 - level)/(y0 - y1)*(t1 - t0))
    return cross(ff, ff_threshold), cross(A, A_frac*A_ref)


def pressure_balance_tau(sigma, DeltaV, K):
    """Classical t_ann=K sigma/DeltaV with t=tau^2/2: tau_ann=sqrt(2K sigma/DeltaV) (exponent 1/2)."""
    return sqrt(2*K*sigma/DeltaV)


def power_law_fit(x, y):
    """Least squares ln y = p ln x + c; returns p, prefactor, and the standard error of p."""
    x, y = np.log(np.asarray(x, float)), np.log(np.asarray(y, float))
    A = np.vstack([x, np.ones_like(x)]).T
    coef, res, *_ = np.linalg.lstsq(A, y, rcond=None)
    n = len(x)
    if n > 2:
        s2 = float(np.sum((y - A@coef)**2))/(n - 2)
        se = sqrt(s2/float(np.sum((x - x.mean())**2)))
    else:
        se = float('nan')
    return float(coef[0]), float(np.exp(coef[1])), se


def spectrum_shape(k, s, tau):
    """Peak k_p tau/(2 pi) and log slopes either side (same windows as develop_wall_gw)."""
    k, s = np.asarray(k), np.asarray(s)
    good = s > 0
    k, s = k[good], s[good]
    j = int(np.argmax(s))
    x = k*tau/(2*np.pi)
    ir = (x < x[j]/1.5) & (x > x[j]/6)
    uv = (x > x[j]*1.5) & (k < .5*np.pi)
    fit = lambda m: float(np.polyfit(np.log(x[m]), np.log(s[m]), 1)[0]) if m.sum() >= 3 else float('nan')
    return {'peak_k': float(k[j]), 'peak_bin': j, 'peak_f_over_H': float(x[j]), 'IR_slope': fit(ir), 'UV_slope': fit(uv)}
