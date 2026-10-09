"""Asymptotics of the biased Z2 wall network: annihilation law and GW peak.

One-parameter Press-Ryden-Spergel family (radiation era, a=tau, comoving
lattice units, dx=1):

  phi'' + (3-s) phi'/tau - lap phi = -tau^(2s) (phi^2-1)(lam phi + e(tau)),

with lam = 2/(w_ref tau_ref^s)^2, so the comoving wall width is
w(tau) = w_ref (tau_ref/tau)^s. s=1 is the physical equation of
wall_annihilation_gw.evolve_biased_gw (friction 2/tau, potential times a^2);
s=0 is the PRS fixed-width equation of wall_network.evolve (friction 3/tau).
The friction (3-s) satisfies the PRS momentum condition alpha+beta/2=3 for
walls with beta=2s, so the wall equation of motion (Lorentz factor, Hubble
damping) is the physical one for every s; only the width history changes.

Bias. The cubic bias of wall_annihilation_gw keeps the minima at +-1 and
splits them by 4e/3. With the factor tau^(2s) the comoving tension is
sigma0 tau^s, sigma0=(2 sqrt2/3) sqrt(lam), and the ratio of bias pressure to
curvature force on a wall of comoving radius R is tau^s (4e/3) R/sigma0.
For a constant physical ratio X = sigma/Delta V it must equal tau R/X, so

  e(tau) = (3/4) sigma0 tau^(1-s)/X   (times a C^1 switch-on ramp).

The classical pressure-balance law t_ann = K X with t=tau^2/2 then predicts
tau_ann = (2 K X)^(1/2) for every s, the same statement as for s=1.

Tensor modes (optional): u_ij'' + 2u_ij'/tau - lap u_ij = 16 pi G tau^(1-s)
d_i phi d_j phi. The factor tau^(1-s) restores the physical comoving
tension sigma0 tau of the s=1 walls (fat-wall rescaling of the source), so
eps_gw = rho_gw/(G A^2 sigma0^2) has the convention of wall_gw.json; for s=1
the factor is 1 and the equations are those of evolve_biased_gw. For s<1 the
wall profile is not the physical one, so only the geometry-driven quantities
(spectral peak, slopes) are meant to transfer, and the amplitude only to the
extent the source is wall-dominated.

Floating-point float32 lattice evolution in a periodic box; box and
resolution limits are reported, not removed. Nothing here is certified.
"""
from math import sqrt, pi
import numpy as np
from . import wall_network as wn
from . import wall_annihilation_gw as wa

F32 = np.float32
PAIRS = wn.PAIRS


def lam_for(s, w_ref, tau_ref):
    """Coupling giving comoving width w_ref at tau_ref, w(tau)=sqrt(2/lam) tau^-s."""
    return 2/(w_ref*tau_ref**s)**2


def sigma0(lam):
    return wn.kink_tension(lam)


def bias_e(tau, s, lam, X):
    """Cubic-bias coefficient e(tau) for constant physical sigma/Delta V = X (before the ramp)."""
    return .75*sigma0(lam)*tau**(1 - s)/X


def predicted_tau_ann(X, K):
    """Pressure balance t_ann = K X, t = tau^2/2."""
    return sqrt(2*K*X)


def evolve(N, *, s=0., w_ref=2., tau_ref=1., X=None, tau_on=0., ramp=0., tau_i=1., tau_f=None, dt=.2,
           seed=0, amplitude=.1, kmax_frac=.25, measure_every=1., gw=False, gw_every=None, nbins=48,
           field=None, stop_false_fraction=None, return_field=False):
    """Evolve the s-family network, optionally with tensor modes.

    X=None is the unbiased network. Measurements every measure_every: tau, A, false fraction,
    bias/barrier ratio (4e/3)/(lam/4); with gw, every gw_every also the TT energies and spectra.
    stop_false_fraction ends the run once min(f, 1-f) is below it (after tau_on), saving time.
    return_field adds the final phi (used by the tests).
    """
    tau_f = N/2 if tau_f is None else tau_f
    lam = lam_for(s, w_ref, tau_ref)
    sig = sigma0(lam)
    if field is None:
        phi = wn.initial_field(N, 3, seed, kmax_frac=kmax_frac, amplitude=amplitude)
    else:
        phi = np.array(field, np.float32)
    vel = np.zeros_like(phi)
    force = np.empty_like(phi); tmp = np.empty_like(phi); src = np.empty_like(phi)
    if gw:
        u = [np.zeros_like(phi) for _ in PAIRS]
        du = [np.zeros_like(phi) for _ in PAIRS]
        g = [np.empty_like(phi) for _ in range(3)]
        gw_every = measure_every if gw_every is None else gw_every
        next_gw = tau_i + gw_every
    vol = float(phi.size)  # N^3 for the cubic boxes; slabs are allowed for tests
    rows = []
    next_measure = tau_i + measure_every
    nsteps = int(round((tau_f - tau_i)/dt))
    max_bias_barrier = 0.
    tau = tau_i
    for step in range(1, nsteps + 1):
        d = .5*(3 - s)*dt/tau
        e = bias_e(tau, s, lam, X)*wa.bias_ramp(tau, tau_on, ramp) if X else 0.
        if e >= lam:
            raise ValueError('bias e(tau)=%g reached lam=%g at tau=%g: false vacuum no longer metastable' % (e, lam, tau))
        max_bias_barrier = max(max_bias_barrier, (4*e/3)/(lam/4))
        a2s = tau**(2*s)
        wa.laplacian_into(phi, force)
        np.multiply(phi, phi, out=tmp); tmp -= F32(1)
        np.multiply(phi, F32(lam), out=src); src += F32(e)
        tmp *= src; tmp *= F32(a2s)
        force -= tmp
        vel *= F32(1 - d); force *= F32(dt); vel += force; vel *= F32(1/(1 + d))
        if gw:
            dg = dt/tau
            for ax in range(3):
                wa.gradient_into(phi, ax, g[ax])
            c = F32(16*pi*tau**(1 - s))
            for n, (i, j) in enumerate(PAIRS):
                wa.laplacian_into(u[n], src)
                np.multiply(g[i], g[j], out=tmp); tmp *= c
                src += tmp
                du[n] *= F32(1 - dg); src *= F32(dt); du[n] += src; du[n] *= F32(1/(1 + dg))
                np.multiply(du[n], F32(dt), out=tmp); u[n] += tmp
        np.multiply(vel, F32(dt), out=tmp); phi += tmp
        tau = tau_i + step*dt
        last = step == nsteps
        if tau >= next_measure - 1e-9 or last:
            next_measure += measure_every
            area = wn.wall_area(phi, 1.)
            ff = float(np.count_nonzero(phi < 0))/vol
            row = {'tau': tau, 'A': area/vol*tau/2, 'false_fraction': ff,
                   'bias_over_barrier': (4*e/3)/(lam/4), 'width_comoving': sqrt(2/lam)*tau**(-s)}
            if gw and (tau >= next_gw - 1e-9 or last):
                next_gw += gw_every
                hk, hg, k, sk, sg = wa.tt_spectra(u, du, nbins)
                a2 = tau*tau
                row.update({'rho_gw': hk/(32*pi*a2), 'rho_gw_avg': (hk + hg)/(64*pi*a2),
                            'k': k.tolist(), 'drho_dlnk': (sk/(32*pi*a2)).tolist(),
                            'drho_avg_dlnk': ((sk + sg)/(64*pi*a2)).tolist()})
            rows.append(row)
            if stop_false_fraction is not None and X and tau > tau_on and min(ff, 1 - ff) < stop_false_fraction:
                break
    out = {'s': s, 'lam': lam, 'sigma0': sig, 'X': X, 'tau_on': tau_on, 'ramp': ramp,
           'max_bias_over_barrier': max_bias_barrier, 'rows': rows}
    if return_field:
        out['field'] = phi
    return out


def thin_wall_displacement(X, tau_i, tau, n=4000):
    """Planar wall from rest at tau_i: (gamma v)' + 3 gamma v/tau = tau/X (a=tau), so
    gamma v = (tau^5 - tau_i^5)/(5 X tau^3); returns the comoving distance moved (trapezoid rule)."""
    t = np.linspace(tau_i, tau, n)
    P = (t**5 - tau_i**5)/(5*X*t**3)
    v = P/np.sqrt(1 + P*P)
    return float(np.sum(.5*(v[1:] + v[:-1])*np.diff(t)))


# --- analysis ----------------------------------------------------------------

def annihilation_tau(rows, tau_on, level=.01):
    """First tau after tau_on with min(f,1-f) below level, linearly interpolated."""
    tau = np.array([r['tau'] for r in rows])
    ff = np.array([min(r['false_fraction'], 1 - r['false_fraction']) for r in rows])
    m = np.flatnonzero((tau > tau_on) & (ff < level))
    if not m.size:
        return float('nan')
    j = m[0]
    if j == 0 or ff[j - 1] < level:
        return float(tau[j])
    return float(tau[j - 1] + (ff[j - 1] - level)/(ff[j - 1] - ff[j])*(tau[j] - tau[j - 1]))


def local_exponents(X, tau):
    """Sorted-by-X successive log slopes d ln tau/d ln X with the geometric mid-points."""
    o = np.argsort(X)
    x, y = np.log(np.asarray(X, float)[o]), np.log(np.asarray(tau, float)[o])
    return np.exp(.5*(x[1:] + x[:-1])), np.diff(y)/np.diff(x)


def fit_power(X, tau):
    return wa.power_law_fit(X, tau)


def fit_offset(X, tau):
    """t_ann - t0 = K X with t=tau^2/2 (ordinary least squares in t)."""
    X = np.asarray(X, float); t = np.asarray(tau, float)**2/2
    M = np.vstack([X, np.ones_like(X)]).T
    (K, t0), *_ = np.linalg.lstsq(M, t, rcond=None)
    r = t - M@np.array([K, t0])
    n = len(X)
    se = sqrt(float(np.sum(r*r))/(n - 2)/float(np.sum((X - X.mean())**2))) if n > 2 else float('nan')
    return float(K), float(t0), se


def fit_power_with_offset(X, tau):
    """tau^2/2 = t0 + K X^q (q = 2p_asymptotic): grid search in q, linear in (K, t0). Returns q, K, t0."""
    X = np.asarray(X, float); t = np.asarray(tau, float)**2/2
    best = None
    for q in np.linspace(.5, 1.5, 201):
        M = np.vstack([X**q, np.ones_like(X)]).T
        coef, *_ = np.linalg.lstsq(M, t, rcond=None)
        r = float(np.sum((np.log(t) - np.log(np.maximum(M@coef, 1e-30)))**2))
        if best is None or r < best[0]:
            best = (r, float(q), float(coef[0]), float(coef[1]))
    return best[1], best[2], best[3]


def spectrum_shape(k, s, tau, ir_bins_min=3):
    """Peak k, peak bin, f/H = k tau/(2pi), and the log slope of all bins from the box mode to below the peak.

    IR slope: least squares over bins with k <= k_peak/1.5 (needs ir_bins_min such bins).
    """
    k, s = np.asarray(k, float), np.asarray(s, float)
    good = s > 0
    k, s = k[good], s[good]
    j = int(np.argmax(s))
    ir = k <= k[j]/1.5
    uv = (k >= 1.5*k[j]) & (k < .5*pi)
    fit = lambda m: float(np.polyfit(np.log(k[m]), np.log(s[m]), 1)[0]) if m.sum() >= ir_bins_min else float('nan')
    kp = peak_log_parabola(k, s, j)
    return {'peak_k': float(k[j]), 'peak_bin': j, 'peak_f_over_H': float(k[j]*tau/(2*pi)),
            'peak_k_parabola': kp, 'peak_f_over_H_parabola': kp*tau/(2*pi),
            'peak_over_box': float(k[j]/k[0]), 'n_ir_bins': int(ir.sum()), 'IR_slope': fit(ir), 'UV_slope': fit(uv)}


def peak_log_parabola(k, s, j=None, half=2):
    """Vertex of a parabola fitted to ln s against ln k over the 2*half+1 bins around the maximum bin j.
    nan if the window leaves the data or the parabola does not open downwards inside the window."""
    k, s = np.asarray(k, float), np.asarray(s, float)
    j = int(np.argmax(s)) if j is None else j
    if j - half < 0 or j + half >= len(k):
        return float('nan')
    x, y = np.log(k[j - half:j + half + 1]), np.log(s[j - half:j + half + 1])
    a, b, _ = np.polyfit(x, y, 2)
    if a >= 0:
        return float('nan')
    xv = -b/(2*a)
    return float(np.exp(xv)) if x[0] <= xv <= x[-1] else float('nan')
