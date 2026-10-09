"""All physical vector polarizations in the decay of the planar wall mode.

Unitary-gauge Proca field with position-dependent mass m(z)=c h(z) on a
planar wall (h>0 everywhere). The wall preserves the 2+1 Lorentz group of the
parallel directions, so every bulk vector mode is a 2+1 particle with
3-momentum P, P^2=s3=k_z^2+m0^2, labelled by its normal momentum k_z. For
fixed P the three physical polarizations are

  TE     eps=(0,y_hat), A_z=0;                    f solves L_T f=s3 f,
  TM_par eps=(|p|, omega p_hat)/sqrt(s3), A_z=0;  the same L_T waves,
  TM_n   A^z=sqrt(s3) chi/m, A^a=-i P^a D/sqrt(s3), D=(m chi)'/m^2;
         chi solves L_L chi=s3 chi, L_L=-d^2+m^2+2(m'/m)^2-m''/m.

L_T=-d^2+m^2. The TM_n (normal/longitudinal) mode carries the eaten
Goldstone. Its conserved Proca charge density is Im(A*_nu F^{0 nu})=omega chi^2
exactly (exact_identities), so chi is delta-normalized exactly like f and
reduces to the unit vacuum polarization far from the wall.

The unitary-gauge cubic vertex is (dm^2/dH) dH (W+W-) or (1/2)(dm^2/dH) dH ZZ,
dH the canonical Higgs component of the wall mode. It is the only tree
vertex of one wall-mode quantum to two vectors. All numerics are
floating-point distorted-wave Born calculations, not interval enclosures.
"""
from math import pi, sqrt, log
import json
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import solve_ivp, simpson
from scipy.interpolate import CubicSpline, RectBivariateSpline
from scipy.linalg import eigh_tridiagonal

HBAR_GEV_S = 6.582119569e-25
SECTOR_PAIRS = ('TE_TE', 'TMpar_TMpar', 'TMpar_TMn', 'TMn_TMpar', 'TMn_TMn')


# ---------------------------------------------------------------- algebra
def exact_identities():
    """Symbolic checks: polarizations, Proca equations of TM_n, charge norm, m->0 limit."""
    import sympy as sp
    w, p, k, m, s = sp.symbols('omega p k m s', positive=True)
    g = sp.diag(1, -1, -1, -1)
    K = sp.Matrix([w, p, 0, k])
    s_ = w**2-p**2
    # Plane-wave TM_n polarization from the chi map with chi=exp(ikz):
    # A^a=P^a k/(sqrt(s3)m), A^z=sqrt(s3)/m (overall phase dropped).
    eN = sp.Matrix([w*k/(sp.sqrt(s_)*m), p*k/(sp.sqrt(s_)*m), 0, sp.sqrt(s_)/m])
    eT = sp.Matrix([0, 0, 1, 0])
    eP = sp.Matrix([p, w, 0, 0])/sp.sqrt(s_)
    dot = lambda a, b: (a.T*g*b)[0]
    onshell = {w: sp.sqrt(p**2+k**2+m**2)}
    checks = {}
    for name, e in (('TE', eT), ('TM_par', eP), ('TM_n', eN)):
        checks[name+'_transverse'] = dot(e, K).subs(onshell)
        checks[name+'_unit_spacelike'] = (dot(e, e)+1).subs(onshell)
    checks['TMpar_TMn_orthogonal'] = dot(eP, eN).subs(onshell)
    checks['TE_TMn_orthogonal'] = dot(eT, eN)
    completeness = eT*eT.T+eP*eP.T+eN*eN.T-(-g.inv()+K*K.T/m**2)
    for i in range(4):
        for j in range(i, 4):
            checks[f'vacuum_completeness_{i}{j}'] = completeness[i, j].subs(onshell)
    # Contractions used in the pair amplitudes (P1=(w1,p), P2=(w2,-p)).
    w1, w2 = sp.symbols('omega1 omega2', positive=True)
    s1, s2 = w1**2-p**2, w2**2-p**2
    e1 = sp.Matrix([p, w1, 0])/sp.sqrt(s1); e2 = sp.Matrix([p, -w2, 0])/sp.sqrt(s2)
    P1 = sp.Matrix([w1, p, 0]); P2 = sp.Matrix([w2, -p, 0]); h3 = sp.diag(1, -1, -1)
    d3 = lambda a, b: (a.T*h3*b)[0]
    checks['TMpar_TMpar_contraction'] = d3(e1, e2)-d3(P1, P2)/(sp.sqrt(s1)*sp.sqrt(s2))
    checks['TMpar_P2_contraction'] = d3(e1, P2)-p*(w1+w2)/sp.sqrt(s1)
    checks['TMpar_P1_orthogonal'] = d3(e1, P1)
    checks['P1P2_invariant'] = d3(P1, P2)-((w1+w2)**2-s1-s2)/2
    # Full Proca equations d_mu F^{mu nu}+m(z)^2 A^nu=0 for the TM_n ansatz.
    t, X, Z = sp.symbols('t x z', real=True)
    mz = sp.Function('m')(Z); chi = sp.Function('chi')(Z)
    am = sp.diff(mz, Z)/mz
    UL = mz**2+2*am**2-sp.diff(mz, Z, 2)/mz
    D = sp.diff(mz*chi, Z)/mz**2
    phase = sp.exp(-sp.I*(w*t-p*X))
    Aup = [-sp.I*w*D/sp.sqrt(s)*phase, -sp.I*p*D/sp.sqrt(s)*phase, 0, sp.sqrt(s)*chi/mz*phase]
    coords = [t, X, sp.Symbol('y'), Z]
    eta = [1, -1, -1, -1]
    Alow = [eta[i]*Aup[i] for i in range(4)]
    F = [[sp.diff(Alow[j], coords[i])-sp.diff(Alow[i], coords[j]) for j in range(4)] for i in range(4)]
    Fup = [[eta[i]*eta[j]*F[i][j] for j in range(4)] for i in range(4)]
    chidd = {sp.diff(chi, Z, 2): (UL-s)*chi}
    for nu, name in enumerate(['t', 'x', 'y', 'z']):
        eq = sum(sp.diff(Fup[mu][nu], coords[mu]) for mu in range(4))+mz**2*Aup[nu]
        eq = sp.expand(eq.subs(w, sp.sqrt(s+p**2))/phase)
        eq = eq.subs(sp.Derivative(chi, (Z, 3)), sp.diff((UL-s)*chi, Z)).subs(chidd)
        checks[f'TMn_Proca_equation_{name}'] = eq
    # Conserved charge density Im(conj(A_nu) F^{0 nu}) equals omega chi^2.
    # All profile functions are real: complex conjugation is I -> -I.
    amp = [a/phase for a in Alow]
    famp = [sp.expand(Fup[0][nu]/phase) for nu in range(4)]
    charge = sp.expand(sum(amp[nu].subs(sp.I, -sp.I)*famp[nu] for nu in range(4)))
    imag = sp.expand((charge-charge.subs(sp.I, -sp.I))/(2*sp.I)).subs(chidd)
    checks['TMn_Proca_charge_density'] = imag-w*chi**2
    # Goldstone equivalence: m->0 TM_n wave chi=D_- G/k with D_-=d/dz-a maps
    # L_G G=k^2 G to the m=0 partner (B B^dagger) chi=k^2 chi, and (h chi)'=-k h G.
    z = sp.Symbol('z'); h = sp.Function('h')(z); psi = sp.Function('psi')(z)
    a = sp.diff(h, z)/h
    G = sp.Function('G')(z)
    LG = -sp.diff(G, z, 2)+sp.diff(h, z, 2)/h*G
    DG = sp.diff(G, z)-a*G
    LL0 = -sp.diff(DG, z, 2)+(2*a*a-sp.diff(h, z, 2)/h)*DG
    checks['partner_intertwining'] = LL0-(sp.diff(LG, z)-a*LG)
    checks['TMn_derivative_map'] = sp.diff(h*DG, z)+h*LG
    wv = psi/h
    bracket = sp.diff(wv, z, 2)/2-wv*sp.diff(h, z, 2)/h+sp.diff(wv*a, z)+wv*a*a
    checks['equivalence_bracket'] = bracket-(sp.diff(psi, z, 2)-sp.diff(h, z, 2)/h*psi)/(2*h)
    # Longitudinal factorization L_L=(-d+a_m)(d+a_m)+m^2 used for the spectral floor.
    f = sp.Function('f')(Z)
    checks['longitudinal_factorization'] = (-sp.diff(sp.diff(f, Z)+am*f, Z)+am*(sp.diff(f, Z)+am*f)+mz**2*f)-(-sp.diff(f, Z, 2)+UL*f)
    reduced = {n: sp.simplify(v) for n, v in checks.items()}
    bad = [n for n, v in reduced.items() if v != 0]
    if bad:raise ArithmeticError('vector polarization algebra mismatch: '+', '.join(bad))
    return {n: '0' for n in reduced}


# ---------------------------------------------------------------- continuum
def parity_waves(x, potential, momenta, *, rtol=2e-10):
    """Delta-normalized even/odd waves of -d^2+U and their x-derivatives.

    Same normalization as wall_pair_decay.parity_continuum (asymptotic
    amplitude 1/sqrt(pi) in q), with the derivative returned as well.
    Returns arrays [parity, momentum, x], parity 0 even, 1 odd.
    """
    x = np.asarray(x, float); q = np.asarray(momenta, float); U = np.asarray(potential, float)
    if x.ndim != 1 or len(x) < 4 or x[0] != 0 or np.any(np.diff(x) <= 0):raise ValueError('increasing half-line mesh from zero required')
    if U.shape != x.shape or q.ndim != 1 or np.any(q <= 0) or not np.all(np.isfinite(U)):raise ValueError('positive momenta and finite matching potential required')
    n = len(q); ui = CubicSpline(x, U)
    init = np.zeros((2, 2, n)); init[0, 0] = 1; init[1, 1] = q
    def rhs(t, z):
        z = z.reshape(2, 2, n); out = np.empty_like(z); out[:, 0] = z[:, 1]; out[:, 1] = (ui(t)-q*q)*z[:, 0]
        return out.ravel()
    sol = solve_ivp(rhs, (0, x[-1]), init.ravel(), t_eval=x, method='DOP853', rtol=rtol, atol=rtol*.05)
    if not sol.success:raise ArithmeticError(sol.message)
    z = sol.y.reshape(2, 2, n, len(x))
    amp = np.hypot(z[:, 0, :, -1], z[:, 1, :, -1]/q)
    c = 1/(amp[:, :, None]*sqrt(pi))
    return z[:, 0]*c, z[:, 1]*c


def pair_phase_space(M, m1, m2, order=64):
    """Nested Gauss rule on sqrt(k^2+m1^2)+sqrt(l^2+m2^2)<M, k,l>0."""
    if not (np.isfinite(M) and M > 0 and m1 >= 0 and m2 >= 0 and order >= 4):raise ValueError('positive parent mass, nonnegative leg masses, order>=4')
    if M <= m1+m2:return np.empty((0, 0)), np.empty((0, 0)), np.empty((0, 0))
    a, w = leggauss(order); a = (a+1)/2; w = w/2
    kmax = sqrt((M-m2)**2-m1**2); k = kmax*a
    lm = np.sqrt(np.maximum((M-np.sqrt(k*k+m1*m1))**2-m2*m2, 0))
    return np.broadcast_to(k[:, None], (order, order)), lm[:, None]*a, kmax*w[:, None]*lm[:, None]*w


def simpson_weights(x):
    n = len(x)
    if n % 2 != 1:raise ValueError('odd node count required for Simpson weights')
    w = np.ones(n); w[1:-1:2] = 4; w[2:-1:2] = 2
    return w*(x[1]-x[0])/3


def _leg(prof, mu_kin, mu_prof, grid, rtol):
    """TE/TM_par wave f, and the TM_n pieces D=(m chi)'/m^2 and C=chi/m (x units)."""
    UT = mu_prof**2*prof['relative_barrier']
    UL = UT+prof['L_extra']
    fT, _ = parity_waves(prof['x'], UT, grid, rtol=rtol)
    chi, dchi = parity_waves(prof['x'], UL, grid, rtol=rtol)
    mt = mu_kin*prof['h_over_h0']
    return {'T': fT, 'D': (dchi+prof['a']*chi)/mt, 'C': chi/mt}


def pair_width_core(prof, M, mu1, mu2, *, identical, prof_mass1=None, prof_mass2=None,
                    momentum_nodes=193, order=64, rtol=2e-10, kernels_out=False):
    """Polarization-resolved distorted-wave pair width in wall units.

    prof: dict with x (half line, odd count), Vw (vertex times full-line
    quadrature weights), relative_barrier (h^2/h0^2-1), a=h'/h, L_extra=2a^2-h''/h,
    h_over_h0. Masses in the same inverse-x units. Gamma=S/(8 M^2) int dq dq' sum|amp|^2.
    mu_kin (mu1, mu2) enter kinematics and polarization maps, prof_mass the bulk barrier.
    Distinct polarization/parity final states do not interfere.
    """
    pm1 = mu1 if prof_mass1 is None else prof_mass1; pm2 = mu2 if prof_mass2 is None else prof_mass2
    zero = {n: 0. for n in SECTOR_PAIRS}
    if M <= mu1+mu2:return {'open': False, 'width': 0., 'sectors': zero, 'parity': {}}
    k, l, w = pair_phase_space(M, mu1, mu2, order)
    lo = .2*min(k.min(), l.min())
    def grid(qmax):return lo+(qmax*1.00001-lo)*np.linspace(0, 1, momentum_nodes)**2
    g1 = grid(sqrt((M-mu2)**2-mu1**2)); g2 = grid(sqrt((M-mu1)**2-mu2**2))
    A = _leg(prof, mu1, pm1, g1, rtol); B = _leg(prof, mu2, pm2, g2, rtol)
    Vw = prof['Vw']
    K = lambda a, b: (a*Vw[None, :])@b.T
    ker = {}
    for p in (0, 1):
        o = 1-p
        ker['TT', p] = K(A['T'][p], B['T'][p])
        ker['TN', p] = K(A['T'][p], B['D'][o])     # f parity p, chi parity o (D parity p)
        ker['NT', p] = K(A['D'][o], B['T'][p])
        ker['Nd', p] = K(A['D'][p], B['D'][p])     # chi parities p
        ker['Nc', p] = K(A['C'][p], B['C'][p])
    kk, ll = k.ravel(), l.ravel()
    ev = {key: RectBivariateSpline(g1, g2, v, kx=3, ky=3, s=0).ev(kk, ll).reshape(k.shape) for key, v in ker.items()}
    s1 = k*k+mu1*mu1; s2 = l*l+mu2*mu2
    om1 = (M*M+s1-s2)/(2*M); pp = np.sqrt(np.maximum(om1*om1-s1, 0))
    PP = (M*M-s1-s2)/2; r = np.sqrt(s1*s2)
    S = .5 if identical else 1.
    fac = S/(8*M*M)
    sectors = {n: 0. for n in SECTOR_PAIRS}; parity = {}
    for p in (0, 1):
        amps = {'TE_TE': ev['TT', p], 'TMpar_TMpar': ev['TT', p]*PP/r,
                'TMpar_TMn': ev['TN', p]*pp*M/r, 'TMn_TMpar': ev['NT', p]*pp*M/r,
                'TMn_TMn': -(PP/r)*ev['Nd', p]-r*ev['Nc', p]}
        for n, a in amps.items():
            val = float(fac*np.sum(w*a*a)); sectors[n] += val; parity[n+('_even' if p == 0 else '_odd')] = val
    out = {'open': True, 'width': sum(sectors.values()), 'sectors': sectors, 'parity': parity}
    if kernels_out:out.update({'grid1': g1, 'grid2': g2, 'kernels': ker})
    return out


# ---------------------------------------------------------------- candidate
def candidate_profile(solution, *, spatial_nodes=2601):
    """Background, vertex unit and Goldstone data for the main candidate solution
    (wall_gauge_channels.candidate_channel_solution)."""
    wall = solution['wall']; model = wall['model']; bath = wall['bath']; k = wall['k']
    x = np.linspace(0, k*wall['L'], spatial_nodes); rho = x/k
    sol = wall['solution'].sol(rho); u, h, hp = sol[0], sol[2], sol[5]
    psi = solution['mode'].sol(x)[:3]/k
    norm = 2*simpson(np.sum(psi*psi, axis=0), x=rho); nrm = sqrt(model.v_GeV/norm)
    h0 = bath.v_GeV/model.v_GeV; scale = model.v_GeV*k
    VG = bath.lam*(h*h-h0*h0)+bath.portal*(u*u-1)          # h_rho rho / h (static equation)
    a = hp/h/k
    weights = simpson_weights(x)
    M = model.v_GeV*sqrt(solution['mode_energy_over_v2'])
    return {'x': x, 'scale_GeV': scale, 'k': k, 'h0': h0, 'v_GeV': model.v_GeV, 'v_H_GeV': bath.v_GeV,
            'M_GeV': M, 'M': M/scale,
            'relative_barrier': h*h/(h0*h0)-1, 'a': a, 'L_extra': 2*a*a-VG/k**2, 'h_over_h0': h/h0,
            # main's (wall_pair_decay) vector vertex normalization*coupling*h*psi_H/2 with 2/k: per unit coupling
            'Vw_unit': (2/k)*weights*nrm*h*psi[2]/2,
            'psi_H_canonical': nrm*psi[2], 'quadrature_weights': weights,
            'normalization_over_rho': norm, 'max_relative_barrier': float(np.max(h*h/(h0*h0)-1))}


def vector_pair_widths(prof, coupling, *, identical, mu1_GeV=None, mu2_GeV=None, prof_mass_GeV=None,
                       momentum_nodes=193, order=64, rtol=2e-10):
    """All-polarization pair width (GeV) for W (coupling g^2, distinguishable W+W-)
    or Z (coupling g^2+g'^2, identical)."""
    if coupling <= 0:raise ValueError('positive declared coupling required')
    sc = prof['scale_GeV']; m0 = sqrt(coupling)*prof['v_H_GeV']/2
    mu1 = m0 if mu1_GeV is None else mu1_GeV; mu2 = m0 if mu2_GeV is None else mu2_GeV
    pm1 = mu1 if prof_mass_GeV is None else prof_mass_GeV
    pm2 = mu2 if prof_mass_GeV is None else prof_mass_GeV
    P = {**prof, 'Vw': coupling*prof['Vw_unit']}
    r = pair_width_core(P, prof['M'], mu1/sc, mu2/sc, identical=identical, prof_mass1=pm1/sc, prof_mass2=pm2/sc,
                        momentum_nodes=momentum_nodes, order=order, rtol=rtol)
    s = r['sectors']
    return {'width_GeV': r['width'], 'open': r['open'], 'vacuum_mass_GeV': m0, 'leg_masses_GeV': [mu1, mu2],
            'TE_GeV': s['TE_TE'], 'TM_par_pair_GeV': s['TMpar_TMpar'],
            'TM_par_TM_n_mixed_GeV': s['TMpar_TMn']+s['TMn_TMpar'], 'TM_n_pair_GeV': s['TMn_TMn'],
            'parity_resolved_GeV': r['parity'], 'momentum_nodes': momentum_nodes, 'phase_space_order': order}


def coupling_scan(prof, gs, gprime, **kw):
    rows = []
    for g in gs:
        W = vector_pair_widths(prof, g*g, identical=False, **kw)
        Z = vector_pair_widths(prof, g*g+gprime*gprime, identical=True, **kw)
        rows.append({'declared_g': g, 'declared_gprime': gprime, 'WW': W, 'ZZ': Z,
                     'total_vector_pair_width_GeV': W['width_GeV']+Z['width_GeV'],
                     'TE_only_width_GeV': W['TE_GeV']+Z['TE_GeV'],
                     'lifetime_from_vector_pairs_s': HBAR_GEV_S/(W['width_GeV']+Z['width_GeV']) if W['width_GeV']+Z['width_GeV'] > 0 else None})
    return rows


def goldstone_equivalence_scan(prof, couplings_list, goldstone_width_GeV, **kw):
    """TM_n TM_n width of W+W- (identical=False) versus 2/3 of the three-Goldstone width.

    Equivalence: W_L+W_L- <-> G+G- (two real Goldstones), Z_L Z_L <-> G3 G3, so
    Gamma(W_L W_L)+Gamma(Z_L Z_L) -> Gamma_GG as m_V/M->0 at fixed vertex.
    Richardson extrapolation assumes deficit = a m + b m^2 on a halving ladder.
    """
    rows = []
    for c in couplings_list:
        r = vector_pair_widths(prof, c, identical=False, **kw)
        rows.append({'coupling_squared': c, 'vector_mass_GeV': r['vacuum_mass_GeV'], 'mass_over_M': r['vacuum_mass_GeV']/prof['M_GeV'],
                     'TM_n_pair_GeV': r['TM_n_pair_GeV'], 'ratio_to_two_thirds_Goldstone': r['TM_n_pair_GeV']/(2*goldstone_width_GeV/3),
                     'TE_GeV': r['TE_GeV'], 'TM_par_pair_GeV': r['TM_par_pair_GeV'], 'mixed_GeV': r['TM_par_TM_n_mixed_GeV']})
    ratio = [r['ratio_to_two_thirds_Goldstone'] for r in rows]
    ext = None
    if len(ratio) >= 3:
        r1 = [2*ratio[i+1]-ratio[i] for i in range(len(ratio)-1)]
        r2 = [(4*r1[i+1]-r1[i])/3 for i in range(len(r1)-1)]
        ext = {'linear_Richardson': r1, 'second_Richardson': r2, 'extrapolated_ratio': r2[-1]}
    return {'rows': rows, 'Goldstone_width_GeV': goldstone_width_GeV, 'extrapolation': ext}


def threshold_scan(prof, deficits_GeV, **kw):
    """Near-threshold W+W- widths at M-2m_W=deficit and local log slopes per sector."""
    M = prof['M_GeV']; vH = prof['v_H_GeV']; keys = ['TE_GeV', 'TM_par_pair_GeV', 'TM_par_TM_n_mixed_GeV', 'TM_n_pair_GeV', 'width_GeV']
    rows = []
    for d in deficits_GeV:
        g = (M-d)/vH
        r = vector_pair_widths(prof, g*g, identical=False, **kw)
        row = {'pair_energy_excess_GeV': d, 'declared_g': g, **{k: r[k] for k in keys}}
        if rows:
            prev = rows[-1]
            row['log_slopes'] = {k: log(row[k]/prev[k])/log(d/prev['pair_energy_excess_GeV']) for k in keys}
        rows.append(row)
    return rows


# ---------------------------------------------------------------- declared widths
def declared_vector_widths(g, gprime, v_H_GeV, *, alpha_s=0.):
    """Tree-level W and Z total widths to massless fermions (top excluded).

    Fermion content: three lepton generations; quarks u,d,c,s (W: two unitary-CKM
    doublets) and u,c,d,s,b (Z), N_c=3. Quark channels optionally times (1+alpha_s/pi).
    """
    mW = g*v_H_GeV/2; gz2 = g*g+gprime*gprime; mZ = sqrt(gz2)*v_H_GeV/2; sw2 = gprime*gprime/gz2
    K = 1+alpha_s/pi
    W = g*g*mW/(48*pi)*(3+2*3*K)
    def z(T3, Q, Nc):return Nc*((T3-Q*sw2)**2+(Q*sw2)**2)
    zsum = 3*z(.5, 0, 1)+3*z(-.5, -1, 1)+K*(2*z(.5, 2/3, 3)+3*z(-.5, -1/3, 3))
    Z = gz2*mZ/(24*pi)*zsum
    return {'W_mass_GeV': mW, 'Z_mass_GeV': mZ, 'sin2_theta_W': sw2, 'W_width_GeV': W, 'Z_width_GeV': Z,
            'alpha_s_quark_factor': K,
            'fermion_content': 'massless; W: e,mu,tau doublets + (u,d),(c,s) x3 colours; Z: 3 nu, e,mu,tau, u,c,d,s,b x3 colours; no top'}


# ---------------------------------------------------------------- off shell
def breit_wigner_density(s, m, width, *, running=True):
    """Spectral weight (1/pi) sqrt(s) Gamma(sqrt s)/|s-m^2+i ...|^2 for decay to massless fermions."""
    if running:
        gs = s*width/m
        return gs/(pi*((s-m*m)**2+gs*gs))
    return m*width/(pi*((s-m*m)**2+m*m*width*width))


def _tan_nodes(m, width, s_lo, s_hi, n):
    """Gauss nodes in theta, s=m^2+m Gamma tan(theta); returns s and ds weights."""
    t0, t1 = np.arctan((s_lo-m*m)/(m*width)), np.arctan((s_hi-m*m)/(m*width))
    a, w = leggauss(n); th = t0+(t1-t0)*(a+1)/2; w = w*(t1-t0)/2
    s = m*m+m*width*np.tan(th)
    return s, w*m*width/np.cos(th)**2


def spectral_nodes(m, width, s_lo, s_hi, n, *, window=15.):
    """Composite rule for int ds over [s_lo, s_hi] with a Breit-Wigner peak at m^2.

    Tan-mapped Gauss nodes inside |s-m^2|<=window*m*width, Gauss-Legendre in sqrt(s)
    on the off-peak pieces (n nodes per nonempty piece). Returns s and ds weights.
    """
    a, b = m*m-window*m*width, m*m+window*m*width
    S, Wt = [], []
    for lo, hi in ((s_lo, min(a, s_hi)), (max(b, s_lo), s_hi)):
        if hi > lo:
            x, w = leggauss(n); u0, u1 = sqrt(lo), sqrt(hi)
            u = u0+(u1-u0)*(x+1)/2; S.append(u*u); Wt.append(w*(u1-u0)/2*2*u)
    lo, hi = max(a, s_lo), min(b, s_hi)
    if hi > lo:
        s, w = _tan_nodes(m, width, lo, hi, n); S.append(s); Wt.append(w)
    return np.concatenate(S), np.concatenate(Wt)


def offshell_pair_width(prof, coupling, width_GeV, *, identical, running=True, profile='physical',
                        mu_min_GeV=1., outer=16, inner=12, momentum_nodes=97, order=48, rtol=1e-9):
    """Double spectral (Breit-Wigner) convolution of the distorted-wave pair width.

    Gamma=int ds1 ds2 rho(s1) rho(s2) Gamma_2(M; sqrt s1, sqrt s2), sqrt s1+sqrt s2<M.
    Contracted with a conserved massless-fermion current the unitary-gauge
    propagator numerator reduces to -g, the polarization sum of a vector of
    mass sqrt(s). profile='physical': the leg's normal wave keeps the physical
    barrier m0^2(h^2/h0^2-1) and label k_z, with 2+1 mass^2 k_z^2+s (fermion pair
    approximated by plane waves away from the wall); 'rescaled': barrier s(h^2/h0^2-1).
    outer/inner are nodes per piece of spectral_nodes.
    """
    if profile not in ('rescaled', 'physical'):raise ValueError('profile rescaled or physical')
    m0 = sqrt(coupling)*prof['v_H_GeV']/2; M = prof['M_GeV']
    so, wo = spectral_nodes(m0, width_GeV, mu_min_GeV**2, (M-mu_min_GeV)**2, outer)
    total = 0.; rows = []
    for s1, w1 in zip(so, wo):
        mu1 = sqrt(s1); hi = (M-mu1)**2
        if hi <= mu_min_GeV**2:continue
        si, wi = spectral_nodes(m0, width_GeV, mu_min_GeV**2, hi, inner)
        acc = 0.
        for s2, w2 in zip(si, wi):
            r = vector_pair_widths(prof, coupling, identical=identical, mu1_GeV=mu1, mu2_GeV=sqrt(s2),
                                   prof_mass_GeV=None if profile == 'rescaled' else m0,
                                   momentum_nodes=momentum_nodes, order=order, rtol=rtol)
            acc += w2*breit_wigner_density(s2, m0, width_GeV, running=running)*r['width_GeV']
        total += w1*breit_wigner_density(s1, m0, width_GeV, running=running)*acc
        rows.append({'mu1_GeV': mu1, 'inner_integral_GeV': acc})
    return {'width_GeV': total, 'outer_rows': rows, 'declared_width_GeV': width_GeV, 'vacuum_mass_GeV': m0,
            'running_width': running, 'leg_profile': profile, 'mu_min_GeV': mu_min_GeV,
            'outer_nodes_per_piece': outer, 'inner_nodes_per_piece': inner, 'momentum_nodes': momentum_nodes, 'phase_space_order': order}


def single_offshell_width(prof, coupling, width_GeV, *, identical, mu_min_GeV=1., nodes=48,
                          momentum_nodes=97, order=48, rtol=1e-9):
    """Narrow-width cross-check: one leg exactly on shell, the other with running BW,
    Gamma ~ 2 int ds rho(s) Gamma_2(M; m0, sqrt s) (factor 2: either leg virtual).

    Integrated in u=sqrt(s) with Gauss-Legendre on [mu_min, M-m0] (pole outside the range).
    """
    m0 = sqrt(coupling)*prof['v_H_GeV']/2; M = prof['M_GeV']
    if M-m0 <= mu_min_GeV:return {'width_GeV': 0.}
    a, w = leggauss(nodes); u = mu_min_GeV+(M-m0-mu_min_GeV)*(a+1)/2; w = w*(M-m0-mu_min_GeV)/2
    total = 0.
    for ui, wi in zip(u, w):
        r = vector_pair_widths(prof, coupling, identical=identical, mu1_GeV=m0, mu2_GeV=ui, prof_mass_GeV=m0,
                               momentum_nodes=momentum_nodes, order=order, rtol=rtol)
        total += wi*2*ui*breit_wigner_density(ui*ui, m0, width_GeV)*r['width_GeV']
    return {'width_GeV': 2*total, 'nodes': nodes, 'mu_min_GeV': mu_min_GeV}


# ---------------------------------------------------------------- fermions
def _plane_wave_pair(prof, m, spin_sum, symmetry, order):
    """S/(8M^2) int_{R^2} dk dl |Phi(k+l)|^2/(4 pi^2) spin_sum(K1.K2), Phi the Fourier
    transform of the canonical Higgs profile of the wall mode (GeV^-1/2)."""
    M = prof['M_GeV']; sc = prof['scale_GeV']
    x = prof['x']; wq = prof['quadrature_weights']; ph = prof['psi_H_canonical']
    def Phi(q):
        # dz=dx/scale; full line = 2 x half line for the even profile
        return 2/sc*np.cos(np.multiply.outer(q/sc, x))@(wq*ph)
    a, w = leggauss(order)
    kmax = sqrt((M-m)**2-m*m)
    total = 0.
    for kj, wj in zip(kmax*a, kmax*w):
        lmax = sqrt(max((M-sqrt(kj*kj+m*m))**2-m*m, 0))
        l = lmax*a; wl = lmax*w
        s1 = kj*kj+m*m; s2 = l*l+m*m
        om1 = (M*M+s1-s2)/(2*M); om2 = M-om1; p2 = np.maximum(om1*om1-s1, 0)
        K12 = om1*om2+p2-kj*l
        total += wj*np.sum(wl*Phi(kj+l)**2*spin_sum(K12))
    return float(symmetry*total/(8*M*M*4*pi*pi))


def fermion_pair_width(prof, mass_GeV, colors, *, order=96):
    """Yukawa pair width eta -> f fbar with free bulk Dirac waves (Born).

    Vertex (m_f/v_H) dH psibar psi. Plane waves in z; parallel momentum
    conserved. Gamma=N_c/(8M^2) int_{R^2} dk dl |Y(k+l)|^2/(4 pi^2) 4(K1.K2-m^2),
    Y(q)=(m_f/v_H) int dz dH(z) e^{-iqz}. The wall shift of m_f (relative
    barrier below one percent in h^2) is neglected.
    """
    M = prof['M_GeV']; m = mass_GeV
    if M <= 2*m:return {'width_GeV': 0., 'open': False, 'mass_GeV': m, 'colors': colors}
    y2 = (m/prof['v_H_GeV'])**2
    width = colors*_plane_wave_pair(prof, m, lambda K12: y2*4*(K12-m*m), 1., order)
    return {'width_GeV': width, 'open': True, 'mass_GeV': m, 'colors': colors, 'order': order}


def gluon_pair_width(prof, alpha_s, *, order=96):
    """eta -> g g through the heavy-top operator (alpha_s/(12 pi v_H)) dH G^a G^a (LO).

    Sum over 8 colours and polarizations of |M|^2 = 256 c^2 (K1.K2)^2, identical
    gluons S=1/2. Reduces to Gamma=alpha_s^2 M^3/(72 pi^3 v_H^2) for a bulk Higgs.
    No top-mass form factor and no NLO K factor.
    """
    c = alpha_s/(12*pi*prof['v_H_GeV'])
    width = _plane_wave_pair(prof, 0., lambda K12: 256*c*c*K12*K12, .5, order)
    return {'width_GeV': width, 'alpha_s': alpha_s, 'order': order,
            'scope': 'Heavy-top effective operator at leading order; NLO QCD corrections (K about 1.7-2 for a SM Higgs) not computed.'}


# ---------------------------------------------------------------- longitudinal spectrum
def longitudinal_potentials(prof, mass_GeV):
    """L_T and L_L potentials minus the vacuum mass squared, in GeV^2, on prof['x']."""
    sc = prof['scale_GeV']; mu = mass_GeV/sc
    T = mu*mu*prof['relative_barrier']
    return {'transverse_excess_GeV2': T*sc*sc, 'longitudinal_excess_GeV2': (T+prof['L_extra'])*sc*sc}


def zero_energy_scattering_lengths(prof, mass_GeV, *, rtol=1e-11):
    """Threshold (E=m0^2) solutions per parity: chi ~ c(x-a) beyond the wall.

    Returns scattering lengths a (GeV^-1) and the asymptotic slope of the regular
    solution normalized to unit value (even) or slope (odd) at the centre. A
    threshold resonance would show as slope -> 0 (|a| -> infinity).
    """
    sc = prof['scale_GeV']; x = prof['x']; out = {}
    pots = longitudinal_potentials(prof, mass_GeV)
    for name, key in (('transverse', 'transverse_excess_GeV2'), ('longitudinal', 'longitudinal_excess_GeV2')):
        U = CubicSpline(x, pots[key]/sc/sc)
        for par, y0 in (('even', [1., 0.]), ('odd', [0., 1.])):
            sol = solve_ivp(lambda t, y: [y[1], U(t)*y[0]], (0, x[-1]), y0, method='DOP853', rtol=rtol, atol=rtol*1e-3)
            v, d = sol.y[0, -1], sol.y[1, -1]
            out[f'{name}_{par}'] = {'scattering_length_GeV_inv': (x[-1]-v/d)/sc if d != 0 else None,
                                    'asymptotic_slope': float(d), 'endpoint_value': float(v)}
    return out


def box_spectrum(prof, mass_GeV, *, radius_x, dx, levels=3):
    """Lowest Dirichlet-box levels of L_T and L_L minus m0^2 (GeV^2), per parity.

    Cell-centred grid x_j=(j+1/2)dx on [0,R], Dirichlet at R (odd ghost), Neumann/Dirichlet
    (even/odd) at 0 by ghost reflection (symmetric tridiagonal). Beyond the
    profile domain the excess potential is continued by zero (vacuum).
    """
    sc = prof['scale_GeV']; x0 = prof['x']; pots = longitudinal_potentials(prof, mass_GeV)
    n = int(round(radius_x/dx)); xs = (np.arange(n)+.5)*dx
    out = {}
    for name, key in (('transverse', 'transverse_excess_GeV2'), ('longitudinal', 'longitudinal_excess_GeV2')):
        U = np.zeros(n); inside = xs <= x0[-1]
        U[inside] = CubicSpline(x0, pots[key]/sc/sc)(xs[inside])
        for par, ghost in (('even', 1.), ('odd', -1.)):
            d = 2/dx**2+U; d[0] -= ghost/dx**2; d[-1] += 1/dx**2   # odd ghost at R: Dirichlet exactly at R
            e = -np.ones(n-1)/dx**2
            ev = eigh_tridiagonal(d, e, select='i', select_range=(0, levels-1), eigvals_only=True)
            free_k = (np.arange(levels)+(.5 if par == 'even' else 1.))*pi/radius_x
            out[f'{name}_{par}'] = {'levels_above_threshold_GeV2': (ev*sc*sc).tolist(),
                                    'free_box_levels_GeV2': (free_k**2*sc*sc).tolist()}
    return {'radius_x': radius_x, 'radius_GeV_inv': radius_x/sc, 'dx': dx, **out}


def certified_threshold_statement(profile_receipt, stability_receipt=None):
    """Compose the retuned-wall interval certificate with the exact factorizations.

    Needs from the certificate: an exact whole-line solution with h>0, h>=h0
    everywhere, h>h0 in the interior, and asymptotic vacuum. Then for every
    declared coupling g>0 with m0=g v_H/2:
      <f,L_T f>=int |f'|^2+m^2|f|^2 >= m0^2|f|^2,
      <f,L_L f>=int |f'+a_m f|^2+m^2|f|^2 >= m0^2|f|^2,
    the essential spectrum is [m0^2,inf) (potentials decay to m0^2), so neither
    operator has a discrete eigenvalue, and no bounded threshold solution exists:
    if (L-m0^2)chi=0 with chi bounded then integrating chi(L-m0^2)chi gives
    int|B chi|^2+int (m^2-m0^2)chi^2=0, forcing chi=0 where h>h0, hence chi=0.
    """
    d = json.loads(open(profile_receipt).read()) if isinstance(profile_receipt, str) else profile_receipt
    need = ['P5_Higgs_positive', 'Higgs_at_least_vacuum_everywhere', 'Higgs_strictly_above_vacuum_interior']
    flags = {k: bool(d.get(k)) for k in need}
    if stability_receipt is not None:
        st = json.loads(open(stability_receipt).read()) if isinstance(stability_receipt, str) else stability_receipt
        base = st.get('certificate_160_bits', {}).get('base_certificate_flags', {})
        for k in ['continuous_whole_line_wall_existence_certified', 'whole_line_asymptotic_vacuum_certified']:
            flags[k] = bool(base.get(k))
    ok = all(flags.values())
    return {'certificate_flags_used': flags, 'hypotheses_certified': ok,
            'longitudinal_constrained_spectrum': 'sigma(L_L)=sigma_ess=[m0^2,inf); no localized longitudinal state, no threshold resonance' if ok else 'conditional only',
            'transverse_spectrum': 'sigma(L_T)=[m0^2,inf); no localized state, no threshold resonance' if ok else 'conditional only',
            'consequence': 'The vector-pair threshold of the localized wall mode is exactly 2 m0 for every declared coupling; on-shell VV is closed iff M<2 m0.' if ok else 'conditional only',
            'trust_base': 'Arb interval certificate wall_profile_intervals (retuned quartic), exact symbolic factorization, standard 1D Schrodinger facts (Weyl essential spectrum, asymptotics of zero-energy solutions for exponentially decaying potentials). Not a Lean theorem.'}
