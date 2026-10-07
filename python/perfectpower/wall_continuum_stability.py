"""Continuum linear stability of the coupled wall from exact identities.

Theorem (stated in the monograph). Let Phi=(u,y,h) be a static solution of
the three-field equations with u odd and y, h even, satisfying on rho>0:
  (P1) 0<u<1,  (P2) u'>0,  (P3) y'<0,  (P4) h'<0,  (P5) h>0.
Then the Hessian operator L=-d^2+H(rho) on L^2(R)^3 satisfies L>=0, and its
kernel is span(Phi'). Moreover h>=h0 everywhere (Lemma, from (P1) and the
maximum principle), and the angular-Higgs/gauge quadratic form is
nonnegative for any h>0.

Translation sector (u' even; y', h' odd): with psi=(f_u w_u,-f_S w_S,-f_h w_h)
and w=(u',-y',-h')>0 on rho>0, L w=0 gives
  <psi,L psi>=sum_i int w_i^2 f_i'^2+(1/2)sum_{i!=j}|H_ij| w_i w_j (f_i-f_j)^2,
because the sign-flipped off-diagonal entries -2 alpha u and -2 kappa u h
are <=0 (a cooperative system).
Opposite sector: eliminating S and h with (-d^2+mu^2)^{-1}<=mu^{-2} and
H_hh>=2 lam_H eta0^2-kappa=m_h^2-kappa (from h>=h0, u^2<=1) leaves
-d^2+U-nu, where U=lam(3u^2-1)+2 alpha r_S+kappa r_H+2 kappa beta u^2 and
nu=4 kappa^2 u^2 h^2/(m_h^2-kappa). The field equation gives exactly
(-d^2+U)u=2(lam+kappa beta)u^3, so u>0 is a strict supersolution.

This module checks (P1)-(P5) on the numerical profile and evaluates the
identities numerically. The sign checks are floating-point; the theorem
itself is exact algebra plus standard ground-state (Allegretto-Piepenbrink)
arguments.
"""
import numpy as np
from .wall_scattering import _constants, hessian


def profile_and_derivatives(wall, rho):
    z = wall['solution'].sol(np.asarray(rho, float))
    lam, a, m, h0, kap, lH = _constants(wall)
    u, y, h, p, q, r = z
    b = kap/lH
    rs = y + a*u*u/m**2
    rh = h*h - h0*h0 + b*(u*u - 1)
    upp = lam*u*(u*u - 1) + 2*a*u*rs + kap*u*rh
    ypp = m*m*rs
    hpp = lH*h*rh
    return {'u': u, 'y': y, 'h': h, 'du': p, 'dy': q, 'dh': r, 'ddu': upp, 'ddy': ypp, 'ddh': hpp, 'rs': rs, 'rh': rh}


def tail_certificate(wall, R_t=30.):
    """Signs of (P1)-(P4) for rho>=R_t from the decaying vacuum eigenmodes.

    delta Phi=sum_j e_j d_j e^{-sqrt(mu_j)(rho-R_t)} up to quadratic terms. Each
    component of delta Phi and Phi' is then an exponential sum, whose number
    of positive zeros is at most the number of sign changes of its
    coefficients ordered by decay rate. Equal signs (or one change with
    matching values at x=0 and x->infinity) exclude a sign change on
    [R_t, infinity). The Higgs-mode coefficient is evaluated from its exact
    eigenvector, so components far below double precision keep their sign.
    """
    from .wall_scattering import vacuum_channels
    lam, a, m, h0, kap, lH = _constants(wall)
    mu, V = vacuum_channels(wall)
    z = wall['solution'].sol(R_t)
    vac = np.array([1., -a/m**2, h0])
    d = V.T@(z[:3] - vac)
    dprime = V.T@z[3:]
    s = np.sqrt(mu)
    consistency = (dprime + s*d)/np.maximum(abs(s*d), 1e-300)

    def verdict(coef, want):
        order = np.argsort(s)
        c = coef[order]
        c = c[abs(c) > 0]
        changes = int(np.sum(np.sign(c[:-1]) != np.sign(c[1:])))
        at0 = np.sign(np.sum(coef)); atinf = np.sign(c[0]) if c.size else 0
        ok = (changes == 0 and atinf == want) or (changes == 1 and at0 == want and atinf == want)
        return {'coefficients_by_decay': c.tolist(), 'sign_changes': changes, 'holds': bool(ok)}
    # u-1<0, u'>0, y'<0, h'<0, h-h0>0 on [R_t, inf).
    rows = {'u_minus_1_negative': verdict(V[0]*d, -1), 'du_positive': verdict(-s*V[0]*d, 1),
            'dy_negative': verdict(-s*V[1]*d, -1), 'dh_negative': verdict(-s*V[2]*d, -1),
            'h_minus_h0_positive': verdict(V[2]*d, 1)}
    if a == 0:
        rows.pop('dy_negative')
    return {'R_t': R_t, 'mode_amplitudes': d.tolist(), 'decay_rates': s.tolist(),
            'decaying_mode_consistency': consistency.tolist(), 'rows': rows,
            'all_hold': all(r['holds'] for r in rows.values())}


def sign_certificate(wall, *, n=200001, R_t=30.):
    """Margins of (P1)-(P5) on (0, L], plus the leading slopes at rho=0.

    Near rho=0 the odd quantities vanish linearly; their slopes u'(0)>0,
    -y''(0)>0, -h''(0)>0 must be strictly positive.
    """
    rho = np.r_[np.geomspace(1e-6, 1., 2000), np.linspace(1., R_t, n)]
    d = profile_and_derivatives(wall, rho)
    lam, a, m, h0, kap, lH = _constants(wall)
    z0 = profile_and_derivatives(wall, [0.])
    out = {'P1_min_u_over_rho_near0': float(np.min(d['u'][:2000]/rho[:2000])),
           'P1_max_u': float(np.max(d['u'])), 'P1_min_one_minus_u': float(np.min(1 - d['u'])),
           'P2_min_du': float(np.min(d['du'])),
           'P3_max_dy': float(np.max(d['dy'])), 'P3_max_dy_over_rho_near0': float(np.max(d['dy'][:2000]/rho[:2000])),
           'P4_max_dh': float(np.max(d['dh'])), 'P4_max_dh_over_rho_near0': float(np.max(d['dh'][:2000]/rho[:2000])),
           'P5_min_h': float(np.min(d['h'])),
           'h_minus_h0_min': float(np.min(d['h'] - h0)),
           'slopes_at_0': {'du': float(z0['du'][0]), 'minus_ddy': float(-z0['ddy'][0]), 'minus_ddh': float(-z0['ddh'][0])}}
    out['sampled_range'] = [0., R_t]
    # With g=0 the mediator decouples exactly (y'=0, H_uS=0); its block is mu^2>0 and (P3) is not needed.
    out['mediator_decoupled'] = a == 0
    p3 = a == 0 or (out['P3_max_dy'] < 0 and out['slopes_at_0']['minus_ddy'] > 0)
    out['all_strict'] = bool(out['P1_min_u_over_rho_near0'] > 0 and out['P1_min_one_minus_u'] > 0 and out['P2_min_du'] > 0
                             and p3 and out['P4_max_dh'] < 0 and out['P5_min_h'] > 0
                             and out['slopes_at_0']['du'] > 0 and out['slopes_at_0']['minus_ddh'] > 0)
    return out


def translation_identity(wall, f, *, n=40001, R=60.):
    """Both sides of the cooperative ground-state identity for psi built from f=(f_u,f_S,f_h).

    psi_u=f_u u', psi_S=f_S y', psi_h=f_h h' (so the flipped weights are -y', -h').
    Returns <psi,L psi> by direct quadrature and the right-hand side.
    """
    rho = np.linspace(0, R, n)
    d = profile_and_derivatives(wall, rho)
    H = hessian(wall, rho)
    fu, fs, fh = (g(rho) for g in f)
    dfu, dfs, dfh = (np.gradient(g, rho) for g in (fu, fs, fh))
    psi = np.array([fu*d['du'], fs*d['dy'], fh*d['dh']])
    dpsi = np.array([dfu*d['du'] + fu*d['ddu'], dfs*d['dy'] + fs*d['ddy'], dfh*d['dh'] + fh*d['ddh']])
    lhs = np.trapezoid(np.sum(dpsi**2, 0) + np.einsum('in,nij,jn->n', psi, H, psi), rho)
    # Flipped operator D L D, D=diag(1,-1,-1): w=D Phi'>0 and D psi=F*w gives F=(f_u,f_S,f_h).
    w = np.array([d['du'], -d['dy'], -d['dh']])
    F = np.array([fu, fs, fh])
    dF = np.array([dfu, dfs, dfh])
    rhs = np.trapezoid(np.sum(w**2*dF**2, 0), rho)
    for i, j in ((0, 1), (0, 2)):
        rhs += np.trapezoid(abs(H[:, i, j])*w[i]*w[j]*(F[i] - F[j])**2, rho)
    return {'lhs': float(lhs), 'rhs': float(rhs)}


def opposite_supersolution(wall, *, n=200001):
    """Residual of (-d^2+U)u=2(lam+kappa beta)u^3 and the Schur margin."""
    lam, a, m, h0, kap, lH = _constants(wall)
    b = kap/lH
    rho = np.linspace(1e-3, 80., n)
    d = profile_and_derivatives(wall, rho)
    u = d['u']
    U = lam*(3*u*u - 1) + 2*a*d['rs'] + kap*d['rh'] + 2*kap*b*u*u
    lhs = -d['ddu'] + U*u
    exact = 2*(lam + kap*b)*u**3
    mh2 = 2*lH*h0*h0
    nu_max = float(np.max(4*kap**2*d['h']**2/(mh2 - kap)))
    return {'max_relative_residual': float(np.max(abs(lhs - exact)/np.maximum(abs(exact), 1e-300))),
            'supersolution_coefficient': 2*(lam + kap*b), 'nu_over_u2_max': nu_max,
            'margin': 2*(lam + kap*b) - nu_max,
            'Higgs_block_floor': mh2 - kap, 'mediator_block_floor': m*m}


def goldstone_factorization(wall, *, n=20001):
    """lam_H r_H equals h''/h, so -d^2+lam_H r_H=(-d-h'/h)(d-h'/h)>=0."""
    lam, a, m, h0, kap, lH = _constants(wall)
    rho = np.linspace(0, wall['L']*.99, n)
    d = profile_and_derivatives(wall, rho)
    return {'max_abs_difference': float(np.max(abs(lH*d['rh'] - d['ddh']/d['h']))),
            'min_Goldstone_potential': float(np.min(lH*d['rh'])),
            'max_Goldstone_potential': float(np.max(lH*d['rh']))}


def maximum_principle_lemma(wall):
    """h>=h0: at an interior minimum h''>=0 forces r_H>=0, i.e. h^2>=h0^2+beta(1-u^2)>=h0^2."""
    lam, a, m, h0, kap, lH = _constants(wall)
    rho = np.linspace(0, wall['L'], 200001)
    d = profile_and_derivatives(wall, rho)
    return {'min_h_minus_h0': float(np.min(d['h'] - h0)), 'argmin_rho': float(rho[np.argmin(d['h'])])}
