"""Open-channel scattering and the shape resonance of the canonical three-field wall.

Fluctuations obey -psi''+H(rho)psi=E psi in units of v, with H the Hessian of
wall_fluctuations.potential_and_hessian and E=omega^2/v^2. The reflection
D=diag(-1,1,1) composed with rho->-rho is a symmetry. Each parity sector is a
half-line problem: 'translation' has phi Neumann and S,h Dirichlet at rho=0;
'opposite' has phi Dirichlet and S,h Neumann.

Johnson's multichannel log-derivative propagator keeps every open and closed
channel. Asymptotic eigenchannels come from the exact vacuum Hessian. Open
channels are flux-normalised. Poles are zeros of det(Y-iQ), where each closed
channel has q=i*sqrt(mu-E) and each open channel has the principal
q=sqrt(E-mu). Continuing that principal branch to Im E<0 reaches the
unphysical sheet of the open channels. Everything here is floating point.
Step halving, independent matching radii and box lengths are error controls,
not certificates.
"""
from math import pi, sqrt
import numpy as np
from scipy.integrate import solve_ivp
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh

SECTORS = ('translation', 'opposite')


def _constants(wall):
    model, bath = wall['model'], wall['bath']
    a = model.current_g_GeV/model.v_GeV
    m = model.heavy_mass_GeV/model.v_GeV
    h0 = bath.v_GeV/model.v_GeV
    return model.lam, a, m, h0, bath.portal, bath.lam


def hessian(wall, rho, *, coupling_scale=1., decouple=False):
    """Vectorised Hessian on an array of rho >= 0; exact vacuum beyond the BVP box.

    coupling_scale multiplies only the phi-h entries of the fluctuation
    operator (background unchanged). decouple=True sets them to zero.
    """
    lam, a, m, h0, kap, lH = _constants(wall)
    rho = np.asarray(rho, float)
    z = np.empty((3, rho.size))
    inside = rho <= wall['L']
    z[:, inside] = wall['solution'].sol(rho[inside])[:3]
    z[:, ~inside] = np.array([[1.], [-a/m**2], [h0]])
    u, y, h = z
    b = kap/lH
    rs = y + a*u*u/m**2
    rh = h*h - h0*h0 + b*(u*u - 1)
    H = np.zeros((rho.size, 3, 3))
    H[:, 0, 0] = lam*(3*u*u - 1) + 2*a*rs + 4*a*a*u*u/m**2 + kap*rh + 2*kap*b*u*u
    H[:, 0, 1] = H[:, 1, 0] = 2*a*u
    H[:, 1, 1] = m*m
    off = 0. if decouple else coupling_scale*2*kap*u*h
    H[:, 0, 2] = H[:, 2, 0] = off
    H[:, 2, 2] = lH*(rh + 2*h*h)
    return H


def vacuum_channels(wall, *, coupling_scale=1., decouple=False):
    """Thresholds mu_j and orthonormal eigenchannels of the rho->+inf Hessian."""
    H = hessian(wall, [wall['L']*2], coupling_scale=coupling_scale, decouple=decouple)[0]
    mu, V = np.linalg.eigh(H)
    # Fixed orientation: largest component of each eigenvector positive.
    V = V*np.sign(V[np.argmax(abs(V), axis=0), range(3)])
    return mu, V


def channel_momenta(E, mu):
    """Open channels: principal sqrt(E-mu). Closed channels: i*sqrt(mu-E).

    Openness is decided by Re E > mu, so the principal branch of an open
    channel continues to its unphysical sheet when Im E < 0.
    """
    E = np.asarray(E, complex)[..., None]
    open_ = E.real > mu
    return np.where(open_, np.sqrt(E - mu + 0j), 1j*np.sqrt(mu - E + 0j)), open_


def _johnson(Y0, rho, Hgrid, E):
    """Johnson (1973) log-derivative propagation on a uniform grid.

    Y=psi' psi^{-1} for psi''=W psi, W=H-E, so Y'=W-Y^2. Free steps map
    Y->(1+hY)^{-1}Y; W enters with Simpson weights 1,4,2,...,4,1, odd points
    using the Numerov-corrected (1-h^2 W/6)^{-1} W. Global error O(h^4).
    """
    n = len(rho) - 1
    if n % 2:
        raise ValueError('even number of Johnson steps required')
    h = rho[1] - rho[0]
    I = np.eye(3)
    nE = len(E)
    y = Y0 + (h/3)*(Hgrid[0][None] - E[:, None, None]*I)
    for j in range(1, n + 1):
        W = Hgrid[j][None] - E[:, None, None]*I
        if j % 2:
            U = np.linalg.solve(I - (h*h/6)*W, W)
            w = 4.
        else:
            U, w = W, (1. if j == n else 2.)
        y = np.linalg.solve(I + h*y, y) + (h/3)*w*U
    return y


def _reference_tail(Y, rho, wall, E, coupling_scale, decouple):
    """Exact vacuum-reference drift with Strang kicks of the small remainder.

    In the vacuum eigenchannel basis W=diag(mu-E)+dW(rho); dW is the wall's
    exponentially small tail (dominated by the Yukawa tail of the radial
    Higgs). Each step solves the constant reference exactly,
    Y->(pS+CY)(C+(S/p)Y)^{-1} with C=cosh(ph), S=sinh(ph), p^2=mu-E, which is
    even in p, so no branch choice enters. Works for either sign of h.
    """
    mu, V = vacuum_channels(wall, coupling_scale=coupling_scale, decouple=decouple)
    h = rho[1] - rho[0]
    p = np.sqrt(mu[None, :] - E[:, None] + 0j)
    if np.max(abs(p.real*h)) > 300:
        raise ValueError('reference step too long for cosh/sinh in double precision')
    C = np.cosh(p*h)
    pS = p*np.sinh(p*h)
    Sp = np.where(abs(p*h) > 1e-8, np.sinh(p*h)/np.where(p == 0, 1, p), h)
    dW = np.einsum('ji,njk,kl->nil', V, hessian(wall, rho, coupling_scale=coupling_scale, decouple=decouple), V) - np.diag(mu)
    Yc = np.einsum('ji,ejk,kl->eil', V, Y, V)
    I = np.eye(3)
    for j in range(len(rho) - 1):
        Yc = Yc + (h/2)*dW[j]
        Yc = np.linalg.solve((C[:, :, None]*I + Sp[:, :, None]*Yc).transpose(0, 2, 1),
                             (pS[:, :, None]*I + C[:, :, None]*Yc).transpose(0, 2, 1)).transpose(0, 2, 1)
        Yc = Yc + (h/2)*dW[j + 1]
    return np.einsum('ij,ejk,lk->eil', V, Yc, V)


def log_derivative(wall, parity, energies, *, R=None, core=80., h_core=.004,
                   h_tail=.2, coupling_scale=1., decouple=False, tail='reference'):
    """Batched Y(R) for the regular half-line solutions of one parity sector."""
    if parity not in SECTORS:
        raise ValueError('unknown reflection sector')
    E = np.atleast_1d(np.asarray(energies, complex))
    R = wall['L'] if R is None else float(R)
    big = 1e30
    diag = [0., big, big] if parity == 'translation' else [big, 0., 0.]
    Y = np.broadcast_to(np.diag(diag).astype(complex), (len(E), 3, 3)).copy()
    for j, rho in enumerate(_segments(0., R, core, h_core, h_tail)):
        if j and tail == 'reference':
            Y = _reference_tail(Y, rho, wall, E, coupling_scale, decouple)
        else:
            Y = _johnson(Y, rho, hessian(wall, rho, coupling_scale=coupling_scale, decouple=decouple), E)
    return E, Y


def jost_matrix(wall, parity, energies, **kw):
    """det(Y_c - iQ) and the channel data; zeros are bound states or resonances."""
    E, Y = log_derivative(wall, parity, energies, **kw)
    mu, V = vacuum_channels(wall, coupling_scale=kw.get('coupling_scale', 1.),
                            decouple=kw.get('decouple', False))
    Yc = np.einsum('ji,ejk,kl->eil', V, Y, V)
    q, open_ = channel_momenta(E, mu)
    J = Yc - 1j*q[:, :, None]*np.eye(3)
    return {'E': E, 'Yc': Yc, 'q': q, 'open': open_, 'J': J,
            'det': np.linalg.det(J), 'thresholds': mu, 'channels': V}


def s_matrix(wall, parity, energies, *, R=None, **kw):
    """Open-channel sector S, psi_j=(A_j e^{-iq rho}+B_j e^{iq rho})/sqrt(q_j), S=-B/A.

    Free Dirichlet gives S=1 and free Neumann gives S=-1, i.e. S=exp(2i delta)
    for psi ~ sin(q rho+delta).
    """
    d = jost_matrix(wall, parity, energies, R=R, **kw)
    Rm = wall['L'] if R is None else float(R)
    out = []
    for J, Yc, q, o in zip(d['J'], d['Yc'], d['q'], d['open']):
        M = np.linalg.solve(J, Yc + 1j*q[:, None]*np.eye(3))
        idx = np.flatnonzero(o)
        qo = q[idx]
        # S=(I+)^{-1} M I-, I+-=diag(e^{+-iqR}/sqrt(q)): flux normalisation.
        left, right = np.sqrt(qo)*np.exp(-1j*qo*Rm), np.exp(-1j*qo*Rm)/np.sqrt(qo)
        S = left[:, None]*M[np.ix_(idx, idx)]*right[None, :]
        out.append({'open_channels': idx.tolist(), 'S': S,
                    'unitarity_defect': float(np.linalg.norm(S.conj().T@S - np.eye(len(idx)), 2)) if len(idx) else 0.})
    return d, out


def full_line(S_translation, S_opposite):
    """Unitary full-line S from parity sectors; returns reflection and transmission.

    Right-hand channels use e_j and left-hand channels use D e_j. The
    'opposite' sector is P=+1 and 'translation' is P=-1 for P psi(rho)=D psi(-rho).
    """
    Sp, Sm = np.asarray(S_opposite), np.asarray(S_translation)
    r = -(Sp + Sm)/2
    t = (Sm - Sp)/2
    full = np.block([[r, t], [t, r]])
    return {'reflection': r, 'transmission': t, 'S': full,
            'unitarity_defect': float(np.linalg.norm(full.conj().T@full - np.eye(len(full)), 2))}


def _segments(lo, hi, core, h_core, h_tail):
    """Uniform Johnson segments: fine on [0,core], coarse beyond."""
    out = []
    for a, b, step in ((0., min(core, hi), h_core), (min(core, hi), hi, h_tail)):
        if b > a:
            n = 2*int(np.ceil((b - a)/(2*step)))
            out.append(np.linspace(a, b, n + 1))
    return out


def jost_function(wall, parity, energies, *, R=None, core=80., h_core=.004,
                  h_tail=.2, coupling_scale=1., decouple=False, tail='reference'):
    """F(E)=det(P_D X+P_N X')/det(X'-iX) at rho=0, X the inward propagation of outgoing/decaying solutions.

    Y_in(R)=V diag(iq) V^T selects e^{iq rho} in every channel, i.e. decaying
    closed channels and outgoing open ones on the declared sheet. A zero of F
    means some such solution meets the parity condition at rho=0: a bound
    state (real E below every threshold) or a resonance pole. Unlike
    det(Y_out-iQ) at large R, no exponentially squeezed zero/pole pair occurs.
    """
    if parity not in SECTORS:
        raise ValueError('unknown reflection sector')
    E = np.atleast_1d(np.asarray(energies, complex))
    R = wall['L'] if R is None else float(R)
    mu, V = vacuum_channels(wall, coupling_scale=coupling_scale, decouple=decouple)
    q, open_ = channel_momenta(E, mu)
    Y = np.einsum('ij,ej,kj->eik', V, 1j*q, V)
    segments = _segments(0., R, core, h_core, h_tail)
    for j in reversed(range(len(segments))):
        rho = segments[j][::-1]
        if j and tail == 'reference':
            Y = _reference_tail(Y, rho, wall, E, coupling_scale, decouple)
        else:
            Y = _johnson(Y, rho, hessian(wall, rho, coupling_scale=coupling_scale, decouple=decouple), E)
    # det(P_D X+P_N X')/det(X'-iX) for Y=X'X^{-1}: regular where X is singular,
    # and neither Dirichlet nor Neumann zeros are divided away.
    M = np.linalg.inv(Y - 1j*np.eye(3))
    neumann = [0] if parity == 'translation' else [1, 2]
    B = M.copy()
    B[:, neumann, :] = (np.eye(3) + 1j*M)[:, neumann, :]
    return E, np.linalg.det(B), Y


def find_pole(wall, parity, guess, *, scale=1e-6, iterations=14, tol=1e-15, **kw):
    """Complex Newton on the inward Jost function with a batched stencil."""
    E0 = complex(guess)
    history = []
    for _ in range(iterations):
        d = jost_function(wall, parity, [E0, E0 + scale, E0 - scale, E0 + 1j*scale, E0 - 1j*scale], **kw)[1]
        slope = ((d[1] - d[2])/(2*scale) + (d[3] - d[4])/(2j*scale))/2
        step = -d[0]/slope
        history.append({'E': [E0.real, E0.imag], 'F_abs': float(abs(d[0])), 'step_abs': float(abs(step))})
        E0 += step
        scale = max(min(scale, abs(step)), 1e-12*max(1e-3, abs(E0)))
        if abs(step) < tol*max(1e-3, abs(E0)):
            break
    return E0, history


def _fem_matrices(edges, values_at, nfields, dirichlet_left):
    """Quadratic conforming elements for -psi''+H psi; Dirichlet at the right end."""
    x = np.sort(np.r_[edges, (edges[:-1] + edges[1:])/2])
    n = len(x)
    gauss, weights = np.polynomial.legendre.leggauss(5)
    rr, cc, kk, mm = [], [], [], []
    I = np.eye(nfields)
    for j in range(len(edges) - 1):
        d = edges[j + 1] - edges[j]
        K = np.kron(np.array([[7, -8, 1], [-8, 16, -8], [1, -8, 7]])/(3*d), I)
        M = np.kron(d*np.array([[4, 2, -1], [2, 16, 2], [-1, 2, 4]])/30, I)
        pts = edges[j] + (gauss + 1)*d/2
        Hq = values_at(pts)
        for s, w, Hs in zip(gauss, weights, Hq):
            N = np.array([s*(s - 1)/2, 1 - s*s, s*(s + 1)/2])
            K += w*d/2*np.kron(np.outer(N, N), Hs)
        ids = np.arange(2*nfields*j, 2*nfields*j + 3*nfields)
        rr.extend(np.repeat(ids, 3*nfields)); cc.extend(np.tile(ids, 3*nfields))
        kk.extend(K.ravel()); mm.extend(M.ravel())
    N = nfields*n
    K = coo_matrix((kk, (rr, cc)), shape=(N, N)).tocsr()
    M = coo_matrix((mm, (rr, cc)), shape=(N, N)).tocsr()
    excluded = set(range(N - nfields, N)) | set(dirichlet_left)
    keep = np.array([j for j in range(N) if j not in excluded])
    return x, K[keep][:, keep], M[keep][:, keep], keep


def shape_bound_state(wall, *, radius=160., spacing=.02, guess=.15):
    """Opposite-sector bound state of the (phi,S) block with phi-h coupling removed.

    Returns its eigenvalue, nodal values and an exact quadratic-element
    evaluator normalised on the half line.
    """
    k = wall['k']
    edges = np.unique(np.r_[np.arange(0., 30/k, spacing), np.linspace(30/k, radius, 400)])
    blocks = lambda r: hessian(wall, r, decouple=True)[:, :2, :2]
    x, K, M, keep = _fem_matrices(edges, blocks, 2, dirichlet_left=[0])
    vals, vecs = eigsh(K, k=1, M=M, sigma=guess, which='LM', tol=1e-13, v0=np.cos(.37*np.arange(K.shape[0])) + .1)
    full = np.zeros(2*len(x)); full[keep] = vecs[:, 0]
    norm = sqrt(float(vecs[:, 0]@(M@vecs[:, 0])))
    full /= norm
    nodes = full.reshape(-1, 2)
    if nodes[np.argmax(abs(nodes[:, 0])), 0] < 0:
        nodes = -nodes
    return {'E': float(vals[0]), 'edges': edges, 'x': x, 'nodes': nodes}


def _element_quadrature(state, order=6):
    """Points, weights and the phi component of the bound state on each element."""
    edges, nodes = state['edges'], state['nodes']
    g, w = np.polynomial.legendre.leggauss(order)
    pts, wts, phi = [], [], []
    for j in range(len(edges) - 1):
        d = edges[j + 1] - edges[j]
        N = np.array([g*(g - 1)/2, 1 - g*g, g*(g + 1)/2])
        pts.append(edges[j] + (g + 1)*d/2); wts.append(w*d/2)
        phi.append(nodes[2*j:2*j + 3, 0]@N)
    return np.concatenate(pts), np.concatenate(wts), np.concatenate(phi)


def higgs_green_self_energy(wall, state, E=None, *, coupling_scale=1., rtol=1e-12):
    """Second-order Feshbach self-energy of the shape state through the even Higgs channel.

    Sigma(E)=-<b|W G^+_h(E) W|b>, G^+(r,r')=-f_reg(r<) f_out(r>)/Wr with
    Wr=f_reg f_out'-f_reg' f_out. f_reg is Neumann at 0; f_out is exactly
    e^{iq rho} at the box edge, beyond which the Hessian is the exact vacuum.
    The golden rule uses the half-line delta(E)-normalised standing wave
    f_reg/(A sqrt(pi q)), A its asymptotic amplitude, and is an independent
    check of -2 Im Sigma.
    """
    E = state['E'] if E is None else E
    lam, a, m, h0, kap, lH = _constants(wall)
    L = wall['L']
    pts, wts, phi = _element_quadrature(state)
    g = coupling_scale*2*kap*hessian_background(wall, pts)*phi*wts
    V = lambda r: hessian(wall, np.atleast_1d(r), decouple=True)[0, 2, 2]
    mu = V(2*L)
    q = sqrt(E - mu)
    rhs = lambda r, z: np.array([z[1], (V(r) - E)*z[0]])
    reg = solve_ivp(rhs, (0, L), np.array([1., 0.]), method='DOP853', rtol=rtol, atol=1e-15, dense_output=True)
    out = solve_ivp(rhs, (L, 0), np.array([np.exp(1j*q*L), 1j*q*np.exp(1j*q*L)]), method='DOP853', rtol=rtol, atol=1e-15, dense_output=True)
    order = np.argsort(pts)
    pts, g = pts[order], g[order]
    fr, fo = reg.sol(pts), out.sol(pts)
    wr = fr[0]*fo[1] - fr[1]*fo[0]
    Wr = complex(np.mean(wr))
    gr, go = g*fr[0], g*fo[0]
    inner = np.cumsum(gr) - gr/2
    Sigma = 2*np.sum(go*inner)/Wr
    end = reg.y[:, -1]
    amplitude2 = end[0]**2 + (end[1]/q)**2
    overlap = float(np.sum(gr))
    golden = 2*overlap**2/(amplitude2*q)
    return {'E': E, 'Sigma': complex(Sigma), 'golden_rule_Gamma_E': golden,
            'standing_wave_overlap': overlap, 'q_Higgs': q, 'Higgs_threshold': mu,
            'wronskian_relative_spread': float(np.ptp(abs(wr))/abs(Wr)),
            'Higgs_phase_shift_even': float(np.arctan2(-end[1]/q, end[0]) - q*L)}


def hessian_background(wall, rho):
    """u*h along rho, the profile factor of the phi-h coupling 2*kappa*u*h."""
    rho = np.asarray(rho, float)
    z = np.empty((3, rho.size))
    inside = rho <= wall['L']
    z[:, inside] = wall['solution'].sol(rho[inside])[:3]
    lam, a, m, h0, kap, lH = _constants(wall)
    z[:, ~inside] = np.array([[1.], [-a/m**2], [h0]])
    return z[0]*z[2]


def analytic_shape_width(wall):
    """Leading closed form for the single-Higgs radiative width of the shape mode.

    Pure Poschl-Teller shape state sqrt(3k) sech(k rho) tanh(k rho) on the half
    line, coupling 2 kappa eta0 tanh(k rho), free Neumann Higgs wave
    cos(q rho) and q^2=3k^2-m_h^2, nu=q/k. With
    int sech^3(x) e^{i nu x} dx=(pi/2)(1+nu^2) sech(pi nu/2),
    Gamma_E=3 pi^2 kappa^2 eta0^2 (nu^2-1)^2 sech^2(pi nu/2)/(2 k q).
    Neglected: mediator mixing O(alpha^2/mu^2), the O(kappa) Higgs profile
    shift and its Yukawa tail, and O(kappa^4). In v-units, E=omega^2/v^2.
    """
    lam, a, m, h0, kap, lH = _constants(wall)
    k = sqrt(lam/2)
    mh2 = 2*lH*h0*h0
    q = sqrt(3*k*k - mh2)
    nu = q/k
    overlap = -2*kap*h0*sqrt(3*k)/k*(pi/4)*(nu*nu - 1)/np.cosh(pi*nu/2)
    return {'Gamma_E': 3*pi**2*kap**2*h0**2*(nu*nu - 1)**2/np.cosh(pi*nu/2)**2/(2*k*q),
            'standing_wave_overlap': overlap, 'nu': nu, 'q_Higgs': q, 'E_shape': 3*k*k,
            'massless_Higgs_limit_Gamma_omega_over_v': 2*sqrt(2)*pi**2*kap**2*h0**2/lam**1.5/np.cosh(sqrt(3)*pi/2)**2}


def physical_width(E_r, Gamma_E, v_GeV):
    """Convert a pole E_r-i Gamma_E/2 in units of v^2 to omega and the energy decay rate."""
    from .dimensionful_walls import HBAR_GEV_S
    omega = sqrt(E_r)*v_GeV
    gamma = Gamma_E/(2*sqrt(E_r))*v_GeV
    return {'omega_GeV': omega, 'Gamma_GeV': gamma, 'lifetime_s': HBAR_GEV_S/gamma,
            'quality_factor': omega/gamma}
