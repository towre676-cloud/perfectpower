"""Complete CP-even scalar basis through degree six on the declared flavor slice.

Physical row fields L,u,d are used; chiral backgrounds are their conjugates.
Fields are scaled by rho=.1. This is a scalar breaking EFT, not a UV matching.
"""
from itertools import combinations, combinations_with_replacement, product
from math import factorial
from pathlib import Path
import json
import numpy as np
import sympy as s
from scipy.optimize import minimize
from develop_valentiner_susy_vacua import adjugate, holomorphic_down_matching
from perfectpower.flavor_mediator import canonical_mediator, mixing_record

ROOT = Path(__file__).resolve().parents[1]
RHO = .1


class Jet:
    """Complex forward derivative in the 54 real field coordinates."""
    def __init__(self, v, g=None):
        self.v = complex(v)
        self.g = np.zeros(54, complex) if g is None else g

    def __add__(self, b):
        b = b if isinstance(b, Jet) else Jet(b)
        return Jet(self.v+b.v, self.g+b.g)

    __radd__ = __add__

    def __mul__(self, b):
        b = b if isinstance(b, Jet) else Jet(b)
        return Jet(self.v*b.v, self.g*b.v+self.v*b.g)

    __rmul__ = __mul__

    def __pow__(self, n):
        if n == 0:
            return Jet(1)
        return Jet(self.v**n, n*self.v**(n-1)*self.g)

    def conjugate(self):
        return Jet(self.v.conjugate(), self.g.conjugate())

    @property
    def real(self):
        return Jet(self.v.real, self.g.real)


def unpack(x):
    z = np.asarray(x[:27])+1j*np.asarray(x[27:])
    return z[:9].reshape(3, 3), z[9:].reshape(6, 3)


def pack(L, phi):
    z = np.concatenate([np.asarray(L).ravel(), np.asarray(phi).ravel()])
    return np.concatenate([z.real, z.imag])


def poly_data():
    rows = json.loads((ROOT/'receipts/m22_interactions/valentiner_invariants.json').read_text())['sextic']['terms']
    terms = [(tuple(r['powers']), complex(s.sympify(r['coefficient']).evalf())) for r in rows]
    tensor = np.zeros((3,)*6, complex)
    for idx in product(range(3), repeat=6):
        p = tuple(idx.count(i) for i in range(3))
        c = next((v for q, v in terms if q == p), 0)
        tensor[idx] = c*__import__('math').prod(factorial(a) for a in p)/factorial(6)
    return terms, tensor


TERMS, TENSOR = poly_data()
EPSILON = np.zeros((3, 3, 3))
for a, b, c in product(range(3), repeat=3):
    if len({a, b, c}) == 3:
        EPSILON[a, b, c] = 1 if (a, b, c) in [(0, 1, 2), (1, 2, 0), (2, 0, 1)] else -1


def source_poly(z):
    value = 0j
    g, h = np.zeros(3, complex), np.zeros((3, 3), complex)
    for p, c in TERMS:
        value += c*np.prod(z**np.array(p))
        for i in range(3):
            q = list(p)
            if q[i]:
                q[i] -= 1
                g[i] += c*p[i]*np.prod(z**np.array(q))
                for j in range(3):
                    if q[j]:
                        r = list(q); r[j] -= 1
                        h[i, j] += c*p[i]*q[j]*np.prod(z**np.array(r))
    return value, g, h


def link_poly(L):
    transformed = TENSOR.conj()
    for axis in range(4):
        transformed = np.moveaxis(np.tensordot(transformed, L, axes=([axis], [1])), -1, axis)
    h = 30*np.tensordot(TENSOR, transformed, axes=(range(4), range(4))).transpose(0, 2, 1, 3).reshape(9, 9)
    transformed = np.moveaxis(np.tensordot(transformed, L, axes=([4], [1])), -1, 4)
    g = 6*np.tensordot(TENSOR, transformed, axes=(range(5), range(5)))
    value = np.sum(g*L)/6
    return value, g.ravel(), h


def base_potential(x):
    L, phi = unpack(x)
    D = np.linalg.det(L); dg = adjugate(L).T.ravel()
    dh = np.einsum('ikm,jln,mn->ijkl', EPSILON, EPSILON, L).reshape(9, 9)
    _, ig, ih = link_poly(L)
    wg = (-32.4+.4*D)*dg+ig
    wh = (-32.4+.4*D)*dh+ih+.4*np.outer(dg, dg)
    v = np.vdot(wg, wg).real
    dz = np.zeros(27, complex); dz[:9] = wh.T@wg.conj()
    for k, p in enumerate(phi):
        f, g, h = source_poly(p)
        v += np.vdot(g, g).real-36*np.vdot(p, p).real-48*f.real
        dz[9+3*k:12+3*k] = h.T@g.conj()-36*p.conj()-24*g
    return float(v), np.concatenate([2*dz.real, -2*dz.imag])


def operator_basis(x, derivatives=False, balanced_only=False, exact_values=False):
    """263 independent real CP-even contractions, excluding a constant.

    SU(3) trace/Gram invariants plus the only new finite-group sextics.
    Every source's C6 charge is imposed separately. Zero-matter/Higgs slice.
    """
    L, phi = unpack(x)
    if derivatives:
        z = np.concatenate([L.ravel(), phi.ravel()])
        jets = []
        for i, v in enumerate(z):
            g = np.zeros(54, complex); g[i] = 1; g[i+27] = 1j
            jets.append(Jet(v, g))
        L, phi = np.array(jets[:9], object).reshape(3, 3), np.array(jets[9:], object).reshape(6, 3)
    dag = lambda M: M.conj().T
    norm = lambda v: sum(a.conjugate()*a for a in v).real
    real = lambda z: z.real
    abs2 = lambda z: real(z.conjugate()*z)
    trace = lambda M: sum(M[i, i] for i in range(3))
    left, right = L@dag(L), dag(L)@L
    S, T, R = real(trace(left)), real(trace(left@left)), real(trace(left@left@left))
    D = sum(sign*L[0, a]*L[1, b]*L[2, c] for (a, b, c), sign in
            [((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1), ((0, 2, 1), -1), ((2, 1, 0), -1), ((1, 0, 2), -1)])
    N = [norm(p) for p in phi]
    Q = [real(phi[i].conj()@(left if i < 3 else right)@phi[i]) for i in range(6)]
    Q2 = [real(phi[i].conj()@((left@left) if i < 3 else (right@right))@phi[i]) for i in range(6)]
    G = {(i, j): phi[i].conj()@phi[j] for i in range(6) for j in range(6) if i//3 == j//3}
    pairs = [(i, j) for i, j in combinations(range(6), 2) if i//3 == j//3]
    rows = []
    def add(degree, name, value): rows.append((degree, name, value))
    add(2, 'S', S)
    for i in range(6): add(2, f'N{i}', N[i])
    if not balanced_only: add(3, 'ReD', real(D))
    add(4, 'S2', S*S); add(4, 'T', T)
    for i in range(6):
        add(4, f'SN{i}', S*N[i]); add(4, f'Q{i}', Q[i])
    for i, j in combinations_with_replacement(range(6), 2): add(4, f'N{i}N{j}', N[i]*N[j])
    for i, j in pairs: add(4, f'B{i}{j}', abs2(G[i, j]))
    if not balanced_only:
        add(5, 'SReD', S*real(D))
        for i in range(6): add(5, f'N{i}ReD', N[i]*real(D))
    add(6, 'S3', S**3); add(6, 'ST', S*T); add(6, 'R', R)
    if not balanced_only: add(6, 'ReD2', real(D*D))
    if not balanced_only and derivatives:
        lv, lg, _ = link_poly(unpack(x)[0]); grad = np.zeros(54, complex)
        grad[:9], grad[27:36] = lg, 1j*lg
        add(6, 'ReI6', Jet(lv, grad).real)
    elif not balanced_only: add(6, 'ReI6', link_poly(L)[0].real)
    for i in range(6):
        add(6, f'S2N{i}', S*S*N[i]); add(6, f'TN{i}', T*N[i])
        add(6, f'SQ{i}', S*Q[i]); add(6, f'Q2{i}', Q2[i])
    for i, j in combinations_with_replacement(range(6), 2): add(6, f'SN{i}N{j}', S*N[i]*N[j])
    for i in range(6):
        for j in range(6): add(6, f'Q{i}N{j}', Q[i]*N[j])
    for i, j in pairs:
        add(6, f'SB{i}{j}', S*abs2(G[i, j]))
        M = left if i < 3 else right
        add(6, f'ReMQ{i}{j}', real((phi[i].conj()@M@phi[j])*G[j, i]))
    for i in range(3):
        for j in range(3, 6): add(6, f'X{i}{j-3}', abs2(phi[i].conj()@L@phi[j]))
    for i, j, k in combinations_with_replacement(range(6), 3): add(6, f'N{i}N{j}N{k}', N[i]*N[j]*N[k])
    for k in range(6):
        for i, j in pairs: add(6, f'N{k}B{i}{j}', N[k]*abs2(G[i, j]))
    for i, j, k in [(0, 1, 2), (3, 4, 5)]: add(6, f'ReG{i}{j}{k}', real(G[i, j]*G[j, k]*G[k, i]))
    if not balanced_only:
        for i in range(6):
            f = sum(c*__import__('functools').reduce(lambda a, b: a*b, (phi[i, k]**p[k] for k in range(3)), 1) for p, c in TERMS)
            add(6, f'ReF{i}', real(f))
    count = 247 if balanced_only else 263
    assert len(rows) == count and len({n for _, n, _ in rows}) == count
    if derivatives:
        return [d for d, _, _ in rows], [n for _, n, _ in rows], np.array([v.v.real for _, _, v in rows]), np.array([v.g.real for _, _, v in rows])
    if exact_values:
        return [d for d, _, _ in rows], [n for _, n, _ in rows], np.array([v for _, _, v in rows], dtype=object)
    return [d for d, _, _ in rows], [n for _, n, _ in rows], np.array([float(v) for _, _, v in rows])


def potential(x, coefficients):
    v, g = base_potential(x)
    _, _, values, gradients = operator_basis(x, True)
    return v+coefficients@values, g+coefficients@gradients


def hessian(x, coefficients, step=2e-5):
    E = np.eye(54)
    H = np.column_stack([(potential(x+step*e, coefficients)[1]-potential(x-step*e, coefficients)[1])/(2*step) for e in E])
    return (H+H.T)/2


def solve(x, coefficients):
    fit = minimize(lambda z: potential(z, coefficients), x, method='L-BFGS-B', jac=True,
                   options={'maxiter': 1200, 'ftol': 5e-15, 'gtol': 2e-7, 'maxls': 35})
    # A Newton refinement checks stationarity independently of the optimizer flag.
    z = fit.x
    for _ in range(4):
        v, g = potential(z, coefficients)
        if np.max(abs(g)) < 2e-8: break
        H = hessian(z, coefficients)
        step = np.linalg.solve(H, -g)
        if np.linalg.norm(step) > .05: break
        z = z+step
    v, g = potential(z, coefficients); H = hessian(z, coefficients)
    return z, {'energy_scaled': float(v), 'stationarity_max': float(np.max(abs(g))),
               'minimum_real_hessian_eigenvalue_scaled': float(np.linalg.eigvalsh(H)[0]),
               'optimizer_success': bool(fit.success), 'iterations': int(fit.nit)}


def quarks(x, weights=None):
    L, phi = unpack(x)
    weights = np.array([.07, .31, .9, .08, .27, .85]) if weights is None else np.asarray(weights)
    Cu = RHO*phi[:3].T@np.diag(weights[:3]); Cd = RHO*phi[3:].T@np.diag(weights[3:])
    Yu = canonical_mediator(.9*np.eye(3), Cu, h=.6)['Y']
    Yd = holomorphic_down_matching((RHO*L).conj(), Cd.conj())['Y']
    return mixing_record(Yu, Yd)


def gram_record(x):
    _, p = unpack(x)
    rows = []
    for phi in (p[:3], p[3:]):
        G = phi.conj()@phi.T
        rows.append({'normalized_overlap_squares': (abs(G)**2/(np.diag(G).real[:, None]*np.diag(G).real[None, :])).tolist(),
                     'smallest_column_singular_value': float(np.linalg.svd(phi.T, compute_uv=False)[-1])})
    return rows
