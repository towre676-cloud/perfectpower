"""Source-derived scalar RG rays; CKM data never enters candidate discovery.

Pure scalar one-loop running in an exchange-symmetric nine-operator algebra.
This is a reduction of the declared model, not full gauge/Yukawa matching.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

INDICES = (10, 11, 22, 23, 39, 48, 49, 50, 51)
NAMES = ('radial', 'finite_self', 'norm_cross', 'ordinary_cross',
         'finite8_cross', 'finite9_cross', 'CP_pair5_cross')
SLOTS = {10: 0, 22: 0, 11: 1, 23: 1, 39: 2, 48: 3, 49: 4, 50: 5, 51: 6}


def source_table(root=None):
    root = Path(root) if root else Path(__file__).resolve().parents[2]
    path = root / 'receipts/m22_interactions/nonet_higgs_exact_loop_algebra.json'
    raw = path.read_bytes()
    data = json.loads(raw)
    if not data['exact_tensor_proof']['exact_zero_residual_for_every_product']:
        raise ValueError('exact source tensor proof required')
    return data['symmetric_products'], hashlib.sha256(raw).hexdigest()


def restrict(table):
    """Restrict the actual tensor and independently check exchange closure."""
    rows = [{} for _ in range(61)]
    for k, i, j, c in table:
        if i not in SLOTS or j not in SLOTS:
            continue
        mon = tuple(sorted((SLOTS[i], SLOTS[j])))
        rows[k][mon] = rows[k].get(mon, Q(0)) + Q(c) * (1 if i == j else 2)
    rows = [{m: c for m, c in row.items() if c} for row in rows]
    if any(row for k, row in enumerate(rows) if k not in SLOTS):
        raise ValueError('restriction leaks into omitted operators')
    if rows[10] != rows[22] or rows[11] != rows[23]:
        raise ValueError('exchange restriction is not closed')
    return [rows[k] for k in (10, 11, 39, 48, 49, 50, 51)]


def beta(rows, vector):
    if len(rows) != 7 or len(vector) != 7:
        raise ValueError('seven-dimensional exchange-symmetric model required')
    return [sum(c * vector[i] * vector[j] for (i, j), c in row.items())
            for row in rows]


def verify_ray(rows, vector):
    v = [Q(x) for x in vector]
    return any(v) and beta(rows, v) == v


def coercive_lower_bound(vector):
    """Sufficient global bound, using orthogonal finite-channel projectors.

    For traceless Hermitian 3x3 A, ||(A^2)_0||^2=||A||^4/6.
    Return alpha*(Nu^2+Nd^2)+cross*Nu*Nd; Nu,Nd >= 0.
    """
    a, b, c, d, e, f, g = map(Q, vector)
    if b == 0 and e == f == g and e >= 0 and d == 6*e/5:
        cross = c-e/8
        margin = min(a, a+cross/2)
        return {'alpha': str(a), 'cross': str(cross), 'margin': str(margin),
                'certified_coercive': margin > 0,
                'scope': 'exact SU3 trace-square decomposition with nonnegative trace-square coefficient'}
    alpha = a + min(b, Q(0))
    cross = c - abs(d)/6 - abs(e) - abs(f) - abs(g)
    margin = min(alpha, alpha + cross/2)
    return {'alpha': str(alpha), 'cross': str(cross), 'margin': str(margin),
            'certified_coercive': margin > 0,
            'scope': 'sufficient bound; failure of this bound is not instability'}


def discover_rational_rays(rows, trials=512, seed=20261008):
    """Numerical discovery followed by exact rational equation checks.

    The seed/trial budget is fixed before any mixing computation. This is not
    an exhaustive classification; nonrational or undiscovered rays can remain.
    """
    import numpy as np
    from scipy.optimize import root
    if type(trials) is not int or not 1 <= trials <= 10000:
        raise ValueError('trials must be in 1..10000')
    tensor = np.zeros((7, 7, 7))
    for k, row in enumerate(rows):
        for (i, j), c in row.items():
            tensor[k, i, j] += float(c)/(1 if i == j else 2)
            if i != j:
                tensor[k, j, i] += float(c)/2
    fun = lambda x: np.einsum('kij,i,j->k', tensor, x, x)-x
    jac = lambda x: 2*np.einsum('kij,j->ki', tensor, x)-np.eye(7)
    rng = np.random.default_rng(seed)
    rational = {}
    numerical = []
    for start in [np.r_[1/128, np.zeros(6)]] + list(rng.normal(0, .018, (trials, 7))):
        result = root(fun, start, jac=jac, tol=1e-11)
        x = result.x
        if not np.all(np.isfinite(x)) or np.linalg.norm(fun(x), np.inf) > 1e-10 or np.linalg.norm(x) < 1e-8:
            continue
        if any(np.linalg.norm(x-y) < 1e-7 for y in numerical):
            continue
        numerical.append(x.copy())
        v = tuple(Q(float(z)).limit_denominator(100000) for z in x)
        if not verify_ray(rows, v):
            continue
        eigen = np.linalg.eigvals(jac(np.array([float(z) for z in v])))
        rational[v] = {'coefficients': list(map(str, v)), 'beta_equals_ray_exact': True,
                       'finite_anisotropy': any(v[i] != 0 for i in (1,)) or len(set(v[4:])) > 1,
                       'global_bound': coercive_lower_bound(v),
                       'normalized_flow_eigenvalues': sorted(float(z.real) for z in eigen),
                       'normalized_flow_eigenvalue_max_imaginary': float(max(abs(eigen.imag)))}
    return {'seed': seed, 'random_starts': trials, 'numerical_distinct_roots': len(numerical),
            'exact_rational_rays': [rational[v] for v in sorted(rational)],
            'numerical_nonrational_or_unreconstructed': len(numerical)-len(rational),
            'complete': False, 'CKM_inputs_used': False}


def su3_census(rows):
    """Complete real ray census in the exchange-symmetric SU(3) restriction.

    Lexicographic rational Groebner elimination plus exact real-root isolation.
    Both ideal inclusions are checked, not just vanishing at sampled roots.
    """
    import sympy as s
    a, c, d, h = s.symbols('a c d h')
    v = (a, 0, c, d, h, h, h)
    B = beta(rows, v)
    if s.expand(B[1]) != 0 or s.expand(B[4]-B[5]) != 0 or s.expand(B[4]-B[6]) != 0:
        raise AssertionError('SU3 restriction is not closed')
    equations = [s.expand(B[k]-v[k]) for k in (0, 2, 3, 4)]
    G = s.groebner(equations, h, d, c, a, order='lex')
    # Reverse membership through a graded basis avoids an unrecorded claim of completeness.
    reverse = s.groebner(equations, a, c, d, h, order='grevlex')
    assert all(G.reduce(q)[1] == 0 for q in equations)
    assert all(reverse.reduce(q.as_expr())[1] == 0 for q in G.polys)
    univariate = G.polys[-1].as_expr()
    assert univariate.free_symbols <= {a}
    maps = {}
    for q in G.polys[:-1]:
        expression = q.as_expr()
        z = next(z for z in (h, d, c) if expression.coeff(z) == 1)
        other = s.expand(z-expression)
        assert other.free_symbols <= {a}
        maps[z] = other
    roots = s.polys.polytools.intervals(univariate, eps=s.Rational(1, 10**30))
    records = []
    for (lo, hi), multiplicity in roots:
        av = (lo+hi)/2
        values = [av, s.Rational(0), maps[c].subs(a, av), maps[d].subs(a, av),
                  maps[h].subs(a, av), maps[h].subs(a, av), maps[h].subs(a, av)]
        records.append({'a_interval': [str(lo), str(hi)], 'multiplicity': multiplicity,
                        'approximate_coefficients': [float(z) for z in values],
                        'exact_coefficients': list(map(str, values)) if lo == hi else None,
                        'zero_ray': lo == hi == 0})
    return {'variables': ['h', 'd', 'c', 'a'],
            'equations': list(map(str, equations)), 'groebner_basis': [str(p.as_expr()) for p in G.polys],
            'eliminant_factors': [[str(p), n] for p, n in s.factor_list(univariate)[1]],
            'both_ideal_inclusions_checked': True, 'unique_back_substitution': True,
            'real_roots_including_zero': records,
            'nonzero_real_ray_count': sum(not r['zero_ray'] for r in records),
            'complete': True, 'scope': 'only the stated four-dimensional SU3 restriction'}
