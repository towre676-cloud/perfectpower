"""Joint operator census and fully minimized nonorthogonal flavor vacua."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product, combinations
import json
import numpy as np
from scipy.optimize import least_squares
from valentiner_joint import *
from develop_valentiner_frames import generators, group_closure, numeric, product as fp, conjugate
from develop_valentiner_invariants import Z, O, add, sub, scale, symchars, exact_integer
from valentiner_joint_certificate import independence_certificate

OUT = ROOT/'receipts/m22_interactions/valentiner_joint.json'


def exact_complex_census():
    """Cauchy/Schur character average; independent of the displayed trace basis."""
    elements = group_closure(generators())[0]
    traces = Counter(tuple(sum(Q(g[1][3*i+i][j], g[0]) for i in range(3)) for j in range(4)) for g in elements)
    partitions = {n: [(a, b, c) for a in range(n+1) for b in range(a+1)
                       for c in [n-a-b] if 0 <= c <= b] for n in range(7)}
    def schur(lam, h):
        def entry(i, j):
            k = lam[i]-i+j
            return h[k] if k >= 0 else Z
        v = Z
        for perm, sign in [((0, 1, 2), 1), ((1, 2, 0), 1), ((2, 0, 1), 1),
                           ((0, 2, 1), -1), ((2, 1, 0), -1), ((1, 0, 2), -1)]:
            v = add(v, scale(fp(fp(entry(0, perm[0]), entry(1, perm[1])), entry(2, perm[2])), sign))
        return v
    chars = []
    for trace, count in traces.items():
        h = symchars(trace, 8)
        chars.append((count, {lam: schur(lam, h) for parts in partitions.values() for lam in parts},
                      [fp(h[k], conjugate(h[k])) for k in range(4)]))
    @lru_cache(None)
    def average(lam, mu, source_degrees):
        total = Z
        for count, sch, hs in chars:
            v = fp(sch[lam], conjugate(sch[mu]))
            for m in source_degrees: v = fp(v, hs[m])
            total = add(total, scale(v, Q(count, 1080)))
        return exact_integer(total)
    counts = Counter(); sectors = []
    for m in product(range(4), repeat=6):
        source_degree = 2*sum(m)
        if source_degree > 6: continue
        for p in range(7-source_degree):
            for q in range(7-source_degree-p):
                degree = source_degree+p+q
                if degree == 0: continue
                dimension = sum(average(lam, mu, tuple(sorted(m[:3])))*average(mu, lam, tuple(sorted(m[3:])))
                                for lam in partitions[p] for mu in partitions[q])
                if dimension:
                    counts[degree] += dimension
                    sectors.append({'link_bidegree': [p, q], 'source_balanced_powers': list(m), 'dimension': dimension})
    # Each shaping factor permits its own holomorphic sextic and conjugate.
    counts[6] += 12
    assert dict(sorted(counts.items())) == {2: 7, 3: 2, 4: 41, 5: 14, 6: 223}
    return {'complex_polynomial_dimensions': dict(sorted(counts.items())), 'multidegree_sectors': sectors,
            'six_holomorphic_source_sextics_and_conjugates': 12,
            'method': 'Exact Q(sqrt(5),omega) Schur/Cauchy character averages on both 1080-element groups; independent C6 source charges.'}


def axis_rays():
    elements = group_closure(generators())[0]
    rays, exact = [], []
    for element in elements:
        M = numeric(element)
        for j in range(3):
            v = M[:, j]
            if all(abs(np.vdot(v, w)) < 1-1e-9 for w in rays):
                rays.append(v)
                exact.append([tuple(Q(a, element[0]) for a in element[1][3*i+j]) for i in range(3)])
    return rays, exact


def nonorthogonal_start():
    rays, exact = axis_rays()
    for indices in combinations(range(len(rays)), 3):
        C = np.column_stack([rays[i] for i in indices]); G = C.conj().T@C
        triangle = G[0, 1]*G[1, 2]*G[2, 0]
        if abs(np.linalg.det(C)) > .1 and abs(triangle.imag) > .02:
            def inner(i, j):
                return tuple(sum(fp(conjugate(exact[indices[i]][k]), exact[indices[j]][k])[a] for k in range(3)) for a in range(4))
            exact_triangle = fp(fp(inner(0, 1), inner(1, 2)), inner(2, 0))
            assert exact_triangle == (Q(1, 8), Q(0), Q(1, 8), Q(0))
            gram_det = add(O, add(exact_triangle, conjugate(exact_triangle)))
            for i, j in combinations(range(3), 2): gram_det = sub(gram_det, fp(inner(i, j), conjugate(inner(i, j))))
            assert gram_det == (Q(1, 8), Q(0), Q(0), Q(0))
            return pack(np.eye(3), np.vstack([C.T, C.T])), {
                'ray_indices': list(indices), 'Gram_triangle': [float(triangle.real), float(triangle.imag)],
                'exact_Gram_triangle': '(1+i*sqrt(3))/16',
                'exact_Gram_triangle_field_coefficients': list(map(str, exact_triangle)),
                'exact_Gram_determinant': '1/8',
                'selection': 'First full-rank triple with nonzero Gram-triangle imaginary part; no CKM target or fit.'}
    raise AssertionError('No nonorthogonal CP triple')


def hierarchical_witness(x0, coefficients, weights):
    """Declared finite illustration; not energy or observed-anchor selection."""
    rays, _ = axis_rays(); L, p = unpack(x0)
    heavy = 10  # The common dominant ray in the retained up-source triple.
    retained = []; scanned = 0; full_rank = 0
    for i, j in combinations([k for k in range(len(rays)) if k != heavy], 2):
        scanned += 1
        D = np.column_stack([rays[i], rays[j], rays[heavy]])
        if abs(np.linalg.det(D)) < .05: continue
        full_rank += 1
        z = pack(L, np.vstack([p[:3], D.T])); obs = quarks(z, weights)
        if 1e-8 < obs['Vub'] < obs['Vcb'] < obs['Vus'] and abs(obs['J']) > 1e-12:
            retained.append((obs['Vus'], i, j, z, obs))
    _, i, j, z0, initial = min(retained, key=lambda row: row[0])
    z, status = solve(z0, coefficients)
    return {'shared_heavy_ray_index': heavy, 'down_ray_indices': [i, j, heavy],
            'scanned_pairs': scanned, 'full_rank_pairs_above_declared_cut': full_rank,
            'ordered_nonzero_mixing_and_CP_pairs': len(retained),
            'selection': 'Smallest Vus among enumerated full-rank shared-heavy-ray pairs satisfying Vub<Vcb<Vus and nonzero J, with the declared weights. This is a diagnostic witness, not a dynamically selected vacuum or a fit to measured anchors.',
            'before_mixed_operators': initial, 'fully_minimized': {**status, 'observables': quarks(z, weights),
                                                                 'source_grams': gram_record(z), 'field_coordinates': z.tolist()}}


def parameter_response(x, coefficients, weights):
    H = hessian(x, coefficients)
    _, names, _, derivatives = operator_basis(x, True)
    def extended_observable(z, w):
        q = quarks(z, w)
        return np.concatenate([[q[k] for k in ['Vus', 'Vcb', 'Vub', 'J']], np.log(np.array(q['spectra']).ravel())])
    observable = lambda z, w: extended_observable(z, w)[:4]
    directions, columns, mass_columns = [], [], []
    # All 263 scalar directions and all six independent quark column weights.
    for i, name in enumerate(names):
        if name.startswith('X') or name.startswith('B'):
            direction = np.linalg.solve(H, -derivatives[i])
            eps = 2e-5/max(1., np.linalg.norm(direction))
            column = (extended_observable(x+eps*direction, weights)-extended_observable(x-eps*direction, weights))/(2*eps)
            directions.append(name); columns.append(column[:4]); mass_columns.append(column[4:])
    for i in range(6):
        plus, minus = weights.copy(), weights.copy(); plus[i] *= np.exp(2e-5); minus[i] *= np.exp(-2e-5)
        column = (extended_observable(x, plus)-extended_observable(x, minus))/(4e-5)
        directions.append(f'log_lambda{i}'); columns.append(column[:4]); mass_columns.append(column[4:])
    J = np.column_stack(columns); sv = np.linalg.svd(J, compute_uv=False)
    normalized = J/np.maximum(np.linalg.norm(J, axis=0), 1e-25)
    nsv = np.linalg.svd(normalized, compute_uv=False)
    def closure(z, w):
        C = quarks(z, w)['depth']; return C*C-3*C+1
    closure_columns = []
    for name in directions:
        if name.startswith('log_lambda'):
            i = int(name[len('log_lambda'):]); plus, minus = weights.copy(), weights.copy()
            plus[i] *= np.exp(2e-5); minus[i] *= np.exp(-2e-5)
            closure_columns.append((closure(x, plus)-closure(x, minus))/(4e-5))
        else:
            direction = np.linalg.solve(H, -derivatives[names.index(name)])
            eps = 2e-5/max(1., np.linalg.norm(direction))
            closure_columns.append((closure(x+eps*direction, weights)-closure(x-eps*direction, weights))/(2*eps))
    reference = observable(x, weights)
    scaled = J/np.abs(reference[:, None])
    scaled_sv = np.linalg.svd(scaled/np.maximum(np.linalg.norm(scaled, axis=0), 1e-25), compute_uv=False)
    mass_J = np.column_stack(mass_columns)
    correction = np.linalg.solve(mass_J[:, 15:], -mass_J[:, :15])
    conditioned = J[:, :15]+J[:, 15:]@correction
    conditioned_scaled = conditioned/np.abs(reference[:, None])
    conditioned_sv = np.linalg.svd(conditioned_scaled/np.linalg.norm(conditioned_scaled, axis=0), compute_uv=False)
    return {'observable_order': ['Vus', 'Vcb', 'Vub', 'J'], 'parameter_names': directions,
            'jacobian': J.tolist(), 'singular_values': sv.tolist(),
            'column_normalized_singular_values': nsv.tolist(),
            'fractional_observable_column_normalized_singular_values': scaled_sv.tolist(),
            'six_log_mass_jacobian': mass_J.tolist(),
            'quark_weight_mass_jacobian_singular_values': np.linalg.svd(mass_J[:, 15:], compute_uv=False).tolist(),
            'mass_preserving_log_weight_compensation': correction.tolist(),
            'six_masses_fixed_observable_jacobian': conditioned.tolist(),
            'six_masses_fixed_fractional_column_normalized_singular_values': conditioned_sv.tolist(),
            'golden_polynomial_derivatives': closure_columns,
            'scope': 'Numerical local response to allowed scalar couplings and independent quark weights; scalar response solves the full 54-dimensional Hessian equation.'}


def main():
    census = exact_complex_census(); print('exact census complete', flush=True)
    certificate = independence_certificate(); print('modular independence complete', flush=True)
    x0, selection = nonorthogonal_start()
    degrees, names, _ = operator_basis(x0)
    rng = np.random.default_rng(108066)
    # Explicit generic EFT coefficients: all independent and nonzero, no fit.
    coefficients = rng.uniform(.2, 1., len(names))*1e-4
    coefficients[names.index('S3')] = .02
    for name in names:
        if name.startswith('B'): coefficients[names.index(name)] = .5*rng.uniform(.8, 1.2)
        if name.startswith('X'): coefficients[names.index(name)] = -.5*rng.uniform(.8, 1.2)
    cases = []; current = x0.copy()
    weights = np.array([.007, .05, .9, .02, .2, .85])
    for factor in [0., .25, 1., 4.]:
        c = coefficients*factor
        if factor == 0: z, status = solve(x0, c)
        else: z, status = solve(current, c)
        current = z
        obs = quarks(z, weights)
        cases.append({'coupling_factor': factor, **status, 'observables': obs, 'source_grams': gram_record(z),
                      'field_coordinates': z.tolist(), 'all_263_coefficients_nonzero': bool(np.all(c != 0))})
        print('joint case', factor, status, {k: obs[k] for k in ['Vus', 'Vcb', 'Vub', 'J', 'depth']}, flush=True)
    chosen = cases[2]; x = np.array(chosen['field_coordinates']); c = coefficients
    assert chosen['stationarity_max'] < 1e-5 and chosen['minimum_real_hessian_eigenvalue_scaled'] > 0
    response = parameter_response(x, c, weights)
    # A positive pure-link sextic bounds every other pure-link sextic.
    margin = c[names.index('S3')]-abs(c[names.index('ST')])-abs(c[names.index('R')])-abs(c[names.index('ReD2')])/27-16*abs(c[names.index('ReI6')])
    assert margin > 0
    finite = []
    for name in ['X02', 'B02']:
        index = names.index(name)
        for sign in [-1, 1]:
            shifted = c.copy(); shifted[index] += sign*.01*abs(c[index])
            z, status = solve(x, shifted)
            target_masses = np.log(np.array(chosen['observables']['spectra']).ravel())
            def mass_residual(logw):
                return np.log(np.array(quarks(z, np.exp(logw))['spectra']).ravel())-target_masses
            mass_fit = least_squares(mass_residual, np.log(weights), xtol=1e-13, ftol=1e-13, gtol=1e-13, max_nfev=100)
            assert np.max(abs(mass_residual(mass_fit.x))) < 1e-8
            finite.append({'operator': name, 'coefficient_fractional_change': sign*.01,
                           **status, 'observables': quarks(z, weights),
                           'same_six_masses_refitted_weights': np.exp(mass_fit.x).tolist(),
                           'same_six_masses_log_residual_max': float(np.max(abs(mass_residual(mass_fit.x)))),
                           'same_six_masses_observables': quarks(z, np.exp(mass_fit.x))})
    # Independent weak-basis determinant and a matter-sector stability bound.
    L, phi = unpack(x)
    Cu, Cd = RHO*phi[:3].T@np.diag(weights[:3]), RHO*phi[3:].T@np.diag(weights[3:])
    Yu = canonical_mediator(.9*np.eye(3), Cu, h=.6)['Y']
    Yd = holomorphic_down_matching((RHO*L).conj(), Cd.conj())['Y']
    Hu, Hd = Yu@Yu.conj().T, Yd@Yd.conj().T
    commdet = float(np.linalg.det(Hu@Hd-Hd@Hu).imag)
    matter_B_bound = float(RHO**5*np.sqrt(sum(weights[i]**2*np.linalg.norm(source_poly(p)[1])**2 for i, p in enumerate(phi))))
    assert matter_B_bound < 1e-4
    alternatives = []
    for ratio in [.9, 1., 1.1]:
        w = weights.copy(); w[4] *= ratio
        alternatives.append({'down_second_column_factor': ratio, 'observables': quarks(x, w)})
    cp = json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())
    X = np.array([[complex(s.sympify(t).evalf()) for t in row] for row in cp['unitary_CP_matrix']])
    L, p = unpack(x); cp_x = pack(X@L.conj()@X.conj().T, (X@p.conj().T).T)
    cp_obs = quarks(cp_x, weights)
    assert abs(potential(x, c)[0]-potential(cp_x, c)[0]) < 1e-9
    assert abs(cp_obs['J']+chosen['observables']['J']) < 1e-12
    result = {'schema': 'pp-valentiner-joint/1', 'exact_census': census,
              'exact_basis_independence_certificate': certificate,
              'CP_even_counts': {str(k): degrees.count(k) for k in sorted(set(degrees))},
              'CP_odd_counts': {'2': 0, '3': 1, '4': 0, '5': 7, '6': 16},
              'operators': [{'degree': d, 'name': n, 'scaled_coefficient': float(v)} for d, n, v in zip(degrees, names, coefficients)],
              'source_selection': selection, 'quark_column_weights': weights.tolist(),
              'shared_heavy_ray_hierarchy_witness': hierarchical_witness(x0, coefficients, weights),
              'vacua': cases, 'CP_conjugate_observables': cp_obs,
              'independent_quark_column_variations': alternatives, 'local_response': response,
              'fully_reminimized_one_percent_deformations': finite,
              'weak_basis_commutator_determinant_imaginary': commdet,
              'source_induced_matter_B_frobenius_upper_bound': matter_B_bound,
              'specified_universal_matter_breaking_mass_squared': 1e-4,
              'matter_scalar_mass_squared_lower_bound': 1e-4-matter_B_bound,
              'pure_link_sextic_coercivity_margin': float(margin),
              'coercivity_argument': 'S^3 dominates ST,R,Re(det(L)^2),Re(I6) by bounds 1,1,1/27,16. Source grad(F6) is nonzero on the unit sphere, hence its norm-square gives a positive degree-ten radial bound. All remaining link/source mixed monomials have weighted growth a/6+b/10<1. Thus every positive coupling-factor case is coercive; the global winner is not identified.',
              'physical_scaling': 'L_physical=rho*L, Phi_physical=rho*Phi, rho=.1; V_physical=rho^10*V_scaled. A degree-d scalar coefficient has physical value c_d*rho^(10-d). Physical canonical real squared masses are rho^8/2 times the displayed raw-coordinate Hessian eigenvalues.',
              'scope': 'Complete independent CP-even polynomial scalar potential through degree six on the zero-matter/Higgs slice, added to the stated SUSY F potential (link degrees 4,7,10; source degree 10). Canonical kinetic terms and the specified quark chain, no exhaustive Kahler/quark/loop EFT, no global-minimum classification or experimental fit.',
              'frame_weight_theorem': 'For a full-rank fixed column matrix, its left eigenframe is independent of all positive independent column weights on an open set iff its rank-one column projectors commute, hence iff its columns are pairwise orthogonal. This statement concerns frame protection, not every possible isolated observable identity.',
              'conclusion': 'Nonorthogonal local vacua escape the .309 orthogonal-frame floor and can give hierarchical nonzero mixing with physical weak CP. Independent allowed interactions and quark-column weights still move the golden coefficient. No golden prediction, derived coupling hierarchy or unique CP sign.'}
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print('receipt', OUT, flush=True)


if __name__ == '__main__': main()
