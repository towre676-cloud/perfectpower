"""Constructive kinetic freedom at fixed scalar vacuum and six quark masses."""
from pathlib import Path
from itertools import combinations
from fractions import Fraction as Q
import json
import numpy as np
import sympy as s
import mpmath as mp
from scipy.linalg import expm
from perfectpower.flavor_kinetic import KineticCovariants, fixed_spectrum_bare_metric, inner, matrix
from perfectpower.flavor_mediator import mixing_record, inverse_sqrt
from perfectpower.flavor_prediction import ckm_from_depth
from valentiner_joint import unpack, RHO, link_poly, adjugate, EPSILON
from develop_valentiner_susy_vacua import holomorphic_down_matching
from develop_valentiner_frames import generators, group_closure, conjugate, product as fp
from develop_valentiner_invariants import O, Z, add, sub, scale, exact_integer

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/m22_interactions/flavor_kinetic.json'


def symbolic_spanning_proof():
    r = s.symbols('r1 r2 r3', real=True)
    d = s.symbols('d1 d2 d3', real=True)
    a, b, c, e, f, g = s.symbols('a b c e f g', real=True)
    S = s.Matrix([[d[0], a+s.I*b, c+s.I*e], [a-s.I*b, d[1], f+s.I*g], [c-s.I*e, f-s.I*g, d[2]]])
    tau = s.expand(s.im(S[0, 1]*S[1, 2]*S[2, 0]))
    determinants = []
    for i, j in combinations(range(3), 2):
        z, w = S[i, j], (S*S)[i, j]
        det = s.expand(s.re(z)*s.im(w)-s.re(w)*s.im(z))
        assert s.expand(det-([ -tau, tau, -tau][len(determinants)])) == 0
        determinants.append(det)
    assert s.expand(s.prod(determinants)-tau**3) == 0
    R = s.diag(*r)
    delta = (r[1]-r[0])*(r[2]-r[0])*(r[2]-r[1])
    assert s.expand(s.im(s.trace(R*R*S*S*R*S))-delta*tau) == 0
    return {'exact_pair_determinants': ['-tau', 'tau', '-tau'],
            'nine_Hermitian_generator_coordinate_determinant': 'tau^3',
            'tau': 'Im(S12*S23*S31) in an R eigenbasis',
            'CP_invariant_identity': 'Im Tr(R^2*S^2*R*S)=Delta(R)*tau',
            'number_of_generators': 9, 'all_coefficients_real': True,
            'polynomial_positive_metric_flavor_degree_bound': '24*p+8*q, where deg X=p and deg Z=q',
            'proof_status': 'Exact symbolic identities; projector interpolation and the positive completion are established in the accompanying proof.'}


def label_contractions():
    elements = group_closure(generators())[0]
    counts = [Z, Z, Z]
    for G in elements:
        tr = tuple(sum(Q(G[1][3*i+i][j], G[0]) for i in range(3)) for j in range(4))
        adj = sub(fp(tr, conjugate(tr)), O)
        counts[0] = add(counts[0], fp(tr, conjugate(tr)))
        counts[1] = add(counts[1], fp(adj, adj))
        counts[2] = add(counts[2], fp(fp(adj, adj), adj))
    dims = [exact_integer(scale(x, Q(1, 1080))) for x in counts]
    assert dims == [1, 1, 2]
    return {'common_label_group': '3.A6_H', 'source_matrices': 'A=(3_u,3bar_H), B=(3_d,3bar_H)',
            'RH_quarks': 'One H triplet per charge sector; one global C6 charge per source matrix, replacing six independently charged source columns.',
            'exact_invariant_multiplicities': {'triplet_pair_singlet': dims[0], 'adjoint_pair_singlet': dims[1], 'adjoint_cubic_singlets': dims[2]},
            'quark_column_coefficients_per_sector': 1,
            'dressed_label_channels': ['|Tr(A^dagger*L*B)|^2', 'Tr(Z^dagger*Z)-|Tr Z|^2/3; Z=A^dagger*L*B'],
            'adjoint_mediator_matching': 'M^2||S||^2-2k Re Tr(S^dagger Z_8) gives V_eff=-(k^2/M^2)||Z_8||^2, with Z_8=Z-(Tr Z)I/3.',
            'fixed_Clebsch_ratio': '-1/3 in the traceless norm; not the nominated golden coefficient',
            'allowed_additional_UV_interactions': 'S^dagger S times link norm; source norm and both adjoint bilinears for each A,B; pure S quartics. These cannot be silently excluded from higher-order matching.',
            'scope': 'A justified label/Yukawa contraction and leading adjoint-exchange correlation, not a complete predictive CKM vacuum.'}


def rank_one_source_spectrum(t=-34., c=.2):
    A = np.diag([1., 0., 0.]).astype(complex)
    def V(A):
        D = np.linalg.det(A); value, g, _ = link_poly(A)
        grad = g+2*c*D*adjugate(A).T.ravel()
        W = value+c*D*D
        return np.vdot(grad, grad).real-(180+6*t)*np.vdot(A, A).real+2*t*W.real
    E = np.vstack([np.eye(9), 1j*np.eye(9)]).reshape(18, 3, 3)/np.sqrt(2)
    eps = 3e-5
    H = np.array([[(V(A+eps*(e+f))-V(A+eps*(e-f))-V(A+eps*(-e+f))+V(A-eps*(e+f)))/(4*eps*eps)
                   for f in E] for e in E])
    off = -90-6*t; low = -171-6*t
    exact = [1440+24*t, -36*t]+[off-3*np.sqrt(10)*abs(24+t)]*4+[off+3*np.sqrt(10)*abs(24+t)]*4+[low-3*abs(24+t)]*4+[low+3*abs(24+t)]*4
    actual = np.linalg.eigvalsh(H)
    assert np.max(abs(actual-np.sort(exact))) < .002
    assert min(actual) > 0
    return {'t': t, 'source_superpotential': 'W_A=I6(A)+c*det(A)^2', 'determinant_square_coefficient': c,
            'source_potential': '||grad W_A||^2-(180+6t)||A||^2+2t Re W_A',
            'stationary_rank_one_branch': 'A=rho*u*v^dagger for group-rotated axis rays u,v',
            'eighteen_real_canonical_mass_coefficients': sorted(map(float, exact)),
            'numerical_Hessian_max_error': float(np.max(abs(actual-np.sort(exact)))),
            'energy_scaled': float(V(A)), 'stable_interval_below_origin': '-36<t<-33',
            'scope': 'Locally stable one-heavy-family source branch with universal quark coupling. Two light modes remain massless before rank-lifting interactions; no joint three-family vacuum or golden relation is claimed.'}


def actual_vacuum_setup():
    receipt = json.loads((ROOT/'receipts/m22_interactions/valentiner_joint.json').read_text())
    x = receipt['vacua'][2]['field_coordinates']; L, phi = unpack(x)
    weights = np.array(receipt['quark_column_weights'])
    Cu, Cd = RHO*phi[:3].T@np.diag(weights[:3]), RHO*phi[3:].T@np.diag(weights[3:])
    au = Cu/.9; ku = np.eye(3)+au.conj().T@au; yu0 = -.6*au; yu = yu0@inverse_sqrt(ku)
    physical_L = RHO*L
    down = holomorphic_down_matching(physical_L.conj(), Cd.conj())
    ad = np.linalg.solve(down['M'], np.vstack([np.zeros((3, 3)), Cd]))
    kd = np.eye(3)+ad.conj().T@ad; yd0 = -.57*ad[:3]; yd = yd0@inverse_sqrt(kd)
    return yu, yd, yd0, ad, physical_L@Cd, Cu


def actual_vacuum_countermetrics():
    yu, yd, yd0, ad, X, Z = actual_vacuum_setup()
    frame = KineticCovariants(X, Z)
    _, uu = np.linalg.eigh(yu@yu.conj().T); hd = yd@yd.conj().T
    rows = []; response = []
    for i, j in combinations(range(3), 2):
        for kind in ['real', 'imaginary']:
            G = np.zeros((3, 3), complex)
            if kind == 'real': G[i, j], G[j, i] = 1, -1
            else: G[i, j] = G[j, i] = 1j
            pair = []
            for sign in [-1, 1]:
                epsilon = sign*1e-5
                U = uu@expm(epsilon*G)@uu.conj().T
                target = U@hd@U.conj().T
                matched = fixed_spectrum_bare_metric(yd0, ad, target)
                completed = frame.positive_completion(matched['bare_metric'])
                assert completed['error'] < 1e-55
                obs = mixing_record(yu, matched['matched_Y'])
                pair.append(obs)
                rows.append({'mass_basis_plane': [i, j], 'generator': kind, 'rotation': epsilon,
                             'minimum_bare_metric_eigenvalue': matched['minimum_bare_metric_eigenvalue'],
                             'metric_operator_distance_from_identity': matched['metric_operator_distance_from_identity'],
                             'target_H_error': matched['target_H_error'], 'positive_completion_error': completed['error'],
                             'real_polynomial_metric_coefficients': completed['real_coefficients'],
                             'observables': obs})
            response.append([(pair[1][k]-pair[0][k])/2e-5 for k in ['Vus', 'Vcb', 'Vub', 'J']])
    J = np.array(response).T; ref = mixing_record(yu, yd)
    scaled = J/np.array([abs(ref[k]) for k in ['Vus', 'Vcb', 'Vub', 'J']])[:, None]
    singular = np.linalg.svd(scaled/np.linalg.norm(scaled, axis=0), compute_uv=False)
    assert singular[-1] > .01
    masses = np.array(ref['spectra'])
    error = max(np.max(abs(np.log(np.array(q['observables']['spectra'])/masses))) for q in rows)
    with mp.workdps(90):
        gram_error = max(abs(inner(a, b)-int(i==j)) for i, a in enumerate(frame.basis) for j, b in enumerate(frame.basis))
    return {'reference': ref, 'twelve_positive_kinetic_countermetrics': rows,
            'six_fixed_mass_max_log_residual_in_double_SVD': float(error),
            'fractional_observable_column_normalized_response_singular_values': singular.tolist(),
            'nine_polynomial_basis_orthonormality_error': float(gram_error),
            'finite_polynomial_covariants': 'X=L*Cd (degree 2), Z=Cu (degree 1)',
            'positive_bare_metric_max_flavor_degree': 56,
            'scope': 'Same solved scalar vacuum and superpotential as f76767e. Only the bare RH down-quark metric changes; its full heavy-null-space matching is recalculated. All six singular values stay fixed.'}


def golden_countermetric():
    golden = (3-np.sqrt(5))/2; delta = 11*np.pi/30
    u, v = .2253, .0409
    yu = np.diag([.000005, .002, .6]).astype(complex)
    V = ckm_from_depth(golden, delta, u, v); yd = V@np.diag([.0003, .006, .3])
    frame = KineticCovariants(yd, yu); rows = []
    for sign in [-1, 1]:
        targetV = ckm_from_depth(golden*(1+sign*.001), delta, u, v)
        targetH = targetV@np.diag([.0003**2, .006**2, .3**2])@targetV.conj().T
        result = fixed_spectrum_bare_metric(yd, np.zeros((3, 3)), targetH)
        completion = frame.positive_completion(result['bare_metric'])
        obs = mixing_record(yu, result['matched_Y'])
        assert result['metric_operator_distance_from_identity'] < .01
        assert abs(obs['depth']-golden*(1+sign*.001)) < 1e-10
        rows.append({'fractional_C_change': sign*.001, 'metric_operator_distance_from_identity': result['metric_operator_distance_from_identity'],
                     'minimum_metric_eigenvalue': result['minimum_bare_metric_eigenvalue'],
                     'positive_polynomial_completion_error': completion['error'], 'observables': obs})
    return {'reference': mixing_record(yu, yd), 'cases': rows,
            'scope': 'Initialized golden/66-degree chart is used solely as a counterexample test, not as a derived vacuum. Both anchors, the physical phase and all masses are held fixed while C changes.'}


def main():
    result = {'schema': 'pp-flavor-kinetic-freedom/1', 'symbolic_proof': symbolic_spanning_proof(),
              'label_contraction_candidate': label_contractions(), 'rank_one_source': rank_one_source_spectrum(),
              'actual_vacuum': actual_vacuum_countermetrics(), 'golden_chart_counterexample': golden_countermetric(),
              'theorem_scope': 'Unitary internal flavor transformations, CP-covariant flavor functions, full-rank nondegenerate reference spectra and nonzero CP triangle. Complete allowed matter kinetic operators with independent real coefficients. Polynomial degree bounds apply to polynomial covariants; analytic matched functions need their EFT expansion.',
              'conclusion': 'Nine CP-even polynomial matter metrics span the complete Hermitian flavor space. Positive bare metrics can preserve a fixed scalar vacuum and all six quark masses while moving all four CKM observables. Symmetry alone cannot protect the nominated relation against the complete kinetic operator space. UV matching can still predict correlated coefficients; no assertion that loop corrections are large or that flavor models cannot be predictive.'}
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print('actual',result['actual_vacuum']['fractional_observable_column_normalized_response_singular_values'])
    print('mass residual',result['actual_vacuum']['six_fixed_mass_max_log_residual_in_double_SVD'])
    print('golden',result['golden_chart_counterexample'])
    print('receipt',OUT)


if __name__ == '__main__': main()
