"""Degree-six SUSY link vacua, their mass gap, and the source-vacuum obstruction.

No CKM target is inserted. Exact statements concern the specified truncated
superpotential with canonical kinetic terms and zero matter/Higgs backgrounds.
"""
from itertools import product
from math import factorial
from pathlib import Path
import json
import numpy as np
import sympy as s
from fractions import Fraction as Q
from develop_valentiner_frames import generators, group_closure, numeric, product as field_product, conjugate
from develop_valentiner_link import coefficient_functions
from perfectpower.flavor_mediator import canonical_mediator, mixing_record

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts/m22_interactions/valentiner_susy_vacua.json'


def exact_tensor_derivatives():
    field = s.QQ.algebraic_field(s.sqrt(5), s.I * s.sqrt(3))
    rows = json.loads((ROOT / 'receipts/m22_interactions/valentiner_invariants.json').read_text())['sextic']['terms']
    coefficients = {tuple(r['powers']): field.from_sympy(s.sympify(r['coefficient'])) for r in rows}
    tensor = {}
    for idx in product(range(3), repeat=6):
        powers = tuple(idx.count(i) for i in range(3))
        mult = factorial(6) // __import__('math').prod(factorial(p) for p in powers)
        tensor[idx] = coefficients.get(powers, field.zero) / field.convert(mult)
    conjugated = {k: field.from_sympy(s.conjugate(field.to_sympy(v))) for k, v in tensor.items()}
    checked = 0
    for i, j, k, l in product(range(3), repeat=4):
        value = sum((conjugated[(i, j) + tail] * tensor[(k, l) + tail]
                     for tail in product(range(3), repeat=4)), field.zero)
        expected = field.convert(s.Rational(4, 3) * (int(i == k and j == l) + int(i == l and j == k)))
        assert value == expected
        checked += 1
    return {'exact_two_index_density_entries': checked,
            'density': '(4/3)*(delta_ik*delta_jl+delta_il*delta_jk)',
            'I6_second_derivative_at_I': '40*(Tr(E)*Tr(F)+Tr(E*F))',
            'W_second_derivative_at_rI_on_F_flat_branch':
            'r^4*((8*b+2*c)*Tr(E)*Tr(F)+72*b*Tr(E*F))'}


def source_critical_locus():
    data = json.loads((ROOT / 'receipts/m22_interactions/valentiner_invariants.json').read_text())
    x, y, z = s.symbols('x y z')
    f = s.sympify(data['sextic']['polynomial'], locals={'x': x, 'y': y, 'z': z})
    A = s.expand(f).coeff(x, 4).coeff(y, 2)
    B = s.expand(f).coeff(x, 2).coeff(y, 4)
    D = s.expand(f).coeff(x, 2).coeff(y, 2).coeff(z, 2)
    u, v, w = s.symbols('u v w')
    h = u**3 + v**3 + w**3 + A*(u*u*v+v*v*w+w*w*u) + B*(u*v*v+v*w*w+w*u*u) + D*u*v*w
    field = s.QQ.algebraic_field(s.sqrt(5), s.I * s.sqrt(3))
    assert s.Poly(h.subs({u: v, v: w, w: u}, simultaneous=True)-h, u, v, w, domain=field).is_zero
    # Nonzero x permits u=x^2=1 after homogeneous rescaling. Cyclicity covers
    # every choice of nonzero coordinate. All support sizes are checked.
    full = s.groebner([s.diff(h, t).subs(u, 1) for t in (u, v, w)], v, w, domain=field)
    assert list(full) == [1]
    two = s.resultant(s.diff(h, u).subs({u: 1, w: 0}),
                      s.diff(h, v).subs({u: 1, w: 0}), v)
    two = field.to_sympy(field.from_sympy(two))
    assert field.from_sympy(two) != field.zero
    one = s.diff(h, u).subs({u: 1, v: 0, w: 0})
    assert one == 3
    return {'full_support_Groebner_basis': ['1'], 'two_support_resultant': str(two),
            'one_support_derivative': str(one), 'cyclic_reduction_verified': True,
            'gradient_F6_zero_iff_triplet_zero': True,
            'conjugate_triplet_same_result': True,
            'generic_nonzero_source_coefficients_imply_all_six_sources_zero': True,
            'scalar_source_complex_modes_with_no_quadratic_mass_at_origin': 18,
            'source_F_energy_first_nonzero_degree': 10}


def link_branch(a, b, c):
    """Masses in canonical units; a dimensionless, b,c have mass dimension -3."""
    a, b, c = map(float, (a, b, c))
    d = 32*b + 2*c
    if d == 0 or a == 0:
        raise ValueError('nonzero generic group branch required')
    r = np.cbrt(-a/d)
    masses = [abs((96*b+6*c)*r**4), abs(72*b*r**4)]
    return {'a': a, 'b': b, 'c': c, 'real_radius': float(r),
            'F_gradient_scalar': float(a*r*r+d*r**5),
            'singlet_fermion_mass': masses[0], 'adjoint_fermion_mass': masses[1],
            'real_scalar_mass_squared_levels': [
                {'mass_squared': masses[0]**2, 'multiplicity': 2},
                {'mass_squared': masses[1]**2, 'multiplicity': 16}],
            'isolated_link_minimum': bool(min(masses) > 0),
            'origin_also_F_flat': True}


def source_breaking_branch(radius=.1, kappa=1., t=-24.):
    """V=kappa^2|grad F6|^2-m2|Phi|^2+2*A*kappa*Re F6.

    t=A/(kappa*r^4). These are specified spurion-breaking EFT terms, not
    an exhaustive symmetry-allowed breaking action.
    """
    p = 3*np.sqrt(10)/2  # Exact |A_tensor|=|B_tensor|=sqrt(45/2).
    radial = 1440+24*t
    phase = -36*t
    transverse = [-90-6*t-p*abs(48+2*t), -90-6*t+p*abs(48+2*t)]
    scale = kappa*kappa*radius**8
    m2 = scale*(180+6*t)
    breaking_A = t*kappa*radius**4
    masses = [radial, phase]+2*transverse
    assert min(masses) > 0 and m2 > 0
    return {'radius': radius, 'kappa': kappa, 't': t,
            'tachyon_parameter_m2': float(m2), 'holomorphic_breaking_A': float(breaking_A),
            'real_scalar_mass_squared': [float(x*scale) for x in masses],
            'energy': float(kappa*kappa*radius**10*(-144-4*t)),
            'stable_open_t_interval_with_positive_m2':
            '-30<t<-(90+72*sqrt(10))/(6+3*sqrt(10))',
            'source_F_norm': float(6*abs(kappa)*radius**5),
            'scope': 'Locally stable axis branch and its group transforms. No claim that these are all source vacua or the global winners.'}


def orthogonal_axis_census():
    """Finite axis-ray census and exact lower bound on group entries."""
    group = group_closure(generators())[0]
    matrices = np.array([numeric(g) for g in group])
    rays, exact_rays, ray_keys = [], [], {}
    def projector_key(v):
        return tuple(field_product(v[i], conjugate(v[j])) for i in range(3) for j in range(3))
    for g, (den, entries) in zip(matrices, group):
        v = g[:, 0]
        exact = [tuple(Q(z, den) for z in entries[3*i]) for i in range(3)]
        key = projector_key(exact)
        if key not in ray_keys:
            ray_keys[key] = len(rays)
            rays.append(v)
            exact_rays.append(exact)
    orthogonal = np.zeros((len(rays), len(rays)), bool)
    for i, u in enumerate(exact_rays):
        for j, v in enumerate(exact_rays):
            terms = [field_product(conjugate(u[k]), v[k]) for k in range(3)]
            orthogonal[i, j] = all(sum(t[k] for t in terms) == 0 for k in range(4))
    assert np.array_equal(orthogonal, np.abs(np.array(rays).conj()@np.array(rays).T) < 2e-12)
    from itertools import combinations
    triples = [q for q in combinations(range(len(rays)), 3)
               if all(orthogonal[i, j] for i, j in combinations(q, 2))]
    actions = []
    for den, entries in generators():
        M = [[tuple(Q(z, den) for z in entries[3*i+j]) for j in range(3)] for i in range(3)]
        permutation = []
        for v in exact_rays:
            image = []
            for i in range(3):
                terms = [field_product(M[i][j], v[j]) for j in range(3)]
                image.append(tuple(sum(t[k] for t in terms) for k in range(4)))
            permutation.append(ray_keys[projector_key(image)])
        assert sorted(permutation) == list(range(len(rays)))
        actions.append(permutation)
    remaining = set(triples)
    orbit_sizes, orbit_labels = [], {}
    while remaining:
        root = min(remaining)
        orbit, todo = {root}, [root]
        while todo:
            current = todo.pop()
            for permutation in actions:
                image = tuple(sorted(permutation[i] for i in current))
                assert image in triples
                if image not in orbit:
                    orbit.add(image)
                    todo.append(image)
        remaining -= orbit
        for q in orbit:
            orbit_labels[q] = len(orbit_sizes)
        orbit_sizes.append(len(orbit))
    values = set()
    for den, entries in group:
        for entry in entries:
            z = tuple(Q(v, den) for v in entry)
            squared = field_product(z, conjugate(z))
            assert squared[2:] == (0, 0)
            values.add(squared[:2])
    lower, upper = Q(2236067977499789, 10**15), Q(2236067977499790, 10**15)
    assert lower*lower < 5 < upper*upper
    bounds = [a+b*(lower if b >= 0 else upper) for a, b in values if (a, b) != (0, 0)]
    assert min(bounds) > Q(9, 100)  # Every nonzero magnitude exceeds .3.
    exact_minimum = (Q(3, 8), Q(-1, 8))
    assert exact_minimum in values
    for a, b in values:
        if (a, b) in ((0, 0), exact_minimum):
            continue
        a, b = a-exact_minimum[0], b-exact_minimum[1]
        assert a+b*(lower if b >= 0 else upper) > 0
    magnitudes = np.sqrt(np.array([float(a)+float(b)*np.sqrt(5) for a, b in values]))
    minimum = min(x for x in magnitudes if x > 1e-10)
    j = np.imag(matrices[:, 0, 0]*matrices[:, 1, 1]*matrices[:, 0, 1].conj()*matrices[:, 1, 0].conj())
    frames = [np.column_stack([rays[i] for i in q]) for q in triples]
    js = []
    for U in frames:
        for D in frames:
            V = U.conj().T@D
            js.append(float(np.imag(V[0, 0]*V[1, 1]*V[0, 1].conj()*V[1, 0].conj())))
    witness = next(i for i, x in enumerate(js) if abs(x) > 1e-5)
    U, D = frames[witness//len(frames)], frames[witness % len(frames)]
    uq, dq = triples[witness//len(frames)], triples[witness % len(frames)]
    def entry(i, j):
        terms = [field_product(conjugate(exact_rays[uq[i]][k]), exact_rays[dq[j]][k]) for k in range(3)]
        return tuple(sum(v[n] for v in terms) for n in range(4))
    jproduct = field_product(field_product(entry(0, 0), entry(1, 1)),
                             field_product(conjugate(entry(0, 1)), conjugate(entry(1, 0))))
    assert jproduct[2:] == (Q(-1, 16), Q(0))
    encoded = lambda M: [[[float(z.real), float(z.imag)] for z in row] for row in M]
    return {'projective_axis_rays': len(rays), 'orthogonal_unordered_axis_frames': len(triples),
            'orthogonal_axis_group_orbit_sizes': orbit_sizes,
            'complete_ordered_frame_pair_census_size': len(js),
            'frame_pair_J_range': [min(js), max(js)],
            'within_same_frame_orbit_max_abs_J': max(abs(js[i*len(triples)+j]) for i, q in enumerate(triples) for j, p in enumerate(triples) if orbit_labels[q] == orbit_labels[p]),
            'mixed_frame_orbit_max_abs_J': max(abs(js[i*len(triples)+j]) for i, q in enumerate(triples) for j, p in enumerate(triples) if orbit_labels[q] != orbit_labels[p]),
            'CP_witness_frame_orbits': [orbit_labels[uq], orbit_labels[dq]],
            'exact_group_entry_squared_values': [[str(a), str(b)] for a, b in sorted(values)],
            'sqrt5_rational_enclosure': [str(lower), str(upper)],
            'exact_nonzero_magnitude_lower_bound': '3/10',
            'exact_smallest_nonzero_magnitude': '(sqrt(5)-1)/4',
            'smallest_nonzero_group_entry_magnitude': float(minimum),
            'coordinate_frame_group_link_max_abs_J': float(max(abs(j))),
            'first_frame_pair_CP_witness_index': witness,
            'frame_pair_CP_witness_J': js[witness],
            'exact_frame_pair_CP_witness_J': '-sqrt(3)/32',
            'CP_witness_up_down_frames': [encoded(U), encoded(D)],
            'scope': 'Complete finite orthogonal-axis branch census, not all nonorthogonal or other source extrema. Exact field arithmetic identifies projectors, orthogonality, generator action and frame orbits. Group links permute these frames, so all frame pairs include every link choice. The magnitude lower bound and witness J are exact; numerical magnitudes and the full J range are cross-checks.'}


def adjugate(matrix):
    """Polynomial adjugate, defined at singular links too."""
    L = np.asarray(matrix, complex)
    return np.array([[(-1)**(i+j)*np.linalg.det(np.delete(np.delete(L, j, axis=0), i, axis=1))
                      for j in range(3)] for i in range(3)])


def holomorphic_down_matching(K, source, mu=.8, md=1.3, g=.71, eta=.23, h=.57):
    """K and source are anti-triplet chiral backgrounds, not physical row fields.

    W includes D_u^T K D_d^c and the allowed degree-four reverse vertex
    eta*D_d^T adj(K) D_u^c. The corresponding Dirac row matrix is conjugated.
    """
    L, C = np.asarray(K).conj(), np.asarray(source).conj()
    M = np.block([[mu*np.eye(3), g*L], [eta*adjugate(L), md*np.eye(3)]])
    A = np.linalg.solve(M, np.vstack([np.zeros((3, 3)), C]))
    metric = np.eye(3) + A.conj().T@A
    vals, U = np.linalg.eigh(metric)
    ki = (U/np.sqrt(vals))@U.conj().T
    frame = np.vstack([np.eye(3), -A])@ki
    heavy = np.hstack([np.vstack([np.zeros((3, 3)), C]), M])
    assert np.max(abs(heavy@frame)) < 2e-12
    assert np.max(abs(frame.conj().T@frame-np.eye(3))) < 2e-12
    return {'Y': -h*A[:3]@ki, 'M': M, 'C': C, 'light_right_frame': frame}


def conditional_transmission():
    cp = json.loads((ROOT / 'receipts/m22_interactions/valentiner_cp.json').read_text())
    previous = json.loads((ROOT / 'receipts/m22_interactions/valentiner_link.json').read_text())
    X = np.array([[complex(s.sympify(t).evalf()) for t in row] for row in cp['unitary_CP_matrix']])
    W = np.array([[complex(*t) for t in row] for row in previous['CP_basis']])
    group = group_closure(generators())[0]
    G = numeric(group[previous['selected_link_element']])
    r = .1
    Cu, Cd = W@np.diag([.07, .31, .9]), W@np.diag([.08, .27, .85])
    Yu = canonical_mediator(.9*np.eye(3), Cu, h=.6)['Y']
    physical_link = r*G
    match = holomorphic_down_matching(physical_link.conj(), Cd.conj())
    cpL, cpC = X@physical_link.conj()@X.conj().T, X@Cd.conj()
    partner = holomorphic_down_matching(cpL.conj(), cpC.conj())
    a, b = mixing_record(Yu, match['Y']), mixing_record(Yu, partner['Y'])
    assert abs(a['J']+b['J']) < 2e-13 and abs(a['J']) > .01
    # Projectors transmit G exactly on a group-aligned link for orthogonal sources.
    _, V = np.linalg.eigh(match['Y']@match['Y'].conj().T)
    _, S = np.linalg.eigh(Cd@Cd.conj().T)
    assert np.max(abs(abs(V.conj().T@G@S)-np.eye(3))) < 2e-12
    free = []
    raw = np.array([[1., .3, .1], [.2, 1., .4], [.1, .15, 1.]])
    for t in (.8, 1., 1.2):
        background = W@raw@np.diag([.08, .27*t, .85])
        record = holomorphic_down_matching(physical_link.conj(), background.conj())
        free.append({'second_column_coupling': t, 'observables': mixing_record(Yu, record['Y'])})
    assert max(q['observables']['depth'] for q in free)-min(q['observables']['depth'] for q in free) > .1
    zero = holomorphic_down_matching(physical_link.conj(), np.zeros((3, 3)))['Y']
    assert np.max(abs(zero)) == 0
    return {'conditional_CP_pair': [a, b], 'free_source_column_cases': free,
            'self_consistent_source_zero_Y_norm': 0.,
            'scope': 'Off-vacuum background transmission checks using a previously selected group element and CP-real basis. The exact minimal scalar vacuum has zero sources, zero Yukawa matrices and no defined CKM frame.'}


def joint_breaking_vacuum(census):
    U, D = [np.array([[complex(*z) for z in row] for row in M])
            for M in census['CP_witness_up_down_frames']]
    L = .1*np.eye(3)
    # All six columns are individually group-rotated axis vacua; independent
    # real quark couplings multiply them. No nominated phase is used.
    Cu = .1*U@np.diag([.07, .31, .9])
    Cd = .1*D@np.diag([.08, .27, .85])
    Yu = canonical_mediator(.9*np.eye(3), Cu, h=.6)['Y']
    Yd = holomorphic_down_matching(L.conj(), Cd.conj())['Y']
    record = mixing_record(Yu, Yd)
    assert abs(record['J']-census['frame_pair_CP_witness_J']) < 2e-13
    cp = json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())
    X = np.array([[complex(s.sympify(x).evalf()) for x in row] for row in cp['unitary_CP_matrix']])
    Yucp = canonical_mediator(.9*np.eye(3), X@Cu.conj(), h=.6)['Y']
    Ydcp = holomorphic_down_matching((X@L.conj()@X.conj().T).conj(), (X@Cd.conj()).conj())['Y']
    partner = mixing_record(Yucp, Ydcp)
    assert abs(record['J']+partner['J']) < 2e-13
    Hu, Hd = Yu@Yu.conj().T, Yd@Yd.conj().T
    cpdet = float(np.linalg.det(Hu@Hd-Hd@Hu).imag)
    assert abs(cpdet) > 1e-32
    # Source F backgrounds induce scalar matter B terms. Positive universal
    # matter breaking mass larger than their operator norm suffices for stability.
    Bbound = .9*6*.1**5
    squark_mass_squared = 1e-4
    assert squark_mass_squared > Bbound
    up_rows = np.hstack([.9*np.eye(3), Cu.conj()])
    down_match = holomorphic_down_matching(L.conj(), Cd.conj())
    down_rows = np.hstack([down_match['M'].conj(), np.vstack([np.zeros((3, 3)), Cd.conj()])])
    matter_minima = []
    for rows, source_matrix, source_offset in ((up_rows, Cu, 0), (down_rows, Cd, 3)):
        left, right = rows.shape
        fermions = np.block([[np.zeros((left, left)), rows],
                             [rows.T, np.zeros((right, right))]])
        B = np.zeros_like(fermions)
        source_B = 6*.1**4*source_matrix.conj()
        B[source_offset:source_offset+3, -3:] = source_B
        B[-3:, source_offset:source_offset+3] = source_B.T
        hermitian = fermions.conj().T@fermions+squark_mass_squared*np.eye(left+right)
        real_mass = np.block([[hermitian, B.conj()], [B, hermitian.conj()]])
        mass_minimum = float(np.linalg.eigvalsh(real_mass)[0])
        assert mass_minimum >= squark_mass_squared-Bbound-2e-14
        matter_minima.append(mass_minimum)
    return {'CP_pair': [record, partner], 'commutator_determinant_imaginary': cpdet,
            'source_stationary_directions': 'Group-rotated axis columns in the retained up/down frames; chiral Phi=conjugate(physical columns).',
            'frame_selection': 'First enumerated orthogonal frame pair with nonzero J; a witness, not an energy preference.',
            'universal_quark_scalar_breaking_mass_squared': squark_mass_squared,
            'source_induced_matter_B_operator_norm_bound': Bbound,
            'matter_scalar_mass_squared_lower_bound': squark_mass_squared-Bbound,
            'computed_up_down_matter_scalar_minima': matter_minima,
            'Higgs_supersymmetric_mu': .2, 'positive_Higgs_breaking_mass_squared': 1e-4,
            'scope': 'Joint locally stable link/source branch with positive matter scalar masses and nonzero weak CP. No global vacuum selection, EW breaking, unique CP sign, realistic mass fit or golden relation.'}


def allowed_cross_response(census):
    """First-order stationary-vacuum response to an allowed scalar operator."""
    data = json.loads((ROOT/'receipts/m22_interactions/valentiner_invariants.json').read_text())
    x, y, z = s.symbols('x y z')
    f = s.sympify(data['sextic']['polynomial'], locals={'x': x, 'y': y, 'z': z})
    F = s.lambdify((x, y, z), f, 'numpy')
    gradF = s.lambdify((x, y, z), [s.diff(f, q) for q in (x, y, z)], 'numpy')
    U, D = [np.array([[complex(*z) for z in row] for row in M])
            for M in census['CP_witness_up_down_frames']]
    sources = [p for p in .1*U.T]+[p for p in .1*D.T]
    L = .1*np.eye(3)
    H = np.zeros((54, 54))
    basis9 = np.eye(9).reshape(9, 3, 3)
    WH = np.array([[.1**4*((8+2*.2)*np.trace(E)*np.trace(G)+72*np.trace(E@G))
                    for G in basis9] for E in basis9])
    Qm = WH.T@WH
    H[:9, :9] = H[9:18, 9:18] = Qm
    branch = source_breaking_branch()
    def V(phi):
        return (np.linalg.norm(gradF(*phi))**2-branch['tachyon_parameter_m2']*np.vdot(phi, phi).real
                +2*branch['holomorphic_breaking_A']*F(*phi).real)
    directions = np.vstack([np.eye(3), 1j*np.eye(3)])/np.sqrt(2)
    eps = 2e-6
    for k, p in enumerate(sources):
        h = np.array([[(V(p+eps*(E+G))-V(p+eps*(E-G))-V(p+eps*(-E+G))
                       +V(p-eps*(E+G)))/(4*eps*eps) for G in directions] for E in directions])
        assert np.linalg.eigvalsh(h)[0] > 5.39e-7
        H[18+6*k:24+6*k, 18+6*k:24+6*k] = h
    u, d = sources[0], sources[3]
    overlap = u.conj()@L@d
    Glink = overlap*np.outer(u, d.conj())
    Gu, Gd = overlap.conjugate()*(L@d), overlap*(L.conj().T@u)
    gradient = np.zeros(54)
    gradient[:9], gradient[9:18] = np.sqrt(2)*Glink.real.ravel(), np.sqrt(2)*Glink.imag.ravel()
    for index, g in ((0, Gu), (3, Gd)):
        gradient[18+6*index:24+6*index] = np.sqrt(2)*np.r_[g.real, g.imag]
    response = np.linalg.solve(H, -gradient)
    deltaL = (response[:9]+1j*response[9:18]).reshape(3, 3)/np.sqrt(2)
    delta_sources = [(response[18+6*k:21+6*k]+1j*response[21+6*k:24+6*k])/np.sqrt(2) for k in range(6)]
    B = abs(u.conj()@d)**2/.1**4
    tangential = Gu-u*(u.conj()@Gu)/np.vdot(u, u)
    assert abs(np.linalg.norm(tangential)**2-.1**4*.1**6*B*(1-B)) < 1e-24
    cases = []
    for strength in (-1e-6, 0., 1e-6):
        src = [p+strength*q for p, q in zip(sources, delta_sources)]
        Cu = np.column_stack(src[:3])@np.diag([.07, .31, .9])
        Cd = np.column_stack(src[3:])@np.diag([.08, .27, .85])
        Yu = canonical_mediator(.9*np.eye(3), Cu, h=.6)['Y']
        Yd = holomorphic_down_matching((L+strength*deltaL).conj(), Cd.conj())['Y']
        cases.append({'epsilon': strength, 'observables': mixing_record(Yu, Yd)})
    derivatives = {key: (cases[2]['observables'][key]-cases[0]['observables'][key])/(2e-6)
                   for key in ('J', 'depth', 'Vus', 'Vcb', 'Vub', 'delta_degrees')}
    assert abs(derivatives['depth']) > .01
    return {'operator': 'epsilon*|phi_u1^dagger L phi_d1|^2',
            'source_overlap_probability': float(B),
            'source_tangential_force_norm_squared_per_epsilon_squared': float(np.linalg.norm(tangential)**2),
            'minimum_54_real_flavor_Hessian_eigenvalue': float(np.linalg.eigvalsh(H)[0]),
            'linear_stationary_response_residual': float(np.max(abs(H@response+gradient))),
            'maximum_source_displacement_per_unit_epsilon': float(max(np.linalg.norm(z) for z in delta_sources)),
            'canonical_observable_first_derivatives': derivatives,
            'linear_continuation_cases': cases,
            'scope': 'Numerical implicit-function response using the full positive link/source Hessian. Cases are a first-order continuation, not newly minimized finite-epsilon vacua or experimental uncertainty. The counterterm is permitted by family, shaping and CP symmetries.'}


def main():
    derivatives = exact_tensor_derivatives()
    source = source_critical_locus()
    # No selected mixing coefficient or phase enters the link-vacuum parameters.
    branches = [link_branch(-.0324, b, c) for b, c in ((.5, .2), (1., .2), (1.5, .2), (1., -.1))]
    assert all(r['isolated_link_minimum'] for r in branches)
    r = branches[1]['real_radius']
    assert abs(r-.1) < 2e-16
    group = group_closure(generators())[0]
    matrices = [numeric(g) for g in group]
    # For real CP-compatible coefficients r^3 is real. Its three phases differ
    # by a center element, and the group vacua constitute ONE family orbit.
    omega = np.exp(2j*np.pi/3)
    cp_phase_compensation = []
    for k in range(3):
        z = r*omega**k
        compensation = z/z.conjugate()
        assert abs(compensation**3-1) < 2e-14
        assert abs(compensation*z.conjugate()-z) < 2e-14
        cp_phase_compensation.append([float(compensation.real), float(compensation.imag)])
    _, link, norm = coefficient_functions()
    assert max(abs(link(g)-norm) for g in matrices) < 3e-11
    census = orthogonal_axis_census()
    result = {'schema': 'pp-valentiner-susy-vacua/1',
              'canonical_scalar_superpotential': 'W=a*det(K)+b*I6bar(K)+c*det(K)^2+sum_i kappa_i*F6bar(Phi_i)',
              'family_group': '3.A6_u x 3.A6_d',
              'chiral_link': '(3bar_u,3_d)', 'physical_Dirac_link': 'L=conjugate(K)',
              'six_source_fields': 'three (3bar_u,1), three (1,3bar_d), each with its own C6 charge',
              'all_scalar_holomorphic_contractions_through_degree_six': 9,
              'scalar_sector_scope': 'Link and six source flavons; no extra driving fields, canonical Kahler potential, no soft breaking, matter and Higgs scalar backgrounds zero. Independent nonzero source coefficients.',
              'derivatives': derivatives, 'source_obstruction': source,
              'group_branch': 'r^3=-a/(32*b+2*c), K=r*conjugate(R(g))',
              'group_branch_stability_conditions': 'a!=0, 32*b+2*c!=0, b!=0, 16*b+c!=0',
              'coupling_variations': branches,
              'group_branch_family_orbits': 1,
              'CP_phase_center_compensations': cp_phase_compensation,
              'group_link_only_CP_is_unbroken_up_to_family': True,
              'complete_classification_of_all_link_F_flat_vacua': False,
              'higher_invariant_deformations': 'A nonsingular group branch persists locally: its diagonal-group fixed subspace is scalar matrices, and the singlet implicit-function derivative is nonzero. This is not a guarantee of global selection or stability under large deformations.',
              'quark_superpotential': 'h_u Q.H_u U^c+mu_u U.U^c+sum_i lambda_ui u_i^c Phi_ui^T U + h_d Q.H_d D_u^c+mu D_u.D_u^c+md D_d.D_d^c+g D_u^T K D_d^c+sum_i lambda_di d_i^c Phi_di^T D_d+eta D_d^T adj(K) D_u^c',
              'reverse_vertex_degree': 4, 'reverse_vertex_has_independent_coefficient': True,
              'quark_scope': 'Specified holomorphic interaction with canonical tree matching, matter parity and baryon conservation. The degree-four cofactor vertex is retained; a complete higher-degree quark EFT operator census and UV completion are not claimed.',
              'spurion_breaking_source_branches': [source_breaking_branch(t=t) for t in (-26., -24., -22.)],
              'orthogonal_axis_census': census,
              'joint_breaking_vacuum': joint_breaking_vacuum(census),
              'allowed_cross_sector_response': allowed_cross_response(census),
              'transmission': conditional_transmission(),
              'conclusion': 'Stable discrete link alignment is derived on a locally isolated F-flat branch. Exact SUSY forces zero sources. Specified spurion breaking gives locally stable nonzero source vacua and physical weak CP, but every orthogonal axis branch fails the CKM magnitude hierarchy. No golden relation or unique physical phase is predicted.'}
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('transmission',)}, indent=2), flush=True)


if __name__ == '__main__':
    main()
