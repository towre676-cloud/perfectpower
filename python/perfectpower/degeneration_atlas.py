"""Collision strata and real ordered branch chambers, with exact invariants.

Normalized collision polynomials, singular curves and stable limits are distinct.
General stable admissible-cover construction is intentionally not inferred from
the collision partitions. The Legendre endpoints include explicit node data.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import comb, gcd
from . import polyalg as P
from .core import mul
from .connection_polytope import exact


def normalized_cover(multiplicities, d):
    xs = tuple(multiplicities)
    if type(d) is not int or not 2 <= d <= 64 or any(type(r) is not int or r < 1 for r in xs):
        raise ValueError('power 2..64 and positive integer multiplicities required')
    c = d
    for r in xs:
        c = gcd(c, r)
    e, reduced = d // c, [r // c for r in xs]
    finite = sum(e - gcd(e, r) for r in reduced)
    infinity = e - gcd(e, sum(reduced))
    chi = 2 * e - finite - infinity
    if chi > 2 or (2 - chi) % 2:
        raise AssertionError('invalid normalized-cover Euler number')
    g = (2 - chi) // 2
    return {'power': d, 'multiplicities': list(xs), 'components': c,
            'cover_degree_per_component': e, 'genus_per_component': g,
            'genus_sum': c * g, 'euler_total': c * chi,
            'betti': [c, 2 * c * g, c], 'curvature_over_pi': 2 * c * chi,
            'trivalent_face_charge': 6 * c * chi,
            'finite_ramification_per_component': finite,
            'infinity_ramification_per_component': infinity,
            'infinity_points_per_component': gcd(e, sum(reduced)),
            'formalized': False}


def partitions(n):
    """Every labelled set partition exactly once, in restricted-growth order."""
    if type(n) is not int or not 0 <= n <= 8:
        raise ValueError('labelled partition enumeration requires 0..8 roots')
    def rec(i, blocks):
        if i == n:
            yield tuple(tuple(b) for b in blocks)
            return
        for j in range(len(blocks)):
            yield from rec(i + 1, [b + [i] if k == j else b for k, b in enumerate(blocks)])
        yield from rec(i + 1, blocks + [[i]])
    yield from rec(0, [])


def collision_atlas(multiplicities, d):
    xs = tuple(multiplicities)
    original = normalized_cover(xs, d)
    rows = []
    for blocks in partitions(len(xs)):
        merged = [sum(xs[i] for i in block) for block in blocks]
        p = normalized_cover(merged, d)
        rows.append({'blocks': [list(b) for b in blocks], 'cluster_voltages': [r % d for r in merged],
                     'normalization': p, 'euler_change': p['euler_total'] - original['euler_total']})
    return {'schema': 'pp-collision-atlas/1', 'original': original, 'strata': rows,
            'stratum_count': len(rows), 'formalized': False,
            'scope': 'normalization of colliding-root polynomials; general stable limits not constructed'}


def crosses(a, b):
    i, j = a
    k, l = b
    return i < k < j < l or k < i < l < j


def associahedron(n):
    """Face poset of the compactified fixed cyclic-order real M_0,n chamber."""
    if type(n) is not int or not 4 <= n <= 9:
        raise ValueError('associahedron enumeration supports 4..9 marked points')
    diagonals = [(i, j) for i in range(n) for j in range(i + 2, n) if (i, j) != (0, n - 1)]
    compatible = [()]
    for k in range(1, n - 2):
        for ds in combinations(diagonals, k):
            if not any(crosses(a, b) for a, b in combinations(ds, 2)):
                compatible.append(ds)
    faces = []
    dimension = n - 3
    for ds in compatible:
        faces.append({'diagonals': [list(d) for d in ds], 'dimension': dimension - len(ds),
                      'codimension': len(ds),
                      'boundary_faces': [list(d) for d in diagonals if d not in ds and not any(crosses(d, a) for a in ds)],
                      'collision_splits': [{'left': list(range(i, j)),
                                           'right': [k for k in range(n) if k not in range(i, j)]}
                                          for i, j in ds]})
    vector = [sum(f['dimension'] == k for f in faces) for k in range(dimension + 1)]
    euler = sum((-1) ** k * v for k, v in enumerate(vector))
    boundary_euler = sum((-1) ** k * vector[k] for k in range(dimension))
    if euler != 1 or boundary_euler != 1 + (-1) ** (dimension - 1):
        raise AssertionError('polytope Euler identity failed')
    return {'schema': 'pp-associahedron/1', 'marked_points': n, 'dimension': dimension,
            'f_vector': vector, 'euler_closed_polytope': euler,
            'euler_boundary': boundary_euler, 'faces': faces,
            'triangulations': vector[0], 'formalized': False,
            'scope': 'labelled real chamber face poset; no intrinsic metric or generic amplituhedron'}


def legendre(parameter, series_terms=16):
    lam = exact(parameter)
    if type(series_terms) is not int or not 1 <= series_terms <= 4096:
        raise ValueError('series terms must be 1..4096')
    endpoint = lam in (0, 1)
    profile = normalized_cover([2, 1] if endpoint else [1, 1, 1], 2)
    series = [Q(comb(2 * n, n) ** 2, 16 ** n) for n in range(series_terms)]
    for n in range(series_terms - 1):
        if (n + 1) ** 2 * series[n + 1] != (Q(n) + Q(1, 2)) ** 2 * series[n]:
            raise AssertionError('Picard-Fuchs coefficient identity failed')
    out = {'schema': 'pp-legendre/1', 'parameter': str(lam),
           'coefficients': list(map(str, [0, lam, -1 - lam, 1])),
           'polynomial_discriminant': str(lam ** 2 * (1 - lam) ** 2),
           'elliptic_discriminant': str(16 * lam ** 2 * (1 - lam) ** 2),
           'normalization': profile, 'in_positive_chamber': 0 < lam < 1,
           'canonical_form_coefficient': None if endpoint else str(1 / (lam * (1 - lam))),
           'picard_fuchs': {'order_two': ['0', '1', '-1'], 'order_one': ['1', '-2'], 'order_zero': ['-1/4']},
           'normalized_period_series': list(map(str, series)),
           'series_scope': 'formal series at 0 for 2F1(1/2,1/2;1;lambda), not endpoint evaluation',
           'parameter_monodromy_convention': {'around_0': [[1, 2], [0, 1]], 'around_1': [[1, 0], [-2, 1]],
                                            'scope': 'standard marked-period convention; distinct from fibre sheet monodromy'},
           'formalized': False}
    if endpoint:
        out['singular_limit'] = {'type': 'irreducible nodal cubic', 'arithmetic_genus': 1,
                                 'singular_euler': 1, 'normalization_euler': 2,
                                 'dual_graph': {'vertices': 1, 'loop_edges': 1, 'first_betti': 1},
                                 'vanishing_cycles': 1,
                                 'normalization_map': 'x=v^2+1, y=x*v' if lam == 0 else 'x=v^2, y=(x-1)*v',
                                 'node_preimages': 'v=+i,-i' if lam == 0 else 'v=+1,-1'}
    return out


def interval_form(a, b, x):
    a, b, x = map(exact, (a, b, x))
    if a >= b or x in (a, b):
        raise ValueError('ordered interval and nonendpoint evaluation required')
    return (b - a) / ((x - a) * (b - x))


def ordered_branch_form(coordinates):
    """Gauge-fixed real M_0,n Parke-Taylor form, marks 0,z...,1,infinity.

    Its stable compactification is associahedral; the open coordinate region
    alone is a simplex. Blowups expose the extra collision boundary divisors.
    """
    zs = tuple(map(exact, coordinates))
    if not 1 <= len(zs) <= 6 or not all(a < b for a, b in zip((Q(0),)+zs, zs+(Q(1),))):
        raise ValueError('1..6 strictly ordered rational coordinates in (0,1) required')
    gaps = [b-a for a,b in zip((Q(0),)+zs,zs+(Q(1),))]
    denominator = Q(1)
    for gap in gaps:denominator *= gap
    return {'marked_points':len(zs)+3,'coordinates':list(map(str,zs)),
            'coefficient':str(1/denominator),'wedge_order':'increasing coordinate labels',
            'formula':'dz_1 wedge ... wedge dz_r / (z_1*(z_2-z_1)*...*(1-z_r))',
            'formalized':False,'scope':'ordered real branch chamber canonical form'}


def pentagon_collision_chart(u, t):
    """Blowup x=t*u,y=t exposes the two-mark collision divisor t=0."""
    u,t=exact(u),exact(t)
    if not 0<u<1 or not 0<t<1:
        raise ValueError('chart coordinates must lie in (0,1)')
    source=Q(ordered_branch_form([t*u,t])['coefficient'])
    pullback=source*t  # dx wedge dy = t du wedge dt
    residue=1/(u*(1-u))
    if pullback != residue/(t*(1-t)):
        raise AssertionError('collision residue factorization failed')
    return {'map':{'x':str(t*u),'y':str(t)},'wedge_order':'du wedge dt',
            'pullback_coefficient':str(pullback),'boundary_residue_coefficient':str(residue),
            'identity':'Omega_5=du wedge dt/[u*(1-u)*t*(1-t)]',
            'boundary':'t=0, residue up to boundary orientation is Omega_4(u)',
            'formalized':False}


def descartes_variations(coefficients, a, b):
    """Descartes bound on open (a,b) after x=(a+b*t)/(1+t)."""
    f, a, b = P.poly(map(exact, coefficients)), exact(a), exact(b)
    if P.is_zero(f) or a >= b:
        raise ValueError('nonzero polynomial and ordered rational endpoints required')
    n, transformed = P.degree(f), P.ZERO
    for i, coefficient in enumerate(f):
        left, right = P.ONE, P.ONE
        for _ in range(i):
            left = mul(left, (a, b))
        for _ in range(n - i):
            right = mul(right, (Q(1), Q(1)))
        transformed = P.add(transformed, P.scale(mul(left, right), coefficient))
    signs = [1 if c > 0 else -1 for c in transformed if c]
    variations = sum(x != y for x, y in zip(signs, signs[1:]))
    return {'interval': [str(a), str(b)], 'transformed': list(map(str, transformed)),
            'variations': variations, 'root_count_upper_bound': variations,
            'exact_root_count': variations if variations <= 1 else None,
            'scope': 'open interval, multiplicities counted; endpoint roots excluded'}


def triangle_canonical(a, b, c=1):
    a, b, c = map(exact, (a, b, c))
    if min(a, b, c) <= 0:
        raise ValueError('positive rational conductances required')
    det = 4 * a * b + 2 * a * c + 2 * b * c
    q = [2 * b * c / det, 2 * a * c / det, 4 * a * b / det]
    # Quotient derivatives with c fixed. The Jacobian identity is exact.
    da, db = 4 * b + 2 * c, 4 * a + 2 * c
    jac = (-2*b*c*da / det**2) * (-2*a*c*db / det**2) - ((2*c*det-2*b*c*db) / det**2) * ((2*c*det-2*a*c*da) / det**2)
    coefficient = jac / (q[0] * q[1] * q[2])
    if coefficient != 1 / (a * b):
        raise AssertionError('canonical dlog pullback failed')
    return {'determinant': str(det), 'simplex_coordinates': list(map(str, q)),
            'edge_marginals': list(map(str, [1-z for z in q])),
            'canonical_form_pullback': str(coefficient), 'coordinates': 'da wedge db, c fixed',
            'identity': 'Omega_triangle pulls back to da wedge db/(a*b)', 'formalized': False}
