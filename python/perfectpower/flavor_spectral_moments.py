"""Exact weak-basis spectral moments and mixing probabilities.

Inputs are distinct squared source spectra and invariant moments. No CKM
targets are inferred or supplied by this arithmetic transformation.
"""
from fractions import Fraction as Q


def _spectra(values):
    if len(values) != 3:
        raise ValueError('three spectral values required')
    if any(isinstance(x, float) for x in values):
        raise ValueError('exact rational spectral values required')
    v = tuple(map(Q, values))
    if len(set(v)) != 3:
        raise ValueError('distinct squared spectra required; degeneracy leaves frame freedom')
    return v


def lagrange_rows(values):
    values = _spectra(values)
    rows = []
    for i, a in enumerate(values):
        b, c = [x for j, x in enumerate(values) if j != i]
        den = (a-b)*(a-c)
        rows.append([b*c/den, -(b+c)/den, 1/den])
    assert all(sum(rows[i][r]*a**r for r in range(3)) == int(i == j)
               for i in range(3) for j, a in enumerate(values))
    return rows


def moments(up, down, probabilities):
    up, down = _spectra(up), _spectra(down)
    p = [[Q(x) for x in row] for row in probabilities]
    if len(p) != 3 or any(len(row) != 3 for row in p):
        raise ValueError('three-by-three probabilities required')
    return [[sum(up[i]**r*down[j]**s*p[i][j] for i in range(3) for j in range(3))
             for s in range(3)] for r in range(3)]


def recover(up, down, invariant_moments):
    L, R = lagrange_rows(up), lagrange_rows(down)
    M = [[Q(x) for x in row] for row in invariant_moments]
    if len(M) != 3 or any(len(row) != 3 for row in M):
        raise ValueError('three-by-three moments required')
    P = [[sum(L[i][r]*M[r][s]*R[j][s] for r in range(3) for s in range(3))
          for j in range(3)] for i in range(3)]
    assert moments(up, down, P) == M
    return P


def jarlskog_squared(probabilities):
    """Exact unistochastic boundary for a doubly stochastic 3x3 matrix."""
    P = [[Q(x) for x in row] for row in probabilities]
    if len(P) != 3 or any(len(row) != 3 for row in P):
        raise ValueError('three-by-three probabilities required')
    if any(x < 0 for row in P for x in row):
        raise ValueError('negative mixing probability')
    if any(sum(row) != 1 for row in P) or any(sum(P[i][j] for i in range(3)) != 1 for j in range(3)):
        raise ValueError('doubly stochastic matrix required')
    x, y, z = [P[0][i]*P[1][i] for i in range(3)]
    return x*y-(z-x-y)**2/4


def probability_chart(a, b, c, d):
    a, b, c, d = map(Q, (a, b, c, d))
    return [[a, b, 1-a-b], [c, d, 1-c-d],
            [1-a-c, 1-b-d, a+b+c+d-1]]


def su3_orientation(vector):
    a, b, c, d, e, f, g = map(Q, vector)
    if b or e != f or f != g:
        raise ValueError('SU3 restriction required')
    # Exact identities in the normalization of the source operator table.
    return {'radial_self': str(a), 'norm_product': str(c-d/3+11*e/40),
            'trace_AB_squared': str(e), 'trace_A2B2': str(d-6*e/5),
            'scope': 'V=a(Nu^2+Nd^2)+norm_product*Nu*Nd+h(Tr AB)^2+L Tr(A^2 B^2)'}


def alignment_rank(up, down, vector):
    """Exact number of available orientation directions in the SU3 quartic.

    An open CP-violating chart has four independent probabilities. At a
    stationary point the rank-one Hessian leaves at least three directions.
    This is a local exact obstruction, not a classification of boundary vacua.
    """
    import sympy as s
    up, down = _spectra(up), _spectra(down)
    o = su3_orientation(vector)
    h, L = Q(o['trace_AB_squared']), Q(o['trace_A2B2'])
    def gradients(u, v):
        return [(u[i]-u[2])*(v[j]-v[2]) for i, j in ((0,0),(0,1),(1,0),(1,1))]
    w, z = gradients(up, down), gradients([x*x for x in up], [x*x for x in down])
    independent = s.Matrix([[s.Rational(x) for x in w], [s.Rational(x) for x in z]]).rank()
    assert independent == 2
    H = s.Matrix([[2*s.Rational(h)*s.Rational(x)*s.Rational(y) for y in w] for x in w])
    return {'linear_moment_gradient_rank': independent, 'orientation_hessian_rank': H.rank(),
            'flat_probability_directions_at_stationarity': 4-H.rank(),
            'isolated_CP_violating_stationary_point_possible': False,
            'reason': 'independent moment gradients force L=0 at an interior stationary point; its Hessian then has rank at most one',
            'L': str(L), 'h': str(h)}
