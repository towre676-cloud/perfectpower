"""Exact rational WZ identities in Q(n)(k), and bounded certificate search.

This checks the interior shift identity. Support and endpoint cancellation
must be established separately before concluding a summation identity.
"""
from .rational_functions import RationalFunction as RF, AlgebraBudget, solve_many
from . import field_polynomials as F
from .divisor_square import WorkLimit


class ShiftFraction:
    def __init__(self, packet, budget=None):
        if not isinstance(packet, dict) or set(packet) != {'numerator', 'denominator'}:
            raise ValueError('outer k numerator/denominator required')
        self.budget = budget or AlgebraBudget(degree_limit=128)
        if any(not isinstance(packet[k], (list, tuple)) or not 1 <= len(packet[k]) <= 33 for k in packet):
            raise WorkLimit('outer k degree budget exceeded')
        n, d = ([RF.parse(v, self.budget) for v in packet[k]] for k in ('numerator', 'denominator'))
        if not any(d):
            raise ValueError('nonzero k denominator required')
        g, _, _ = F.extended_gcd(n, d)
        n, d = F.divide(n, g)[0], F.divide(d, g)[0]
        lead = d[-1]; self.n, self.d = F.scale(n, 1/lead), F.scale(d, 1/lead)

    def packet(self):
        return {'numerator': [v.packet() for v in self.n], 'denominator': [v.packet() for v in self.d]}

    def _new(self, n, d):
        return ShiftFraction({'numerator': n, 'denominator': d}, self.budget)

    def __add__(self, other):
        return self._new(F.add(F.product(self.n, other.d), F.product(other.n, self.d)), F.product(self.d, other.d))

    def __neg__(self):
        return self._new(F.scale(self.n, -1), self.d)

    def __sub__(self, other):
        return self+-other

    def __mul__(self, other):
        return self._new(F.product(self.n, other.n), F.product(self.d, other.d))

    def shift_k(self):
        return self._new(F.shift(self.n, self.n[0].coerce(1)), F.shift(self.d, self.d[0].coerce(1)))

    def is_zero(self):
        return not any(self.n)


def check_wz_identity(n_ratio, k_ratio, certificate):
    """F(n+1,k)/F=r_n, F(n,k+1)/F=r_k, G=R*F."""
    budget = AlgebraBudget(degree_limit=128)
    rn, rk, r = (ShiftFraction(p, budget) for p in (n_ratio, k_ratio, certificate))
    one = ShiftFraction({'numerator': [1], 'denominator': [1]}, budget)
    delta = rn-one-(rk*r.shift_k()-r)
    return {'schema': 'pp-wz-identity/1', 'valid': delta.is_zero(),
            'n_ratio': rn.packet(), 'k_ratio': rk.packet(), 'certificate': r.packet(),
            'cross_residual': [v.packet() for v in delta.n],
            'boundary_conditions_proved': False,
            'scope': 'r_n-1 = r_k R(n,k+1)-R(n,k) as a rational identity, wherever the supplied terms and ratios are defined',
            'execution_verified': False}


def discover_wz(n_ratio, k_ratio, denominator, degree=2):
    """Solve a supplied denominator ansatz R=P(k)/D(k), degree(P)<=degree.

    Failure is only failure of this ansatz; it is not nonexistence of a WZ mate.
    """
    if type(degree) is not int or not 0 <= degree <= 8:
        raise ValueError('certificate numerator degree 0 through 8 required')
    budget = AlgebraBudget(degree_limit=128)
    rn, rk = ShiftFraction(n_ratio, budget), ShiftFraction(k_ratio, budget)
    one = ShiftFraction({'numerator': [1], 'denominator': [1]}, budget)
    rhs = rn-one
    cols = []
    for j in range(degree+1):
        r = ShiftFraction({'numerator': [0]*j+[1], 'denominator': denominator}, budget)
        cols.append(rk*r.shift_k()-r)
    # Clear a common outer denominator, retaining exact Q(n) coefficients.
    common = [RF([1], budget=budget)]
    for v in cols+[rhs]:
        g, _, _ = F.extended_gcd(common, v.d)
        common = F.product(common, F.divide(v.d, g)[0])
        if len(common) > 129:
            raise WorkLimit('WZ ansatz denominator budget exceeded')
    polys = [F.product(v.n, F.divide(common, v.d)[0]) for v in cols+[rhs]]
    length = max(map(len, polys)); zero = RF([0], budget=budget)
    padded = [p+[zero]*(length-len(p)) for p in polys]
    solution = solve_many([list(row) for row in zip(*padded[:-1])], [[v] for v in padded[-1]])
    if solution is None:
        return {'status': 'ANSATZ_UNRESOLVED', 'degree': degree, 'execution_verified': False}
    cert = ShiftFraction({'numerator': [r[0] for r in solution], 'denominator': denominator}, budget)
    packet = check_wz_identity(n_ratio, k_ratio, cert.packet())
    if not packet['valid']:
        raise AssertionError('discovered WZ identity failed exact replay')
    return dict(packet, status='EXACT_INTERIOR_CERTIFICATE', degree=degree)
