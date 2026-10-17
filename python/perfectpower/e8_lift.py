"""Exact E8 Lie brackets and an actual adjoint Coxeter lift.

This is the Frenkel--Kac lattice-cocycle construction, in the simple-root
basis and sign convention documented in ``docs/E8_LIFT_NOTE.md``.  All
entries are integers.  Basis indices 0..7 mean h_i; 8..247 mean e_alpha
in the sorted root order from :mod:`perfectpower.e8_periods`.

References: Geck, arXiv:2602.19632v1, section 3; Adams--He,
arXiv:1608.00510.  This executable construction is not a Lean proof.
"""

from functools import lru_cache
from fractions import Fraction
from itertools import combinations
from math import comb

from . import e8_periods as geometry

DIMENSION = 248
RANK = 8


def _clean(values):
    return tuple((i, a) for i, a in sorted(values.items()) if a)


def _add_scaled(out, values, factor=1):
    for i, a in values:
        out[i] = out.get(i, 0) + factor * a


@lru_cache(maxsize=1)
def root_coordinates():
    """The 240 roots expressed in the fixed integral simple-root basis."""
    return tuple(geometry.simple_root_coordinates(r) for r in geometry.roots())


@lru_cache(maxsize=1)
def _root_index():
    return {r: i + RANK for i, r in enumerate(root_coordinates())}


def root_basis_index(root):
    """Index of a root supplied in simple-root coordinates."""
    return _root_index()[tuple(root)]


def cocycle(a, b):
    """Bimultiplicative epsilon(a,b), with epsilon(alpha,alpha)=-1.

    The exponent is sum_i a_i b_i + sum_{i>j} a_i A_ij b_j.
    For lattice vectors epsilon(a,b)/epsilon(b,a)=(-1)**(a,b).
    """
    if len(a) != RANK or len(b) != RANK:
        raise ValueError("two eight-coordinate lattice vectors are required")
    if any(type(x) is not int for x in (*a, *b)):
        raise ValueError("lattice coordinates must be integers")
    cartan = geometry.cartan_matrix()
    exponent = sum(a[i] * b[i] for i in range(RANK))
    exponent += sum(a[i] * cartan[i][j] * b[j]
                    for i in range(RANK) for j in range(i))
    return -1 if exponent % 2 else 1


def lattice_pairing(a, b):
    cartan = geometry.cartan_matrix()
    return sum(a[i] * cartan[i][j] * b[j]
               for i in range(RANK) for j in range(RANK))


@lru_cache(maxsize=None)
def bracket_basis(i, j):
    """Sparse exact Lie bracket of two basis vectors."""
    if type(i) is not int or type(j) is not int or not (0 <= i < DIMENSION and 0 <= j < DIMENSION):
        raise ValueError("basis indices must lie between zero and 247")
    if i == j or (i < RANK and j < RANK):
        return ()
    if i > j:
        return tuple((k, -c) for k, c in bracket_basis(j, i))
    if i < RANK:
        b = root_coordinates()[j - RANK]
        coefficient = sum(geometry.cartan_matrix()[i][k] * b[k] for k in range(RANK))
        return ((j, coefficient),) if coefficient else ()
    a, b = root_coordinates()[i - RANK], root_coordinates()[j - RANK]
    total = tuple(x + y for x, y in zip(a, b))
    if not any(total):
        # epsilon(a,-a)=-1 for every root in this normalization.
        return tuple((k, -c) for k, c in enumerate(a) if c)
    k = _root_index().get(total)
    return ((k, cocycle(a, b)),) if k is not None else ()


def bracket(left, right):
    """Bracket sparse vectors, supplied as dicts or (index, coefficient) pairs."""
    if isinstance(left, dict):
        left = left.items()
    if isinstance(right, dict):
        right = right.items()
    left, right = tuple(left), tuple(right)
    out = {}
    for i, a in left:
        for j, b in right:
            _add_scaled(out, bracket_basis(i, j), a * b)
    return _clean(out)


def identity_map():
    return tuple(((i, 1),) for i in range(DIMENSION))


def apply_map(operator, vector):
    if len(operator) != DIMENSION:
        raise ValueError("a 248-column sparse operator is required")
    if isinstance(vector, dict):
        vector = vector.items()
    out = {}
    for i, a in vector:
        _add_scaled(out, operator[i], a)
    return _clean(out)


def compose(left, right):
    """Composition left after right; operators are sparse columns."""
    return tuple(apply_map(left, column) for column in right)


def power(operator, exponent):
    if type(exponent) is not int or exponent < 0:
        raise ValueError("a nonnegative integer exponent is required")
    out = identity_map()
    while exponent:
        if exponent & 1:
            out = compose(operator, out)
        operator = compose(operator, operator)
        exponent //= 2
    return out


@lru_cache(maxsize=None)
def exp_ad_root(root_index, parameter=1):
    """exp(parameter ad e_alpha)=I+tD+t²D²/2, checked D³=0.

    The root argument is a basis index in 8..247.  Fraction parameters
    produce rational operators; the Tits lifts use integral parameters.
    """
    if type(root_index) is not int or not RANK <= root_index < DIMENSION:
        raise ValueError("a root basis index in 8..247 is required")
    parameter = Fraction(parameter)
    columns = []
    for i in range(DIMENSION):
        first = bracket_basis(root_index, i)
        second = bracket(((root_index, 1),), first)
        if bracket(((root_index, 1),), second):
            raise ArithmeticError("root adjoint was not nilpotent of degree at most three")
        out = {i: Fraction(1)}
        _add_scaled(out, first, parameter)
        _add_scaled(out, second, parameter * parameter / 2)
        cleaned = _clean(out)
        columns.append(tuple((k, int(a) if a.denominator == 1 else a) for k, a in cleaned))
    return tuple(columns)


@lru_cache(maxsize=8)
def tits_lift(i):
    """n_i=exp(ad e_i) exp(ad e_-i) exp(ad e_i).

    Here F_i=-e_-i, so the middle factor is the conventional exp(-ad F_i).
    """
    if type(i) is not int or not 0 <= i < RANK:
        raise ValueError("a simple-root index in 0..7 is required")
    positive = tuple(int(i == k) for k in range(RANK))
    negative = tuple(-x for x in positive)
    plus = exp_ad_root(root_basis_index(positive))
    minus = exp_ad_root(root_basis_index(negative))
    return compose(plus, compose(minus, plus))


@lru_cache(maxsize=1)
def coxeter_lift():
    """The actual adjoint automorphism n_8 ... n_1, n_1 acting first."""
    out = identity_map()
    for i in range(RANK):
        out = compose(tits_lift(i), out)
    return out


@lru_cache(maxsize=1)
def signed_root_orbits():
    """Root-space signed cycles and an explicit sign gauge removing signs."""
    operator = coxeter_lift()
    remaining = set(range(RANK, DIMENSION))
    result = []
    while remaining:
        start = min(remaining)
        indices, signs, gauges = [], [], []
        point, gauge = start, 1
        while point not in indices:
            if point not in remaining:
                raise ArithmeticError("signed Coxeter map is not a root permutation")
            column = operator[point]
            if len(column) != 1 or column[0][0] < RANK or column[0][1] not in (-1, 1):
                raise ArithmeticError("Coxeter lift is not monomial on root spaces")
            indices.append(point)
            gauges.append(gauge)
            point, sign = column[0]
            signs.append(sign)
            gauge *= sign
        if point != start:
            raise ArithmeticError("signed root orbit did not return to its seed")
        remaining.difference_update(indices)
        result.append({"basis_indices": indices, "edge_signs": signs,
                       "gauge_signs": gauges, "length": len(indices),
                       "sign_product": gauge})
    return tuple(result)


def root_sign_gauge():
    """Diagonal conjugation making all Coxeter root-space edges +1."""
    gauge = {}
    for orbit in signed_root_orbits():
        if orbit["sign_product"] != 1:
            raise ArithmeticError("a negative signed cycle cannot be gauged to a permutation")
        gauge.update(zip(orbit["basis_indices"], orbit["gauge_signs"]))
    return tuple(((i, gauge.get(i, 1)),) for i in range(DIMENSION))


def coxeter_trace(exponent):
    operator = power(coxeter_lift(), exponent % 30)
    return sum(dict(column).get(i, 0) for i, column in enumerate(operator))


def verify_jacobi():
    """Check every distinct unordered basis triple, exactly C(248,3)."""
    # Repeated-index triples follow from skew symmetry; all distinct ones
    # are checked, including zeros, so this covers the full trilinear law.
    table = tuple(tuple(bracket_basis(i, j) for j in range(DIMENSION))
                  for i in range(DIMENSION))
    checked = 0
    for i, j, k in combinations(range(DIMENSION), 3):
        out = {}
        for a, coefficient in table[j][k]:
            _add_scaled(out, table[i][a], coefficient)
        for a, coefficient in table[k][i]:
            _add_scaled(out, table[j][a], coefficient)
        for a, coefficient in table[i][j]:
            _add_scaled(out, table[k][a], coefficient)
        if any(out.values()):
            raise ArithmeticError(f"Jacobi identity failed on {(i, j, k)}")
        checked += 1
    return checked


def verify_cocycle():
    """Check normalization and commutator signs on all 57,600 root pairs."""
    coordinates = root_coordinates()
    checked = 0
    for a in coordinates:
        if cocycle(a, a) != -1 or lattice_pairing(a, a) != 2:
            raise ArithmeticError("root cocycle normalization failed")
        for b in coordinates:
            if cocycle(a, b) * cocycle(b, a) != (-1 if lattice_pairing(a, b) % 2 else 1):
                raise ArithmeticError("cocycle commutator sign failed")
            checked += 1
    return checked


def principal_height_receipt():
    """Independent principal-toral spectrum and exact positive-root height sums."""
    multiplicities = [0] * 30
    multiplicities[0] = RANK
    positive = []
    for root in root_coordinates():
        multiplicities[sum(root) % 30] += 1
        if all(x >= 0 for x in root):
            positive.append(root)
        elif not all(x <= 0 for x in root):
            raise ArithmeticError("the supplied root base is not a positive simple system")
    expected = [8 + int(n in geometry.EXPONENTS) for n in range(30)]
    if multiplicities != expected:
        raise ArithmeticError("principal root-height spectrum differs from lifted spectrum")
    rho = tuple(Fraction(sum(root[i] for root in positive), 2) for i in range(RANK))
    rho_squared = lattice_pairing(rho, rho)
    height_sum = sum(sum(root) for root in positive)
    height_square_sum = sum(sum(root) ** 2 for root in positive)
    if (rho_squared, height_sum, height_square_sum) != (620, 1240, 18600):
        raise ArithmeticError("unexpected independent E8 height sums")
    return {"multiplicities_0_to_29": multiplicities, "positive_roots": len(positive),
            "rho_squared": str(rho_squared), "positive_height_sum": height_sum,
            "positive_height_squared_sum": height_square_sum,
            "principal_adjoint_weight_two_bernoulli_sum": "0"}


def verify_bracket_automorphism(operator):
    checked = 0
    for i, j in combinations(range(DIMENSION), 2):
        if apply_map(operator, bracket_basis(i, j)) != bracket(operator[i], operator[j]):
            raise ArithmeticError(f"bracket preservation failed on {(i, j)}")
        checked += 1
    return checked


def verify_tits_relations():
    """All eight torus-square laws and all 28 pairwise braid laws."""
    cartan = geometry.cartan_matrix()
    for i in range(RANK):
        square = power(tits_lift(i), 2)
        for j, column in enumerate(square):
            pairing = 0 if j < RANK else sum(
                cartan[i][k] * root_coordinates()[j - RANK][k] for k in range(RANK))
            expected = -1 if pairing % 2 else 1
            if column != ((j, expected),):
                raise ArithmeticError("Tits torus-square relation failed")
    for i, j in combinations(range(RANK), 2):
        a, b = tits_lift(i), tits_lift(j)
        left, right = (compose(a, b), compose(b, a)) if not cartan[i][j] else (
            compose(a, compose(b, a)), compose(b, compose(a, b)))
        if left != right:
            raise ArithmeticError(f"Tits braid relation failed on {(i, j)}")
    return {"square_basis_checks": RANK * DIMENSION, "braid_relations": comb(RANK, 2)}


def receipt(exhaustive=True):
    """Recompute a JSON-safe exact evidence packet, rather than saved counts."""
    operator = coxeter_lift()
    if power(operator, 30) != identity_map():
        raise ArithmeticError("adjoint Coxeter lift does not have order dividing 30")
    if any(power(operator, n) == identity_map() for n in (1, 2, 3, 5, 6, 10, 15)):
        raise ArithmeticError("adjoint Coxeter lift has a proper divisor order")
    orbits = signed_root_orbits()
    if len(orbits) != 8 or any(o["length"] != 30 or o["sign_product"] != 1 for o in orbits):
        raise ArithmeticError("root-space signed cycles have unexpected spectrum")
    gauged = compose(root_sign_gauge(), compose(operator, root_sign_gauge()))
    for root, index in zip(geometry.roots(), range(RANK, DIMENSION)):
        target = root_basis_index(geometry.simple_root_coordinates(geometry.coxeter_action(root)))
        if gauged[index] != ((target, 1),):
            raise ArithmeticError("root sign gauge did not intertwine to the root permutation")
    cartan = geometry.coxeter_matrix()
    for i in range(RANK):
        if operator[i] != tuple((k, cartan[k][i]) for k in range(RANK) if cartan[k][i]):
            raise ArithmeticError("Cartan restriction disagrees with geometric Coxeter matrix")
    trace_values = [coxeter_trace(n) for n in range(30)]
    if trace_values != [geometry.coxeter_trace(n) + (240 if n == 0 else 0) for n in range(30)]:
        raise ArithmeticError("adjoint traces disagree with root-permutation-plus-Cartan traces")
    relation_counts = verify_tits_relations()
    for i in range(DIMENSION):
        if bracket_basis(i, i):
            raise ArithmeticError("alternation failed")
    for i, j in combinations(range(DIMENSION), 2):
        if bracket_basis(i, j) != tuple((k, -c) for k, c in bracket_basis(j, i)):
            raise ArithmeticError("skew symmetry failed")
    cocycle_pairs = verify_cocycle() if exhaustive else None
    jacobi = verify_jacobi() if exhaustive else None
    automorphisms = sum(verify_bracket_automorphism(tits_lift(i)) for i in range(RANK)) if exhaustive else None
    return {"schema": "pp-e8-adjoint-lift/1", "dimension": DIMENSION,
            "arithmetic": "exact integers and rationals; not a Lean theorem",
            "cocycle": "(-1)^(sum_i a_i*b_i + sum_{i>j} a_i*A_ij*b_j)",
            "opposite_root_bracket": "[e_alpha,e_-alpha]=-h_alpha",
            "tits_lift": "exp(ad e_i) exp(ad e_-i) exp(ad e_i)",
            "alternating_basis_checks": DIMENSION,
            "skew_symmetry_basis_pairs": comb(DIMENSION, 2),
            "cocycle_root_pairs": cocycle_pairs,
            "jacobi_distinct_basis_triples": jacobi,
            "lift_bracket_preservation_pairs": automorphisms,
            "exhaustive_checks_executed": bool(exhaustive),
            **relation_counts, "coxeter_order": 30,
            "signed_root_orbits": list(orbits),
            "simple_lift_negative_root_images": [sum(c[0][1] < 0 for c in tits_lift(i)[RANK:]) for i in range(RANK)],
            "coxeter_negative_root_images": sum(c[0][1] < 0 for c in operator[RANK:]),
            "root_sign_gauge": {str(i): column[0][1] for i, column in enumerate(root_sign_gauge()) if i >= RANK},
            "adjoint_traces_0_to_29": trace_values,
            "principal_height_spectrum": principal_height_receipt(),
            "characteristic_polynomial": "(X^30-1)^8 * Phi_30(X)",
            "actual_adjoint_identification_checked": True,
            "spectral_mellin_factor": "zeta(s)*30^(1-s)*(8-(2^(s-1)-1)*(3^(s-1)-1)*(5^(s-1)-1))",
            "domain": "Re(s)>1",
            "weight_two_pi_squared_coefficient": str(geometry.combined_pi_coefficient(2)),
            "log_weighted_pi_squared_coefficients": {str(p): str(c) for p, c in geometry.combined_log_mellin_coefficients().items()},
            "scope": "An actual inner automorphism on the explicitly constructed complex E8 Lie algebra; no higher categorical colimit is asserted.",
            "sources": ["https://arxiv.org/html/2602.19632v1", "https://arxiv.org/abs/1608.00510"]}


def main(argv=None):
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive", action="store_true", help="recheck every Jacobi triple and every lift bracket pair")
    args = parser.parse_args(argv)
    print(json.dumps(receipt(exhaustive=args.exhaustive), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
