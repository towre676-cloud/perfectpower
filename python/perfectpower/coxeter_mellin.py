"""Exact Coxeter Mellin factors for every irreducible crystallographic type.

For rank r, Coxeter number h, and reflection exponents m_j, the normalized
Mellin trace of a Coxeter lift in the adjoint representation is

    Z_R(s) = zeta(s) * r * h**(1-s) + sum_j Li_s(exp(2*pi*i*m_j/h)).

The h-th power of a Coxeter lift is central (Adams--He, Proposition 5.1.1),
so every length-h root-space orbit has a regular cyclic spectrum.  This is
the justification for the adjoint interpretation; matching dimensions alone
would not justify it.  Here integer-weight factors and all root/matrix
calculations use only integer and Fraction arithmetic.  The real zero
classification is a mathematical derivation documented in
docs/COXETER_MELLIN_NOTE.md, not a Lean theorem or an originality claim.
"""

from collections import Counter, deque
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import factorial, gcd

from . import polyalg as P
from .connection_polytope import cyclotomic
from .e8_periods import (bernoulli_number, bernoulli_polynomial,
                         characteristic_polynomial, identity, matmul,
                         matrix_power, matvec)


GEOMETRY_MAX_RANK = 16
DEFAULT_EXACT_BIT_BUDGET = 1_000_000
SOURCES = (
    "https://arxiv.org/html/1608.00510v1#S5.SS1",
    "https://www.math.utah.edu/~ptrapa/math-library/reeder/reeder-cyclotomic-root-lattices-2008.pdf",
    "https://dlmf.nist.gov/25.12",
)


def _type_rank(family, rank):
    if not isinstance(family, str):
        raise ValueError("a crystallographic family name is required")
    family = family.upper()
    if family not in ("A", "B", "C", "D", "E", "F", "G"):
        raise ValueError("family must be A, B, C, D, E, F, or G")
    if type(rank) is not int:
        raise ValueError("an integer rank is required")
    valid = ((family == "A" and rank >= 1)
             or (family in ("B", "C") and rank >= 2)
             or (family == "D" and rank >= 4)
             or (family == "E" and rank in (6, 7, 8))
             or (family == "F" and rank == 4)
             or (family == "G" and rank == 2))
    if not valid:
        raise ValueError("rank does not define an irreducible type in this family")
    return family, rank


def coxeter_number(family, rank):
    family, rank = _type_rank(family, rank)
    if family == "A":
        return rank + 1
    if family in ("B", "C"):
        return 2 * rank
    if family == "D":
        return 2 * (rank - 1)
    return {("E", 6): 12, ("E", 7): 18, ("E", 8): 30,
            ("F", 4): 12, ("G", 2): 6}[family, rank]


def exponents(family, rank):
    """Reflection exponents, including the repeated exponent in even D_n."""
    family, rank = _type_rank(family, rank)
    if rank > 4096:
        raise ValueError("explicit exponent lists are limited to rank 4096")
    if family == "A":
        return tuple(range(1, rank + 1))
    if family in ("B", "C"):
        return tuple(range(1, 2 * rank, 2))
    if family == "D":
        return tuple(sorted(tuple(range(1, 2 * rank - 2, 2)) + (rank - 1,)))
    return {("E", 6): (1, 4, 5, 7, 8, 11),
            ("E", 7): (1, 5, 7, 9, 11, 13, 17),
            ("E", 8): (1, 7, 11, 13, 17, 19, 23, 29),
            ("F", 4): (1, 5, 7, 11), ("G", 2): (1, 5)}[family, rank]


def _weight(s, h, bit_budget):
    if type(s) is not int or s < 2:
        raise ValueError("integer Mellin weight s >= 2 is required")
    if type(bit_budget) is not int or bit_budget < 64:
        raise ValueError("an integer bit budget >= 64 is required")
    # Conservative bound for numerator/denominator powers before allocation.
    if (s - 1) * h.bit_length() > bit_budget:
        raise ValueError("exact exponentiation exceeds the requested bit budget")


def zeta_factor(family, rank, s, *, bit_budget=DEFAULT_EXACT_BIT_BUDGET):
    """Exact rational Z_R(s)/zeta(s), at integer s>=2, without roots/eigenfloats."""
    family, rank = _type_rank(family, rank)
    h = coxeter_number(family, rank)
    _weight(s, h, bit_budget)
    t = s - 1
    if family == "A":
        numerator = h - h ** t
    elif family in ("B", "C"):
        return Fraction(rank + 1 - 2 ** t, (2 * rank) ** t)
    elif family == "D":
        numerator = rank + 1 - 2 ** t - (2 ** t - 1) * (rank - 1) ** t
    elif (family, rank) == ("E", 6):
        numerator = 6 - (3 ** t - 1) * (4 ** t - 2 ** t + 1)
    elif (family, rank) == ("E", 7):
        numerator = 7 - (2 ** t - 1) * (9 ** t - 3 ** t + 1)
    elif (family, rank) == ("E", 8):
        numerator = 8 - (2 ** t - 1) * (3 ** t - 1) * (5 ** t - 1)
    else:
        numerator = rank + (2 ** t - 1) * (3 ** t - 1)
    return Fraction(numerator, h ** t)


def zeta_even_pi_coefficient(s):
    """Exact rational coefficient of pi**s in zeta(s), even s>=2."""
    if type(s) is not int or s < 2 or s % 2:
        raise ValueError("an even integer Mellin weight >= 2 is required")
    return Fraction((-1) ** (s // 2 + 1) * 2 ** s,
                    2 * factorial(s)) * bernoulli_number(s)


def even_pi_coefficient(family, rank, s):
    return zeta_factor(family, rank, s) * zeta_even_pi_coefficient(s)


def bernoulli_pi_coefficient(family, rank, s):
    """Independent finite Bernoulli sum over the root and Cartan phases."""
    family, rank = _type_rank(family, rank)
    h = coxeter_number(family, rank)
    if h > 128:
        raise ValueError("finite phase checks are limited to Coxeter number 128")
    scale = zeta_even_pi_coefficient(s) / bernoulli_number(s)
    reflection = sum(bernoulli_polynomial(s, Fraction(m, h))
                     for m in exponents(family, rank))
    regular = rank * sum(bernoulli_polynomial(s, Fraction(j, h)) for j in range(h))
    return scale * (reflection + regular)


def real_zero_classification(family, rank):
    """Exact classification for real s>1; strings retain nonrational zero weights."""
    family, rank = _type_rank(family, rank)
    if family in ("F", "G"):
        return {"family": family, "rank": rank, "zero_count": 0,
                "sign": "positive for every real s>1"}
    if family in ("B", "C"):
        # An integer logarithm is reported only when n+1 is a power of two.
        power = rank + 1
        integral = not (power & (power - 1))
        return {"family": family, "rank": rank, "zero_count": 1,
                "zero": "1+log(%d)/log(2)" % power,
                "integer_zero": power.bit_length() if integral else None,
                "sign": "positive below the zero; negative above the zero"}
    return {"family": family, "rank": rank, "zero_count": 1,
            "zero": "2", "integer_zero": 2,
            "sign": "positive for 1<s<2; negative for s>2"}


def bc_zero_tuner(weight, *, max_rank_bits=4096):
    """Choose B_n/C_n with its unique real zero at ANY requested integer weight.

    No rank-n matrix or root list is allocated.  The default rank bit guard
    supports weights through 4097 and can be explicitly changed.
    """
    if type(weight) is not int or weight < 2:
        raise ValueError("an integer target weight >= 2 is required")
    if type(max_rank_bits) is not int or max_rank_bits < 1:
        raise ValueError("a positive integer rank bit budget is required")
    if weight - 1 > max_rank_bits:
        raise ValueError("the tuned rank exceeds the requested bit budget")
    rank = (1 << (weight - 1)) - 1
    return {"schema": "pp-coxeter-zero-tuner/1", "weight": weight,
            "rank": rank, "rank_expression": "2^(%d)-1" % (weight - 1),
            "families": ["A1"] if rank == 1 else ["B", "C"],
            "coxeter_number": 2 * rank,
            "dimension": rank * (2 * rank + 1),
            "normalized_integral": "0", "zero_is_unique_for_real_s_gt_1": True,
            "log_companion": "-Gamma(k)*n^(1-k)*zeta(k)*log(2)",
            "scope": "exact symbolic family; no rank-n root enumeration was performed"}


def bc_kernel(rank, x, *, bit_budget=DEFAULT_EXACT_BIT_BUDGET):
    """Exact rational kernel n*((2n+1)x^(2n-1)-x^(n-1))/(1-x^(2n))."""
    if type(rank) is not int or rank < 1:
        raise ValueError("a positive integer rank is required")
    if type(x) not in (int, Fraction):
        raise ValueError("an exact rational x is required")
    x = Fraction(x)
    if not 0 < x < 1:
        raise ValueError("the integration kernel is evaluated only for 0<x<1")
    if (2 * rank) * max(x.numerator.bit_length(), x.denominator.bit_length()) > bit_budget:
        raise ValueError("kernel exponentiation exceeds the requested bit budget")
    return rank * ((2 * rank + 1) * x ** (2 * rank - 1) - x ** (rank - 1)) / (1 - x ** (2 * rank))


def tuned_log_pi_coefficient(weight, *, bit_budget=DEFAULT_EXACT_BIT_BUDGET):
    """Coefficient of pi**k*log(2) in the unnormalized log companion, even k.

    The integral is int_0^1 (-log x)^(k-1) log(-log x) K_n(x) dx.
    """
    zeta_pi = zeta_even_pi_coefficient(weight)
    rank = bc_zero_tuner(weight)["rank"]
    _weight(weight, 2 * rank, bit_budget)
    return -Fraction(factorial(weight - 1), rank ** (weight - 1)) * zeta_pi


@lru_cache(maxsize=None)
def cartan_matrix(family, rank):
    """Explicit finite Cartan data, with rows pairing coroots against roots."""
    family, rank = _type_rank(family, rank)
    if rank > GEOMETRY_MAX_RANK:
        raise ValueError("explicit geometry is limited to rank 16")
    a = [[2 * int(i == j) for j in range(rank)] for i in range(rank)]
    if family in ("A", "B", "C", "F", "G"):
        edges = [(i, i + 1) for i in range(rank - 1)]
    elif family == "D":
        edges = [(i, i + 1) for i in range(rank - 3)] + [(rank - 3, rank - 2), (rank - 3, rank - 1)]
    else:
        edges = [(0, 2), (1, 3), (2, 3)] + [(i, i + 1) for i in range(3, rank - 1)]
    for i, j in edges:
        a[i][j] = a[j][i] = -1
    if family == "B":
        a[rank - 1][rank - 2] = -2
    elif family == "C":
        a[rank - 2][rank - 1] = -2
    elif family == "F":
        a[2][1] = -2
    elif family == "G":
        a[1][0] = -3
    return tuple(map(tuple, a))


def reflect(root, index, cartan):
    rank = len(cartan)
    if len(root) != rank or type(index) is not int or not 0 <= index < rank:
        raise ValueError("a compatible root and simple reflection are required")
    root = list(root)
    root[index] -= sum(cartan[index][j] * root[j] for j in range(rank))
    return tuple(root)


@lru_cache(maxsize=None)
def roots(family, rank):
    """All roots as integer simple-root coefficients, by reflection closure."""
    a = cartan_matrix(family, rank)
    seeds = [tuple(int(i == j) for i in range(rank)) for j in range(rank)]
    known, pending = set(seeds), deque(seeds)
    while pending:
        root = pending.popleft()
        for i in range(rank):
            image = reflect(root, i, a)
            if image not in known:
                known.add(image)
                pending.append(image)
        if len(known) > rank * coxeter_number(family, rank):
            raise ArithmeticError("root closure exceeded the finite type root count")
    return tuple(sorted(known))


@lru_cache(maxsize=None)
def coxeter_matrix(family, rank):
    a = cartan_matrix(family, rank)
    out = identity(rank)
    for i in range(rank):
        reflection = [list(row) for row in identity(rank)]
        reflection[i] = [int(i == j) - a[i][j] for j in range(rank)]
        out = matmul(tuple(map(tuple, reflection)), out)
    return out


@lru_cache(maxsize=None)
def root_orbits(family, rank):
    c = coxeter_matrix(family, rank)
    remaining = set(roots(family, rank))
    result = []
    while remaining:
        seed = min(remaining)
        orbit, image = [], seed
        while image not in orbit:
            if image not in remaining:
                raise ArithmeticError("Coxeter root orbit left the unused root set")
            orbit.append(image)
            image = matvec(c, image)
        if image != seed:
            raise ArithmeticError("root orbit failed to return to its seed")
        remaining.difference_update(orbit)
        result.append(tuple(orbit))
    return tuple(result)


def bc_signed_cycle_orbits(family, rank):
    """Independent Euclidean B/C roots under e_i -> e_(i+1), e_n -> -e_1.

    These coordinates are not generated from the Cartan matrix or its
    root closure.  The displayed signed cycle is a B/C Coxeter operator.
    """
    family, rank = _type_rank(family, rank)
    if family not in ("B", "C") or rank > GEOMETRY_MAX_RANK:
        raise ValueError("a B/C type of rank 2 through 16 is required")
    remaining = set()
    for i, j in combinations(range(rank), 2):
        for a, b in product((-1, 1), repeat=2):
            v = [0] * rank
            v[i], v[j] = a, b
            remaining.add(tuple(v))
    scale = 1 if family == "B" else 2
    for i in range(rank):
        for sign in (-1, 1):
            v = [0] * rank
            v[i] = sign * scale
            remaining.add(tuple(v))
    result = []
    while remaining:
        seed = min(remaining)
        orbit, v = [], seed
        while v not in orbit:
            if v not in remaining:
                raise ArithmeticError("signed cycle failed to preserve the independent roots")
            orbit.append(v)
            v = (-v[-1],) + v[:-1]
        if v != seed:
            raise ArithmeticError("signed root cycle failed to close at its seed")
        remaining.difference_update(orbit)
        result.append(tuple(orbit))
    return tuple(result)


def exponent_characteristic_polynomial(family, rank):
    """Rational polynomial from the stated exponent phases, independently of C."""
    h = coxeter_number(family, rank)
    counts = Counter(h // gcd(h, m) for m in exponents(family, rank))
    out = P.ONE
    for order, count in sorted(counts.items()):
        factor = cyclotomic(order)
        degree = len(factor) - 1
        if count % degree:
            raise ArithmeticError("the proposed exponent list is not a rational spectrum")
        for _ in range(count // degree):
            out = P.mul(out, factor)
    return tuple(int(x) for x in out)


def kernel(family, rank, x):
    """Exact adjoint trace-resolvent kernel for rational 0<x<1."""
    family, rank = _type_rank(family, rank)
    if family in ("B", "C"):
        return bc_kernel(rank, x)
    if type(x) not in (int, Fraction) or not 0 < x < 1:
        raise ValueError("an exact rational 0<x<1 is required")
    x = Fraction(x)
    c = coxeter_matrix(family, rank)
    # det(I-xC) is the reverse of det(tI-C), preserving multiplicities.
    denominator = tuple(reversed(characteristic_polynomial(c)))
    value = sum(Fraction(a) * x ** i for i, a in enumerate(denominator))
    derivative = sum(Fraction(i * a) * x ** (i - 1) for i, a in enumerate(denominator) if i)
    h = coxeter_number(family, rank)
    return rank * h * x ** (h - 1) / (1 - x ** h) - derivative / value


def geometry_receipt(family, rank):
    """Replay root closure, root orbits, operator order and exponent polynomial."""
    family, rank = _type_rank(family, rank)
    h = coxeter_number(family, rank)
    c, rs, orbits = coxeter_matrix(family, rank), roots(family, rank), root_orbits(family, rank)
    cp = characteristic_polynomial(c)
    expected = exponent_characteristic_polynomial(family, rank)
    valid = (len(rs) == rank * h and len(orbits) == rank
             and all(len(o) == h for o in orbits) and cp == expected
             and matrix_power(c, h) == identity(rank)
             and all(matrix_power(c, d) != identity(rank)
                     for d in range(1, h) if h % d == 0))
    if not valid:
        raise ArithmeticError("exact Coxeter geometry failed")
    result = {"type": "%s%d" % (family, rank), "rank": rank, "coxeter_number": h,
            "roots": len(rs), "root_orbit_lengths": list(map(len, orbits)),
            "adjoint_dimension": rank * (h + 1), "exponents": list(exponents(family, rank)),
            "characteristic_polynomial_low_to_high": list(cp),
            "zeta_factors": {str(s): str(zeta_factor(family, rank, s)) for s in range(2, 9)},
            "real_zero_classification": real_zero_classification(family, rank),
            "arithmetic": "exact Python integers and fractions; no Lean theorem"}
    if family in ("B", "C"):
        signed_orbits = bc_signed_cycle_orbits(family, rank)
        if len(signed_orbits) != rank or any(len(o) != h for o in signed_orbits):
            raise ArithmeticError("independent Euclidean signed cycles disagree")
        result["independent_signed_cycle_orbits_verified"] = True
    return result


def receipt(max_classical_rank=16):
    """Deterministic classification receipt; classical rank budget is explicit."""
    if type(max_classical_rank) is not int or not 4 <= max_classical_rank <= 16:
        raise ValueError("classical geometry budget must be 4 through 16")
    types = ([("A", n) for n in range(1, max_classical_rank + 1)]
             + [(family, n) for family in ("B", "C") for n in range(2, max_classical_rank + 1)]
             + [("D", n) for n in range(4, max_classical_rank + 1)]
             + [("E", 6), ("E", 7), ("E", 8), ("F", 4), ("G", 2)])
    geometry = [geometry_receipt(family, rank) for family, rank in types]
    return {"schema": "pp-coxeter-mellin/1", "domain": "real s>1; analytic identity Re(s)>1",
            "model": "Coxeter-lift adjoint spectrum, justified by Adams--He Proposition 5.1.1",
            "classification_scope": "all irreducible reduced crystallographic root systems",
            "exact_geometry_cases": len(geometry), "geometry": geometry,
            "tuned_examples": [bc_zero_tuner(k) for k in (2, 3, 4, 5, 6, 8, 16, 32, 128)],
            "weight_four_log_pi4_log2_coefficient": str(tuned_log_pi_coefficient(4)),
            "limits": ["real-zero classification does not classify complex zeros",
                       "standard Lie-theoretic theorems are cited, not formalized in Lean",
                       "no originality or higher-category colimit claim is made"],
            "sources": list(SOURCES)}
