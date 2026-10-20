"""Exact arithmetic trace form and nonsplit normalizer of the actual E8 Coxeter lattice.

The cyclotomic realization and centralizer are classical. These certificates
use the repository's integral matrices; no novelty or new Lean claim is made.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd
from .e8_periods import (coxeter_matrix, cartan_matrix, matrix_power, matmul,
                        matvec, identity, roots, simple_root_coordinates)
from .exact_linear import inverse, solve, transpose

UNITS = tuple(k for k in range(30) if gcd(k, 30) == 1)
ALPHA = tuple(map(Q, ('1/3','-1/15','-2/15','-2/15','-1/15','0','1/15','2/15')))


def determinant(matrix):
    a = [list(map(Q, row)) for row in matrix]
    n = len(a)
    if not n or any(len(row) != n for row in a):
        raise ValueError('nonempty square matrix required')
    result = Q(1)
    for j in range(n):
        pivot = next((i for i in range(j,n) if a[i][j]), None)
        if pivot is None: return Q(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        value = a[j][j]
        result *= value
        for i in range(j+1,n):
            factor = a[i][j]/value
            for k in range(j+1,n): a[i][k] -= factor*a[j][k]
    return result


def _int(matrix):
    if any(Q(x).denominator != 1 for row in matrix for x in row):
        raise ArithmeticError('nonintegral lattice map')
    return tuple(tuple(int(x) for x in row) for row in matrix)


def _trace(matrix): return sum(matrix[i][i] for i in range(len(matrix)))


def _krylov(operator, vector):
    columns = [tuple(vector)]
    for _ in range(7): columns.append(matvec(operator, columns[-1]))
    return transpose(columns)


@lru_cache(maxsize=1)
def lattice_data():
    c, a = coxeter_matrix(), cartan_matrix()
    b = _krylov(c, (0,0,0,0,0,0,0,1))
    bi = _int(inverse(b))
    d = _int(matmul(matmul(bi,c),b))
    g = matmul(matmul(transpose(b),a),b)
    if abs(determinant(b)) != 1 or matmul(b,bi) != identity():
        raise ArithmeticError('invalid integral bridge')
    return c,a,b,bi,d,g


@lru_cache(maxsize=1)
def _powers(): return tuple(matrix_power(lattice_data()[4],i) for i in range(30))


def multiplication_matrix(coefficients):
    if len(coefficients) != 8: raise ValueError('eight coefficients required')
    return tuple(tuple(sum(Q(coefficients[k])*_powers()[k][i][j] for k in range(8))
                       for j in range(8)) for i in range(8))


def field_product(x,y): return matvec(multiplication_matrix(x),y)


def galois_matrix(exponent):
    if type(exponent) is not int or exponent%30 not in UNITS:
        raise ValueError('unit exponent modulo30 required')
    one = (1,0,0,0,0,0,0,0)
    return transpose(tuple(matvec(_powers()[(exponent*i)%30],one) for i in range(8)))


def trace_form_certificate():
    g = lattice_data()[-1]
    pairing = tuple(tuple(_trace(_powers()[(i+j)%30]) for j in range(8)) for i in range(8))
    alpha = solve(pairing,tuple(row[0] for row in g))
    actual = tuple(tuple(sum(alpha[k]*_trace(_powers()[(k+i-j)%30]) for k in range(8))
                         for j in range(8)) for i in range(8))
    if alpha != ALPHA or actual != g or matvec(galois_matrix(29),alpha) != alpha:
        raise ArithmeticError('trace form failed')
    norm = determinant(multiplication_matrix(alpha))
    unit = field_product(alpha,(1,0,-3,-4,-5,0,7,8))
    if norm*determinant(pairing) != 1 or determinant(g) != 1 or determinant(multiplication_matrix(unit)) != 1:
        raise ArithmeticError('codifferent certificate failed')
    ai = solve(multiplication_matrix(alpha),(1,0,0,0,0,0,0,0))
    return dict(alpha_coefficients=list(map(str,alpha)),gram=[list(r) for r in g],
                gram_identity_entries_checked=64,alpha_fixed_by_conjugation=True,
                norm_alpha=str(norm),field_discriminant=str(determinant(pairing)),
                lattice_determinant='1',inverse_alpha=list(map(str,ai)),
                alpha_times_cyclotomic_derivative=list(map(str,unit)),
                codifferent_generator_unit_norm='1')


def verify_lift(exponent,u):
    if type(exponent) is not int or exponent%30 not in UNITS: return False
    if len(u) != 8 or any(len(row) != 8 for row in u): return False
    if any(type(x) not in (int,Q) or Q(x).denominator != 1 for row in u for x in row): return False
    c,a,*_ = lattice_data()
    return matmul(matmul(transpose(u),a),u) == a and matmul(u,c) == matmul(matrix_power(c,exponent%30),u)


@lru_cache(maxsize=1)
def normalizer_lifts():
    c,a,b,bi,d,g = lattice_data()
    answer = []
    for exponent in UNITS:
        ca = matrix_power(c,exponent)
        for root in sorted(simple_root_coordinates(r) for r in roots()):
            k = _krylov(ca,root)
            if matvec(transpose(k),matvec(a,root)) != tuple(g[0]): continue
            if matmul(matmul(transpose(k),a),k) != g: continue
            u = _int(matmul(k,bi))
            if not verify_lift(exponent,u): raise ArithmeticError('invalid normalizer lift')
            answer.append((exponent,u))
    return tuple(answer)


def nonsplit_certificate():
    c,a,b,bi,d,g = lattice_data()
    multiplier = (0,0,1,1,1,1,0,-1)
    s = _int(matmul(matmul(b,matmul(multiplication_matrix(multiplier),galois_matrix(7))),bi))
    if not verify_lift(7,s) or matrix_power(s,4) != matrix_power(c,25):
        raise ArithmeticError('nonsplitting witness failed')
    for i in range(30):
        if matrix_power(matmul(matrix_power(c,i),s),4) != matrix_power(c,(25+10*i)%30):
            raise ArithmeticError('coset power law failed')
    return dict(exponent=7,quotient_order=4,lift=[list(r) for r in s],multiplier=list(multiplier),
                fourth_power_coxeter_exponent=25,all_coset_fourth_power_exponents=[5,15,25],
                fourth_power_formula='(C^i S)^4=C^(25+10i)',extension_splits=False,
                order_four_lift_exists=False)


def receipt():
    c,a,b,bi,d,g = lattice_data()
    powers = tuple(matrix_power(c,i) for i in range(30))
    lifts = normalizer_lifts()
    central = {u for e,u in lifts if e == 1}
    if central != set(powers): raise ArithmeticError('centralizer failed')
    rows = []
    for exponent in UNITS:
        fiber = [u for e,u in lifts if e == exponent]
        if len(fiber) != 30 or set(fiber) != {matmul(p,fiber[0]) for p in powers}:
            raise ArithmeticError('incomplete normalizer fiber')
        u = matmul(matmul(bi,fiber[0]),b)
        multiplier = tuple(u[i][0] for i in range(8))
        if matmul(multiplication_matrix(multiplier),galois_matrix(exponent)) != u:
            raise ArithmeticError('semilinear identity failed')
        norm = field_product(multiplier,matvec(galois_matrix(29),multiplier))
        if field_product(ALPHA,norm) != matvec(galois_matrix(exponent),ALPHA):
            raise ArithmeticError('semilinear norm transport failed')
        rows.append(dict(exponent=exponent,lifts=30,representative=[list(r) for r in fiber[0]],
                         multiplier=list(map(str,multiplier)),semilinear_identity_checked=True,norm_transport_checked=True))
    remaining = set(simple_root_coordinates(r) for r in roots())
    orbit_sizes = []
    while remaining:
        orbit = {matvec(u,min(remaining)) for e,u in lifts}
        if not orbit <= remaining: raise ArithmeticError('overlapping orbits')
        orbit_sizes.append(len(orbit));remaining -= orbit
    return dict(schema='pp-coxeter-trace-normalizer/1',trace_form=trace_form_certificate(),
                centralizer_order=30,normalizer_order=len(lifts),unit_exponents=list(UNITS),lifts=rows,
                root_candidates_per_exponent=240,root_orbit_sizes=sorted(orbit_sizes),
                centralizer_exactly_coxeter_powers=True,nonsplit=nonsplit_certificate(),new_lean_theorems=0,
                completeness='The cyclic root image and exponent force every Krylov column; all240 possible root images are tested.',
                provenance='Classical arithmetic framework; explicit finite certificates in the retained coordinates. Historical priority not established.')
