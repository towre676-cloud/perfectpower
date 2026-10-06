"""Replayable continuous flavor bounds using the repository's exact Sturm core.

For D(x)>0, a positive N(x)-b D(x) on x>=0 proves N/D>b.
No global denominator sign, grid, numerical optimizer, or root reconstruction
is needed. This is a sufficient certificate; failed searches are inconclusive.
Certificates concern supplied rational coefficients, not their physical origin.
"""
from fractions import Fraction as Q
from . import polyalg as P


def exact(values):
    values = list(values)
    if not values or any(type(v) not in (int, str, Q) for v in values):
        raise ValueError('nonempty exact rational coefficients required')
    p = P.poly(Q(v) for v in values)
    if P.degree(p) > 64:
        raise ValueError('degree budget exceeded')
    return p


def _variations(values):
    signs = [v > 0 for v in values if v]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def _counts(chain):
    # Positive infinity signs follow the leading coefficients exactly.
    return [_variations([p[0] for p in chain]),
            _variations([p[-1] for p in chain])]


def positive_halfline(coefficients):
    """Certify strict positivity on [0,infinity); reject zero touches as well."""
    f = exact(coefficients)
    if f[0] <= 0:
        raise ValueError('positive endpoint required')
    chain = P.sturm_chain(f) if P.degree(f) > 0 else [P.integer_primitive(f)]
    variations = _counts(chain)
    if variations[0] != variations[1]:
        raise ValueError('polynomial has positive real roots; certificate unavailable')
    return {'schema': 'pp-positive-real-halfline/1',
            'coefficients': [str(c) for c in f],
            'sturm_chain': [[str(c) for c in p] for p in chain],
            'variations_at_zero_and_infinity': variations,
            'positive_real_roots': 0, 'domain': '[0,+infinity)',
            'formal_verification': False}


def verify_positive_halfline(receipt):
    """Check supplied signed remainders and completeness without root search."""
    try:
        if receipt['schema'] != 'pp-positive-real-halfline/1' or receipt['domain'] != '[0,+infinity)':
            return False
        if receipt['formal_verification'] is not False or receipt['positive_real_roots'] != 0:
            return False
        f = exact(receipt['coefficients'])
        chain = [exact(p) for p in receipt['sturm_chain']]
        if f[0] <= 0 or not 1 <= len(chain) <= 65:
            return False
        if chain[0] != P.poly(P.integer_primitive(f)):
            return False
        if P.degree(f) == 0:
            if len(chain) != 1:
                return False
        else:
            if len(chain) < 2 or chain[1] != P.poly(P.integer_primitive(P.derivative(f))):
                return False
            for i in range(2, len(chain)):
                r = P.divmod_poly(chain[i-2], chain[i-1])[1]
                if P.is_zero(r) or chain[i] != P.poly(P.integer_primitive(P.scale(r, -1))):
                    return False
            if not P.is_zero(P.divmod_poly(chain[-2], chain[-1])[1]):
                return False
        variations = _counts(chain)
        return variations[0] == variations[1] and receipt['variations_at_zero_and_infinity'] == variations
    except (ValueError, TypeError, KeyError, IndexError, ArithmeticError):
        return False


def rational_lower_bound(numerator, denominator, lower, witness):
    """Bound every x>=0 with D(x)>0; the witness supplies a finite upper bound."""
    N, D = exact(numerator), exact(denominator)
    b, x = exact([lower])[0], exact([witness])[0]
    if x < 0 or P.evaluate(D, x) <= 0:
        raise ValueError('witness must lie in x>=0, D(x)>0')
    upper = P.evaluate(N, x)/P.evaluate(D, x)
    positive = positive_halfline(P.subtract(N, P.scale(D, b)))
    return {'schema': 'pp-flavor-rational-bracket/1',
            'numerator': [str(c) for c in N], 'denominator': [str(c) for c in D],
            'lower_bound': str(b), 'upper_bound': str(upper), 'witness': str(x),
            'positive_difference': positive,
            'scope': 'infimum of supplied rational function on x>=0 and D(x)>0',
            'formal_verification': False}


def verify_rational_bound(receipt):
    try:
        if receipt['schema'] != 'pp-flavor-rational-bracket/1' or receipt['formal_verification'] is not False:
            return False
        if receipt['scope'] != 'infimum of supplied rational function on x>=0 and D(x)>0':
            return False
        N, D = exact(receipt['numerator']), exact(receipt['denominator'])
        b, x, upper = [exact([receipt[k]])[0] for k in ('lower_bound', 'witness', 'upper_bound')]
        if x < 0 or P.evaluate(D, x) <= 0 or upper != P.evaluate(N, x)/P.evaluate(D, x):
            return False
        difference = P.subtract(N, P.scale(D, b))
        return exact(receipt['positive_difference']['coefficients']) == difference and verify_positive_halfline(receipt['positive_difference'])
    except (ValueError, TypeError, KeyError, IndexError, ArithmeticError):
        return False


def bubble_shape_bracket(polynomials, witness, *, relative_gap=Q(1, 10**10)):
    """Certify an all-shape bracket; numerical witnesses are only proposals."""
    T = exact(polynomials['kinetic_polynomial'])
    U = exact(polynomials['potential_polynomial'])
    x = exact([witness])[0]
    gap = exact([relative_gap])[0]
    if not 0 < gap < 1 or P.evaluate(T, x) <= 0:
        raise ValueError('positive kinetic witness and relative gap in (0,1) required')
    N, D = P.mul(T, T), P.scale(U, -2)
    if P.evaluate(D, x) <= 0:
        raise ValueError('negative potential witness required')
    upper = P.evaluate(N, x)/P.evaluate(D, x)
    if upper <= 0:
        raise ValueError('positive action required')
    return rational_lower_bound(N, D, upper*(1-gap), x)


def rational_absolute_budget(numerator, denominator, budget):
    """Prove |N/D|<budget, with no poles, for every real x>=0.

    Useful for supplied matched flavor responses and kinetic EFT errors.
    An exact positive budget^2 D^2-N^2 also excludes denominator zeros.
    """
    N, D, b = exact(numerator), exact(denominator), exact([budget])[0]
    if b <= 0:
        raise ValueError('positive response budget required')
    residual = P.subtract(P.scale(P.mul(D,D),b*b), P.mul(N,N))
    return {'schema':'pp-flavor-rational-budget/1',
            'numerator':[str(c) for c in N], 'denominator':[str(c) for c in D],
            'budget':str(b), 'positive_residual':positive_halfline(residual),
            'domain':'[0,+infinity)', 'formal_verification':False}


def verify_absolute_budget(receipt):
    try:
        if receipt['schema'] != 'pp-flavor-rational-budget/1' or receipt['domain'] != '[0,+infinity)' or receipt['formal_verification'] is not False:
            return False
        N, D, b = exact(receipt['numerator']), exact(receipt['denominator']), exact([receipt['budget']])[0]
        if b <= 0:
            return False
        residual = P.subtract(P.scale(P.mul(D,D),b*b),P.mul(N,N))
        return exact(receipt['positive_residual']['coefficients']) == residual and verify_positive_halfline(receipt['positive_residual'])
    except (ValueError, TypeError, KeyError, IndexError, ArithmeticError):
        return False
