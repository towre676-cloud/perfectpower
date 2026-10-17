"""Exact coefficient engine for Raghava's complete generating families.

The analytic identities are from arXiv:2607.09904v2, not new summation
principles. All coefficients and finite enclosures use stdlib Fractions.
Formal zeta coordinates are not presumed numerically independent. No Lean
kernel claim is made. The finite m<=64 and dense basis m<=32 guards are
computational budgets, not limits of the cited all-order mathematics.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial

from .cyclotomic_real import pi_interval
from .raghava_periods import ARCSINE_SOURCE, _index, _q


def _precision(bits):
    _index(bits, 8, 512)


def _outward(interval, bits):
    lo, hi = interval
    scale = 1 << bits
    return (Q((lo*scale).numerator//(lo*scale).denominator, scale),
            Q(-((-hi*scale).numerator//(-hi*scale).denominator), scale))


def _add(a, b):
    return a[0]+b[0], a[1]+b[1]


def _scale(a, c):
    c = Q(c)
    return (a[0]*c, a[1]*c) if c >= 0 else (a[1]*c, a[0]*c)


def _mul(a, b):
    values = [x*y for x in a for y in b]
    return min(values), max(values)


def _inverse(a):
    if a[0] <= 0 <= a[1]:
        raise ValueError('interval contains a normalization pole')
    return Q(1)/a[1], Q(1)/a[0]


def _pow(a, n):
    if a[0] < 0 or type(n) is not int or n < 0:
        raise ValueError('nonnegative interval and integer power required')
    return a[0]**n, a[1]**n


def _receipt(schema, interval, **kwargs):
    return dict(schema=schema, lower=str(interval[0]), upper=str(interval[1]),
                source=ARCSINE_SOURCE, arithmetic='exact rational enclosure',
                formal_kernel_verified=False, **kwargs)


def _bounds(receipt):
    return Q(receipt['lower']), Q(receipt['upper'])


@lru_cache(maxsize=65)
def lambda_coefficients(order):
    """Coefficients of y/sinh(y) in ascending even degree, exactly."""
    _index(order, 0, 64)
    values = [Q(1)]
    for m in range(1, order+1):
        values.append(-sum((values[m-h]/factorial(2*h+1)
                            for h in range(1, m+1)), Q(0)))
    return tuple(values)


def generating_multiplier(k, j, kind='second'):
    """The explicit rational C_(k,j) or D_(k,j) of the full families."""
    _index(k, 0, 64)
    _index(j, 0, 64)
    if kind not in ('second', 'supplementary'):
        raise ValueError('second or supplementary family required')
    a = 4**k
    if kind == 'second':
        return (-Q(1, 72*36**j)+Q(1-a, 18*9**j)+Q(1, 8*4**j)
                +Q(a-1, 2)+Q(a*(6-a), 9*(2-a))*Q(4, 9)**j
                +Q(a*(3*a-2), 2-a)*4**j)
    t = Q(a, 2-a)
    return ((t+1)/(9*9**j)+(2*t+3-Q(4, a))/(8*4**j)
            +(Q(4, a)-1)/(72*36**j)+Q(1, 8*a*16**j)
            -Q(1, 72*a*144**j))


def generating_family(m, kind='second'):
    """Return F_m harmonic data and its exact homogeneous odd-zeta value."""
    _index(m, 0, 64)
    if kind not in ('second', 'supplementary'):
        raise ValueError('second or supplementary family required')
    lambdas = lambda_coefficients(m)
    harmonic, zetas = [], []
    for j in range(m+1):
        scale = lambdas[m-j]/3**(2*(m-j))
        harmonic.append(dict(e_index=j, pi_power=2*(m-j), coefficient=str(scale)))
        zetas.append(dict(zeta_order=2*j+3, pi_power=2*(m-j),
                          coefficient=str((-1)**j*scale*generating_multiplier(m-j, j, kind))))
    b = 2**(2*m+1)
    return dict(family=kind, m=m, weight=2*m+3,
                harmonic_coefficients=harmonic, zeta_coefficients=zetas,
                harmonic_insertions=(dict(H_2n='1', H_n=str(b), inverse_n='0')
                                     if kind == 'second' else
                                     dict(H_2n='0', H_n=str(1+Q(1, b)), inverse_n='-1/2')),
                strict_sign=(-1)**m if kind == 'second' else None,
                convergence='ABSOLUTE', source=ARCSINE_SOURCE,
                equation='Theorem 5.3' if kind == 'second' else 'equations (9.3)-(9.4), exact coefficient extraction',
                scope='complete all-order constructive family within a finite order budget; no numerical independence or new summation principle claim')


def verify_family(receipt):
    try:
        return receipt == generating_family(receipt['m'], receipt['family'])
    except (KeyError, ValueError, TypeError, ArithmeticError):
        return False


def _vector(receipt, m):
    v = [Q(0)]*(m+1)
    for row in receipt['zeta_coefficients']:
        j = (row['zeta_order']-3)//2
        if not 0 <= j <= m or row['pi_power'] != 2*(m-j):
            raise ValueError('inhomogeneous zeta expression')
        v[j] += Q(row['coefficient'])
    return v


def canonical_second_basis(m, coefficients):
    """Triangular formal conversion to pi^(2(m-k))*S_k, k=0,...,m.

    coefficients is an ascending vector in pi^(2(m-j))*zeta(2j+3), or
    its zeta_coefficients row representation. A reconstruction check is exact
    and establishes an expression identity without assuming zeta independence.
    """
    _index(m, 0, 32)
    if isinstance(coefficients, dict):
        coefficients = coefficients['zeta_coefficients']
    coefficients = list(coefficients)
    if coefficients and isinstance(coefficients[0], dict):
        target = _vector(dict(zeta_coefficients=coefficients), m)
    else:
        if len(coefficients) != m+1:
            raise ValueError('m+1 homogeneous coordinates required')
        target = [_q(value) for value in coefficients]
    residual = target[:]
    answer = [Q(0)]*(m+1)
    columns = [_vector(generating_family(k), k) for k in range(m+1)]
    for k in range(m, -1, -1):
        if not columns[k][k]:
            raise AssertionError('nonzero triangular diagonal theorem failed')
        answer[k] = residual[k]/columns[k][k]
        for j in range(k+1):
            residual[j] -= answer[k]*columns[k][j]
    reconstructed = [sum((answer[k]*columns[k][j] for k in range(j, m+1)), Q(0))
                     for j in range(m+1)]
    if any(residual) or reconstructed != target:
        raise AssertionError('formal basis reconstruction failed')
    return dict(schema='pp-raghava-second-basis/1', m=m, weight=2*m+3,
                input_coefficients=list(map(str, target)),
                second_coefficients=list(map(str, answer)),
                reconstructed_coefficients=list(map(str, reconstructed)),
                reconstruction_checked=True,
                scope='unique formal homogeneous coordinates; no numerical zeta independence claim')


def two_order_decomposition(r, s):
    """Recover old selected-order sums as S+D B minus a scaled lower pair."""
    _index(s, 2, 16)
    _index(r, 1, s-1)
    m, l = s-1, r-1
    br, bs = 2**(2*r-1), 2**(2*s-1)
    d, a = br*bs, br*bs+br+bs
    kappa = lambda_coefficients(m)[m]/lambda_coefficients(l)[l]/3**(2*(s-r))
    harmonic, zeta = {}, {}
    for order, scale in ((m, Q(1)), (l, -kappa)):
        shift = 2*(m-order)
        for row in generating_family(order)['harmonic_coefficients']:
            key = row['e_index'], row['pi_power']+shift
            harmonic[key] = harmonic.get(key, Q(0))+scale*Q(row['coefficient'])
        for kind, multiplier in (('second', 1), ('supplementary', d)):
            for row in generating_family(order, kind)['zeta_coefficients']:
                key = row['zeta_order'], row['pi_power']+shift
                zeta[key] = zeta.get(key, Q(0))+scale*multiplier*Q(row['coefficient'])
    return dict(schema='pp-raghava-two-order-decomposition/1', r=r, s=s,
                weight=2*s+1, A=a, D=d,
                kappa=dict(coefficient=str(kappa), pi_power=2*(s-r)),
                expression='S_(s-1)+D*B_(s-1)-kappa*(S_(r-1)+D*B_(r-1))',
                harmonic_coefficients=[dict(e_index=j, pi_power=p, coefficient=str(c))
                                       for (j, p), c in sorted(harmonic.items()) if c],
                zeta_coefficients=[dict(zeta_order=j, pi_power=p, coefficient=str(c))
                                   for (j, p), c in sorted(zeta.items()) if c],
                source=ARCSINE_SOURCE, formal_kernel_verified=False)


@lru_cache(maxsize=1024)
def zeta_interval(s, bits=96):
    """Rigorous rational Euler-eta enclosure; positive omitted tail <=2^-K.

    Reversing the finite Euler transform gives K weighted Dirichlet terms,
    avoiding a quadratic array of large rational finite differences.
    """
    _index(s, 2, 131)
    _precision(bits)
    k = bits+8
    scale = 1 << k
    total, prefix = Q(0), 0
    for n in range(1, k+1):
        prefix += comb(k, n-1)
        total += Q((-1)**(n-1)*(scale-prefix), scale*n**s)
    factor = 1-Q(1, 2**(s-1))
    lo, hi = total/factor, (total+Q(1, scale))/factor
    return _outward((lo, hi), bits+4)


def _zeta_value(receipt, bits):
    p = pi_interval(min(1024, bits+24))
    value = Q(0), Q(0)
    for row in receipt['zeta_coefficients']:
        term = _mul(_pow(p, row['pi_power']), zeta_interval(row['zeta_order'], bits))
        value = _add(value, _scale(term, Q(row['coefficient'])))
    return _outward(value, bits+8)


def family_interval(m, kind='second', bits=96):
    """Evaluate the finite zeta formula with independently bounded pi and zeta."""
    _precision(bits)
    receipt = generating_family(m, kind)
    return _receipt('pp-raghava-generating-interval/1', _zeta_value(receipt, bits),
                    m=m, family=kind, bits=bits,
                    method='Machin pi bounds and positive Euler-transformed eta tail')


def family_partial(m, kind='second', terms=32, bits=96):
    """Original signed inverse-binomial partial plus entire rational tail."""
    receipt = generating_family(m, kind)
    _index(terms, 0, 2048)
    _precision(bits)
    e = [Q(1)]+[Q(0)]*m
    h, h2 = Q(0), Q(0)
    values = [Q(0)]*(m+1)
    ins = {key: Q(value) for key, value in receipt['harmonic_insertions'].items()}
    for n in range(1, terms+1):
        h += Q(1, n)
        h2 += Q(1, 2*n-1)+Q(1, 2*n)
        insertion = ins['H_2n']*h2+ins['H_n']*h+ins['inverse_n']/n
        denominator = n*n*comb(2*n, n)
        for j, row in enumerate(receipt['harmonic_coefficients']):
            values[j] += Q(row['coefficient'])*e[j]*insertion/denominator
        for j in range(min(m, n), 0, -1):
            e[j] += e[j-1]/(n*n)
    p = pi_interval(min(1024, bits+24))
    partial = Q(0), Q(0)
    bound = Q(0)
    pirows = []
    for j, value in enumerate(values):
        power = 2*(m-j)
        partial = _add(partial, _scale(_pow(p, power), value))
        row = receipt['harmonic_coefficients'][j]
        bound += abs(Q(row['coefficient']))*Q(22, 7)**power*Q(2**j, factorial(j))
        pirows.append(dict(pi_power=power, coefficient=str(value)))
    insert_bound = 2*abs(ins['H_2n'])+abs(ins['H_n'])+abs(ins['inverse_n'])
    tail = insert_bound*bound/4**terms
    interval = _outward((partial[0]-tail, partial[1]+tail), bits+8)
    return _receipt('pp-raghava-generating-partial/1', interval, m=m, family=kind,
                    terms=terms, pi_coefficients=pirows, tail_absolute=str(tail),
                    method='e_r<=2^r/r!, H_(jn)<=jn, central-binomial geometric tail')


def generator_interval(x, j=1, terms=32, oscillatory=False):
    """Enclose U_j(x), or U_j(i*x), directly, including terminating cases."""
    x = _q(x)
    _index(j, 1, 2)
    _index(terms, 0, 2048)
    if type(oscillatory) is not bool or abs(x) > 16:
        raise ValueError('real rational |x|<=16 and boolean convention required')
    t = x*x
    return _generator_squared(t, j, terms, oscillatory, x=x)


def _generator_squared(t, j, terms, oscillatory=False, **extra):
    product, partial, h = Q(1), Q(0), Q(0)
    terminated = False
    for n in range(1, terms+1):
        if j == 1:
            h += Q(1, n)
        else:
            h += Q(1, 2*n-1)+Q(1, 2*n)
        partial += h*product/(n*n*comb(2*n, n))
        product *= 1+(-t if oscillatory else t)/(n*n)
        terminated |= product == 0
    tail = Q(0) if terminated else Q(j*3**((2*t).__ceil__()), 4**terms)
    interval = (partial-tail, partial+tail) if oscillatory else (partial, partial+tail)
    return _receipt('pp-raghava-generator-interval/1', interval, j=j,
                    t=str(t), terms=terms, oscillatory=oscillatory,
                    partial=str(partial), tail_absolute=str(tail),
                    terminated=terminated, **{key: str(value) for key, value in extra.items()})


def resolvent_interval(x, terms=32, bits=96, oscillatory=False):
    """Taylor enclosure for Z(x)=sum 1/[k(k^2+x^2)], |x|<1.

    oscillatory=True evaluates Z(i*x), stopping before its first pole.
    """
    x = _q(x)
    _index(terms, 1, 64)
    _precision(bits)
    if abs(x) >= 1 or type(oscillatory) is not bool:
        raise ValueError('resolvent common Taylor domain |x|<1 required')
    rho = x*x
    value = Q(0), Q(0)
    for j in range(terms):
        value = _add(value, _scale(zeta_interval(2*j+3, bits),
                                  rho**j*(1 if oscillatory else (-1)**j)))
    tail = 2*rho**terms/(1-rho)
    return _receipt('pp-raghava-resolvent-interval/1',
                    _outward((value[0]-tail, value[1]+tail), bits+8),
                    x=str(x), terms=terms, bits=bits, oscillatory=oscillatory,
                    tail_absolute=str(tail), domain='|x|<1')


def _entire_positive_series(t, offset, bits):
    # sum t^n/(2n+offset)! for offset 0 (cosh) or 1 (sinh(y)/y).
    total = term = Q(1)
    tolerance = Q(1, 1 << (bits+12))
    for n in range(4096):
        ratio = t/((2*n+offset+1)*(2*n+offset+2))
        following = term*ratio
        next_ratio = t/((2*n+offset+3)*(2*n+offset+4))
        if next_ratio < 1:
            tail = following/(1-next_ratio)
            if tail < tolerance:
                return total, total+tail
        total += following
        term = following
    raise ValueError('entire-series precision budget exceeded')


def _cos_interval(y, bits):
    # y is a nonnegative interval. Absolute Lagrange remainder and Lipschitz 1.
    center, radius = (y[0]+y[1])/2, (y[1]-y[0])/2
    term = total = Q(1)
    for n in range(4096):
        error = y[1]**(2*n+2)/factorial(2*n+2)+radius
        if error < Q(1, 1 << bits):
            return max(Q(-1), total-error), min(Q(1), total+error)
        term *= -center*center/((2*n+1)*(2*n+2))
        total += term
    raise ValueError('cosine precision budget exceeded')


def normalization_interval(x, bits=96, oscillatory=False):
    """Enclose (pi*x/3)/sinh(pi*x/3), or the sine normalization."""
    x = abs(_q(x))
    _precision(bits)
    if type(oscillatory) is not bool or (x >= 3 if oscillatory else x > 32):
        raise ValueError('normalization requires |x|<3 for sine or |x|<=32 for sinh')
    if not x:
        return _receipt('pp-raghava-normalization/1', (Q(1), Q(1)), x='0',
                        bits=bits, oscillatory=oscillatory)
    p = pi_interval(min(1024, bits+32))
    y = _scale(p, x/3)
    if oscillatory:
        center, radius = (y[0]+y[1])/2, (y[1]-y[0])/2
        term = total = center
        for n in range(4096):
            error = y[1]**(2*n+3)/factorial(2*n+3)+radius
            if error < Q(1, 1 << (bits+8)):
                sine = total-error, total+error
                break
            term *= -center*center/((2*n+2)*(2*n+3))
            total += term
        else:
            raise ValueError('sine precision budget exceeded')
        value = _mul(y, _inverse(sine))
    else:
        t = _pow(y, 2)
        lower = _entire_positive_series(t[0], 1, bits)[0]
        upper = _entire_positive_series(t[1], 1, bits)[1]
        value = _inverse((lower, upper))
    return _receipt('pp-raghava-normalization/1', _outward(value, bits+8),
                    x=str(x), bits=bits, oscillatory=oscillatory)


def master_interval(x, terms=32, bits=96, oscillatory=False):
    """Independent left/right enclosures of the six-resolvent master identity."""
    x = _q(x)
    _precision(bits)
    if abs(x) >= Q(1, 2):
        raise ValueError('master evaluator retains common domain |x|<1/2')
    p = pi_interval(min(1024, bits+32))
    y = _scale(p, abs(x)/3)
    if oscillatory:
        c = _cos_interval(y, bits+8)
    else:
        a, b = _pow(y, 2)
        c = _entire_positive_series(a, 0, bits)[0], _entire_positive_series(b, 0, bits)[1]
    one = Q(1), Q(1)
    c2 = _mul(c, c)
    coefficients = [_scale(c, -Q(1, 36)), _scale(_add(c, (-1, -1)), Q(1, 9)),
                    _scale(c, Q(1, 4)), _add(one, _scale(c, -1)),
                    _scale(_add(_scale(c2, 8), (2, 2)), Q(1, 9)),
                    _add(_scale(c2, 8), (-6, -6))]
    scales = Q(1, 6), Q(1, 3), Q(1, 2), Q(1), Q(2, 3), Q(2)
    right = Q(0), Q(0)
    for coefficient, scale in zip(coefficients, scales):
        z = resolvent_interval(x*scale, terms=terms, bits=bits, oscillatory=oscillatory)
        right = _add(right, _mul(coefficient, _bounds(z)))
    u1 = generator_interval(2*x, 1, terms, oscillatory)
    u2 = generator_interval(x, 2, terms, oscillatory)
    left = _add(_scale(_bounds(u1), 4), _scale(_mul(c, _bounds(u2)), 2))
    difference = _add(left, _scale(right, -1))
    return dict(schema='pp-raghava-master-interval/1', x=str(x),
                oscillatory=oscillatory, left=list(map(str, _outward(left, bits+8))),
                right=list(map(str, _outward(right, bits+8))),
                difference=list(map(str, _outward(difference, bits+8))),
                intervals_overlap=max(left[0], right[0]) <= min(left[1], right[1]),
                domain='|x|<1/2; no separate singular resolvent evaluated',
                source=ARCSINE_SOURCE, formal_kernel_verified=False)


def global_taylor_bounds(t, order=3, bits=96):
    """Global V(t) bounds by degrees 2*order+1 and 2*order, for every t>=0.

    Their validity follows from complete monotonicity, not convergence of the
    local Taylor series at t. Coefficients are independently enclosed first.
    """
    t = _q(t)
    _index(order, 0, 31)
    _precision(bits)
    if t < 0:
        raise ValueError('nonnegative rational t required')
    upper_poly = Q(0), Q(0)
    lower_poly = Q(0), Q(0)
    for m in range(2*order+2):
        term = _scale(_bounds(family_interval(m, bits=bits)), t**m)
        lower_poly = _add(lower_poly, term)
        if m <= 2*order:
            upper_poly = _add(upper_poly, term)
    lower, upper = max(Q(0), lower_poly[0]), upper_poly[1]
    return _receipt('pp-raghava-global-taylor/1', _outward((lower, upper), bits+8),
                    t=str(t), order=order, lower_degree=2*order+1,
                    upper_degree=2*order, domain='every nonnegative real t',
                    strict_for_positive_t=True,
                    method='complete monotonicity and Taylor integral remainder; no Taylor convergence premise')


def global_generator_interval(t, terms=64, bits=96):
    """Direct normalized-generator V(t) enclosure, 0<=t<=64.

    Squared-parameter arithmetic avoids approximating sqrt(t); the doubled
    U1 parameter stays within the direct generator's |x|<=16 guard.
    """
    t = _q(t)
    _index(terms, 0, 2048)
    _precision(bits)
    if not 0 <= t <= 64:
        raise ValueError('direct V evaluator requires 0<=t<=64')
    p2 = _pow(pi_interval(min(1024, bits+32)), 2)
    answer = Q(0), Q(0)
    for scale, j, factor in ((Q(1), 2, 1), (Q(4), 1, 2)):
        y2 = _scale(p2, t*scale/9)
        a = _entire_positive_series(y2[0], 1, bits)[0]
        b = _entire_positive_series(y2[1], 1, bits)[1]
        normalized = _inverse((a, b))
        u = _bounds(_generator_squared(t*scale, j, terms))
        answer = _add(answer, _scale(_mul(normalized, u), factor))
    return _receipt('pp-raghava-global-generator/1', _outward(answer, bits+8),
                    t=str(t), terms=terms, bits=bits,
                    function='a(sqrt(t))*U2(sqrt(t))+2*a(2sqrt(t))*U1(2sqrt(t))')


# Short aliases retain the mathematical notations used in the monograph.
U_interval = generator_interval
Z_interval = resolvent_interval
