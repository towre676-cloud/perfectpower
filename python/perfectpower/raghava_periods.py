"""Raghava-centered exact analytic families, with explicit domains and tails.

The sine-pole examples are attributed to K. Srinivasa Raghava; the published
all-k generalization is attributed to Abdulhafeez Abdulsalam.  The additional
positive rational scale/shift parameters follow from the same residue proof.
The arcsine and two-selected-order families implement equations (2.1)--(3.3)
of Raghava, arXiv:2607.09904v2.  That paper explicitly gives classical
antecedents; this module claims neither a new summation principle nor a Lean
formalization.  Fractions encode exact coefficients; numerical evaluations
are separately labeled and are never used as identity certificates.
"""
from fractions import Fraction as Q
from math import comb, factorial, exp, fsum, pi


ARCSINE_SOURCE = 'https://arxiv.org/html/2607.09904v2'
SINE_SOURCE = 'https://ictp.global/news/13119204'


def _q(value):
    if type(value) not in (int, str, Q):
        raise ValueError('an exact integer, rational string, or Fraction is required')
    try:
        result = Q(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError('invalid rational') from error
    if max(abs(result.numerator).bit_length(), result.denominator.bit_length()) > 4096:
        raise ValueError('rational input exceeds the 4096-bit budget')
    return result


def _index(value, low=1, high=256):
    if type(value) is not int or not low <= value <= high:
        raise ValueError('integer index in [%s,%s] required' % (low, high))


def sine_pole(k, a=1, b=1):
    """Exact pi-polynomial in z=exp(-a*b) for integral (sin(a*x)/(x-i*b))^k.

    k=1 uses ordinary two-sided improper convergence (each half-line
    converges); k>=2 is absolutely integrable.  Positive rational a,b are
    supported; no analytic continuation to other parameters is presumed.
    """
    _index(k)
    a, b = _q(a), _q(b)
    if a <= 0 or b <= 0:
        raise ValueError('positive rational scale a and shift b required')
    terms = []
    denominator = 2**(k-1) * factorial(k-1)
    for j in range((k-1)//2 + 1):
        frequency = k - 2*j
        coefficient = Q((-1)**j * comb(k, j) * frequency**(k-1), denominator) * a**(k-1)
        terms.append(dict(exp_power=frequency, coefficient=str(coefficient),
                          expansion_index=j, positive_frequency=str(a*frequency),
                          pole_order=k, derivative_order=k-1))
    return dict(schema='pp-raghava-sine-pole/1', k=k, a=str(a), b=str(b),
                integral='integral_R (sin(a*x)/(x-i*b))^k dx',
                expression='pi * sum coefficient * exp(-a*b*exp_power)',
                terms=terms, convergence='CONDITIONAL_IMPROPER' if k == 1 else 'ABSOLUTE',
                domain='integer k>=1; positive rational a,b',
                method='expand sine into exponentials; positive frequencies close above; residue at i*b',
                zero_frequency='absent for odd k; its integral is zero for even k>=2',
                attribution=dict(examples='K. Srinivasa Raghava, displayed k=1,...,7',
                                 all_k='Abdulhafeez Abdulsalam, published generalization',
                                 scaled_family='same residue calculation with positive a,b'),
                source=SINE_SOURCE, formal_kernel_verified=False)


def verify_sine_pole(receipt):
    """Replay exact coefficient arithmetic, including metadata and domain."""
    try:
        return receipt == sine_pole(receipt['k'], receipt['a'], receipt['b'])
    except (ValueError, TypeError, KeyError, ArithmeticError):
        return False


def evaluate_sine_pole(receipt):
    """Binary64 approximation only; cancellation may lose precision at high k."""
    if not verify_sine_pole(receipt):
        raise ValueError('invalid sine-pole receipt')
    scale = float(Q(receipt['a']) * Q(receipt['b']))
    return dict(value=pi*fsum(float(Q(row['coefficient']))*exp(-scale*row['exp_power'])
                              for row in receipt['terms']),
                arithmetic='binary64 approximation; not an enclosure')


def harmonic_factors(n, degree):
    """e_0(n),...,e_degree(n) in product_(j=1)^(n-1)(1+z/j^2)."""
    _index(n, 1, 4096)
    _index(degree, 0, 32)
    values = [Q(1)] + [Q(0)]*degree
    for j in range(1, n):
        for r in range(min(degree, j), 0, -1):
            values[r] += values[r-1]/(j*j)
    return tuple(values)


def arcsine_kernel_coefficients(u, terms):
    """Exact t^(2n) coefficients of cos(2*u*asin(t/2)), n=0,...,terms."""
    u = _q(u)
    _index(terms, 0, 4096)
    result = [Q(1)]
    for n in range(terms):
        result.append(result[-1]*(n*n-u*u)/(2*(n+1)*(2*n+1)))
    return tuple(result)


def arcsine_kernel(u, t, terms=32):
    """Exact partial sum and absolute rational tail for real rational |t|<2.

    Bounds use product(1+u^2/j^2)<=exp(2u^2)<3^ceil(2u^2),
    binom(2n,n)>=4^n/(2n+1), and a geometric tail. Integer u makes
    this polynomial terminate and is reported with a zero tail when complete.
    """
    u, t = _q(u), _q(t)
    if abs(u) > 16 or abs(t) >= 2:
        raise ValueError('real rational |u|<=16 and |t|<2 required')
    coefficients = arcsine_kernel_coefficients(u, terms)
    partial = sum((c*t**(2*n) for n, c in enumerate(coefficients)), Q(0))
    rho = t*t/4
    exponent = (2*u*u).__ceil__()
    if t == 0 or (u.denominator == 1 and terms >= abs(u)):
        tail = Q(0)
    else:
        tail = 3*u*u*3**exponent*rho**(terms+1)/((terms+1)*(1-rho))
    return dict(schema='pp-raghava-arcsine-kernel/1', u=str(u), t=str(t), terms=terms,
                coefficients=[str(c) for c in coefficients], partial=str(partial),
                tail_absolute=str(tail), lower=str(partial-tail), upper=str(partial+tail),
                function='cos(2*u*asin(t/2))', branch='real principal arcsine',
                recurrence='c[n+1]=(n^2-u^2)c[n]/(2(n+1)(2n+1))',
                source=ARCSINE_SOURCE, analytic_basis='equation (2.1), plus explicit elementary tail estimate',
                formal_kernel_verified=False)


def arcsine_moment(j, t, terms=32):
    """Enclose 4^j/(2j)! asin(t/2)^(2j) by positive inverse-binomial sums."""
    _index(j, 1, 32)
    _index(terms, 0, 4096)
    t = _q(t)
    if abs(t) >= 2:
        raise ValueError('real rational |t|<2 required')
    r = j-1
    e = [Q(1)] + [Q(0)]*r
    partial = Q(0)
    coefficients = []
    for n in range(1, terms+1):
        coefficient = e[r]/(n*n*comb(2*n, n))
        coefficients.append(str(coefficient))
        partial += coefficient*t**(2*n)
        for h in range(min(r, n), 0, -1):
            e[h] += e[h-1]/(n*n)
    rho = t*t/4
    tail = 3*Q(2**r, factorial(r))*rho**(terms+1)/((terms+1)*(1-rho))
    return dict(schema='pp-raghava-arcsine-moment/1', j=j, t=str(t), terms=terms,
                coefficients=coefficients, partial=str(partial), tail_absolute=str(tail),
                lower=str(partial), upper=str(partial+tail),
                function='4^j/(2j)! * asin(t/2)^(2j)',
                method='elementary-symmetric recurrence; e_r(n)<=2^r/r!; geometric tail',
                source=ARCSINE_SOURCE, formal_kernel_verified=False)


def arcsine_angle(j, pi_multiple):
    """Exact period for t=2sin(pi*pi_multiple), |pi_multiple|<1/2.

    This symbolic specialization supplies an exact bridge for cyclotomic
    angles without pretending an algebraic t is a rational enclosure input.
    It uses principal arcsin(sin(theta))=theta on (-pi/2,pi/2).
    """
    _index(j, 1, 32)
    angle = _q(pi_multiple)
    if abs(angle) >= Q(1, 2):
        raise ValueError('rational angle multiplier of absolute value below 1/2 required')
    coefficient = Q(4**j, factorial(2*j))*angle**(2*j)
    return dict(schema='pp-raghava-arcsine-angle/1', j=j, pi_multiple=str(angle),
                t='2*sin(pi*(%s))' % angle,
                series='sum e_(j-1)(n)*t^(2n)/(n^2*binom(2n,n))',
                exact=dict(coefficient=str(coefficient), pi_power=2*j),
                branch='principal real arcsine; |theta|<pi/2',
                convergence='ABSOLUTE', source=ARCSINE_SOURCE, formal_kernel_verified=False)


def _lidstone(k):
    p = [Q(0), Q(1)]
    for _ in range(k):
        following = [Q(0)]*(len(p)+2)
        for h, coefficient in enumerate(p):
            following[h+2] = coefficient/((h+1)*(h+2))
        following[1] = -sum(following)
        p = following
    return p


def _derivative_at(p, order, x):
    return sum((p[h]*Q(factorial(h), factorial(h-order))*x**(h-order)
                for h in range(order, len(p))), Q(0))


def two_order_cancellation(r, s):
    """Construct every pair 1<=r<s<=16 in Raghava's specified polynomial ansatz.

    Exact output is sum_n E(n)/(n^2 C(2n,n))*(H_2n+A H_n-D/(2n))
    =sum_j q_j*pi^(2s-2j)*zeta(2j+1).  Each E coefficient is also a
    rational multiple of a nonnegative even power of pi.  Endpoint jets and
    quadratic Fourier multipliers are supplied for every possible sine order.
    """
    _index(s, 2, 16)
    _index(r, 1, s-1)
    high, low = _lidstone(s-1), _lidstone(r-1)
    ratio = high[1]/low[1]
    normalization = factorial(2*s-1)
    p = [normalization*(coefficient - (ratio*low[h] if h < len(low) else 0))
         for h, coefficient in enumerate(high)]
    D = 2**(2*r+2*s-2)
    A = D+2**(2*r-1)+2**(2*s-1)
    harmonic, zetas, jets = [], [], []
    for j in range(1, s+1):
        power = 2*s-2*j
        if p[2*j-1]:
            coefficient = (Q(4**(s-j)*factorial(2*j-1), normalization)
                           *p[2*j-1]/6**power)
            harmonic.append(dict(e_index=j-1, pi_power=power, coefficient=str(coefficient)))
        even = _derivative_at(p, 2*j-2, Q(1))
        z = Q(1, 2**(2*j-1))
        multiplier = 1+(D-A)*z+D*z*z
        jets.append(dict(order=2*j, endpoint_even_derivative_scaled=str(even),
                         multiplier=str(multiplier), product=str(even*multiplier)))
        a, b = Q(1, 2**(2*j)), Q(1, 3**(2*j))
        R = 1+A*a-(1-b)/2*(1+(A+D)*a-D*a*a)
        V = a*(D-Q(2*A+1, 2)*(1-a)*(1-b))
        coefficient = (Q(4**s*(-1)**(j-1), normalization*6**power)
                       *(_derivative_at(p, 2*j-1, Q(1))*R
                         +_derivative_at(p, 2*j-1, Q(0))*V))
        if coefficient:
            zetas.append(dict(zeta_order=2*j+1, pi_power=power, coefficient=str(coefficient)))
    if any(Q(row['product']) for row in jets) or p[1] or p[-1] != 1:
        raise AssertionError('exact cancellation construction failed')
    return dict(schema='pp-raghava-two-order/1', r=r, s=s, weight=2*s+1, A=A, D=D,
                polynomial=dict(variable='v=theta/(pi/6)',
                                normalization='P(theta)=(pi/6)^(2s-1)*C(v)',
                                coefficients=[str(c) for c in p]),
                harmonic_coefficients=harmonic, zeta_coefficients=zetas, cancellation_jets=jets,
                integral=dict(endpoint='pi/6', integrand='P(theta)*(-(A+1)log(1-2sin(theta))-A log(1+2sin(theta))+D log(2sin(theta)))',
                              normalization='series equals 4^s/(2s-1)! times this integral'),
                convergence='ABSOLUTE_SERIES; INTEGRABLE_LOG_ENDPOINTS',
                source=ARCSINE_SOURCE, theorem='Theorem 3.2, within the stated polynomial ansatz',
                algebraic_cancellation_checked=True, formal_kernel_verified=False,
                scope='constructive family; does not classify all inverse-binomial or all odd-zeta identities')


def verify_two_order(receipt):
    try:
        return receipt == two_order_cancellation(receipt['r'], receipt['s'])
    except (ValueError, TypeError, KeyError, ArithmeticError):
        return False


def cancellation_partial(receipt, terms=32):
    """Exact pi-polynomial partial sum and an absolute rational remainder bound.

    The bound uses pi<22/7, e_h(n)<=2^h/h!, H_n<=n and
    binom(2n,n)>=4^n/(2n+1). It is intentionally conservative and
    applies to the entire signed summand, not only a fitted numerical sample.
    """
    if not verify_two_order(receipt):
        raise ValueError('invalid two-order receipt')
    _index(terms, 0, 2048)
    degree = receipt['s']-1
    e = [Q(1)] + [Q(0)]*degree
    h = Q(0)
    h2 = Q(0)
    values = {row['pi_power']: Q(0) for row in receipt['harmonic_coefficients']}
    for n in range(1, terms+1):
        h += Q(1, n)
        h2 += Q(1, 2*n-1)+Q(1, 2*n)
        insertion = h2+receipt['A']*h-Q(receipt['D'], 2*n)
        denominator = n*n*comb(2*n, n)
        for row in receipt['harmonic_coefficients']:
            values[row['pi_power']] += Q(row['coefficient'])*e[row['e_index']]*insertion/denominator
        for j in range(min(degree, n), 0, -1):
            e[j] += e[j-1]/(n*n)
    e_bound = sum((abs(Q(row['coefficient']))*Q(22, 7)**row['pi_power']
                   *Q(2**row['e_index'], factorial(row['e_index']))
                   for row in receipt['harmonic_coefficients']), Q(0))
    bound = Q(2+receipt['A'])+Q(receipt['D'], 2)
    tail = bound*e_bound/4**terms
    return dict(schema='pp-raghava-cancellation-partial/1', r=receipt['r'], s=receipt['s'], terms=terms,
                pi_coefficients=[dict(pi_power=k, coefficient=str(v)) for k, v in sorted(values.items())],
                tail_absolute=str(tail), arithmetic='exact rational coefficients and rational absolute error bound',
                source=ARCSINE_SOURCE, formal_kernel_verified=False)


def verify_receipt(receipt):
    """Replay a JSON-roundtripped family receipt, including every stated bound.

    This checks the finite exact arithmetic against the implemented construction.
    The analytic theorems are source-supported, not checked by a proof assistant.
    """
    try:
        schema = receipt['schema']
        if schema == 'pp-raghava-sine-pole/1':
            return verify_sine_pole(receipt)
        if schema == 'pp-raghava-two-order/1':
            return verify_two_order(receipt)
        if schema == 'pp-raghava-arcsine-kernel/1':
            return receipt == arcsine_kernel(receipt['u'], receipt['t'], receipt['terms'])
        if schema == 'pp-raghava-arcsine-moment/1':
            return receipt == arcsine_moment(receipt['j'], receipt['t'], receipt['terms'])
        if schema == 'pp-raghava-arcsine-angle/1':
            return receipt == arcsine_angle(receipt['j'], receipt['pi_multiple'])
        if schema == 'pp-raghava-cancellation-partial/1':
            return receipt == cancellation_partial(two_order_cancellation(receipt['r'], receipt['s']), receipt['terms'])
        return False
    except (ValueError, TypeError, KeyError, ArithmeticError):
        return False
