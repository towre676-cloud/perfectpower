"""Exact rational Gram, semialgebraic lower-bound and Lyapunov certificates.

Discovery is supported for quadratic polynomials and linear Lyapunov equations.
Higher-degree certificates accept supplied Gram witnesses. All acceptance is
exact coefficient algebra; no floating-point or general SOS completeness claim.
"""
from fractions import Fraction as Q
from .psg_polynomial import Polynomial, rational
from .exact_linear import multiply, transpose, identity, solve
from .divisor_square import WorkLimit


def matrix(rows):
    rows = tuple(tuple(rational(x) for x in row) for row in rows)
    n = len(rows)
    if not 1 <= n <= 64 or any(len(row) != n for row in rows):
        raise ValueError('square matrix of dimension 1..64 required')
    return rows


def encode(a):
    return [[str(x) for x in row] for row in a]


def psd_certificate(rows):
    """Natural-order LDL^T, including singular PSD matrices without division by zero."""
    a = matrix(rows)
    if a != transpose(a):
        raise ValueError('symmetric matrix required')
    n = len(a)
    L = [list(row) for row in identity(n)]
    D = []
    for k in range(n):
        pivot = rational(a[k][k]-sum(L[k][j]**2*D[j] for j in range(k)))
        if pivot < 0:
            raise ValueError('matrix is not positive semidefinite')
        D.append(pivot)
        for i in range(k+1, n):
            residual = rational(a[i][k]-sum(L[i][j]*L[k][j]*D[j] for j in range(k)))
            if not pivot:
                if residual:
                    raise ValueError('zero diagonal with nonzero residual row is indefinite')
                L[i][k] = Q(0)
            else:
                L[i][k] = rational(residual/pivot)
    return {'schema': 'pp-rational-psd/1', 'matrix': encode(a), 'L': encode(L),
            'D': list(map(str, D)), 'rank': sum(d > 0 for d in D),
            'positive_definite': all(d > 0 for d in D), 'formal_verification': False}


def check_psd(packet, rows=None):
    if packet.get('schema') != 'pp-rational-psd/1' or packet.get('formal_verification') is not False:
        raise ValueError('invalid PSD schema')
    a, L = matrix(packet['matrix']), matrix(packet['L'])
    D = tuple(map(rational, packet['D']))
    n = len(a)
    if len(L) != n or len(D) != n or any(d < 0 for d in D):
        raise ValueError('invalid LDL dimensions or signs')
    if any(L[i][j] != int(i == j) for i in range(n) for j in range(i, n)):
        raise ValueError('unit lower triangular factor required')
    actual = multiply(tuple(tuple(L[i][j]*D[j] for j in range(n)) for i in range(n)), transpose(L))
    if actual != a or (rows is not None and matrix(rows) != a):
        raise ValueError('PSD identity or source binding failed')
    if packet['rank'] != sum(d > 0 for d in D) or packet['positive_definite'] != all(d > 0 for d in D):
        raise ValueError('PSD metadata differs from decomposition')
    return True


def toeplitz_certificate(moments):
    """Exact real Toeplitz positivity with nested scalar Schur increments.

    Singular frontiers are retained. Ratios after a zero increment are
    undefined, rather than divided by zero or interpreted as reflection data.
    """
    moments = tuple(map(rational, moments))
    if not 1 <= len(moments) <= 64:
        raise ValueError('one through 64 real rational moments required')
    n = len(moments)
    a = tuple(tuple(moments[abs(i-j)] for j in range(n)) for i in range(n))
    psd = psd_certificate(a)
    increments = list(map(rational, psd['D']))
    determinant, determinants = Q(1), []
    for d in increments:
        determinant *= d
        determinants.append(str(determinant))
    return {'schema':'pp-real-toeplitz-schur/1','moments':list(map(str,moments)),
            'psd':psd,'schur_increments':list(map(str,increments)),
            'leading_determinants':determinants,
            'increment_ratios':[str(increments[i]/increments[i-1]) if increments[i-1] else None
                                for i in range(1,n)],'formal_verification':False}


def check_toeplitz(packet):
    if packet.get('schema')!='pp-real-toeplitz-schur/1':
        raise ValueError('invalid Toeplitz schema')
    check_psd(packet['psd'])
    if toeplitz_certificate(packet['moments'])!=packet:
        raise ValueError('Toeplitz moments or scalar increments altered')
    return True


def gram_certificate(basis, rows):
    basis = tuple(basis)
    if not basis or not all(isinstance(p, Polynomial) for p in basis):
        raise ValueError('nonempty polynomial basis required')
    prototype = basis[0]
    if any(p.variables != prototype.variables for p in basis):
        raise ValueError('common variable order required')
    a = matrix(rows)
    if len(a) != len(basis):
        raise ValueError('Gram dimension mismatch')
    psd = psd_certificate(a)
    polynomial = prototype.constant(0)
    for i, p in enumerate(basis):
        for j, q in enumerate(basis):
            if a[i][j]:
                polynomial = polynomial+a[i][j]*p*q
    return {'schema': 'pp-polynomial-gram/1', 'basis': [p.packet() for p in basis],
            'polynomial': polynomial.packet(), 'psd': psd, 'formal_verification': False}


def check_gram(packet, polynomial=None):
    if packet.get('schema') != 'pp-polynomial-gram/1' or packet.get('formal_verification') is not False:
        raise ValueError('invalid Gram schema')
    basis = tuple(Polynomial.from_packet(p) for p in packet['basis'])
    if not basis or len(basis) > 64:
        raise ValueError('Gram basis dimension outside 1..64')
    p = Polynomial.from_packet(packet['polynomial'])
    if any(b.variables != p.variables for b in basis):
        raise ValueError('Gram variable order mismatch')
    check_psd(packet['psd'])
    a = matrix(packet['psd']['matrix'])
    if len(a) != len(basis):
        raise ValueError('Gram dimension mismatch')
    actual = p.constant(0)
    for i, b in enumerate(basis):
        for j, c in enumerate(basis):
            if a[i][j]:
                actual = actual+a[i][j]*b*c
    if actual != p or (polynomial is not None and polynomial != p):
        raise ValueError('Gram polynomial identity or source binding failed')
    return True


def squares_certificate(polynomials, weights=None):
    polynomials = tuple(polynomials)
    if not polynomials:
        raise ValueError('at least one square required')
    weights = tuple(map(rational, weights)) if weights is not None else (Q(1),)*len(polynomials)
    if len(weights) != len(polynomials) or any(w < 0 for w in weights):
        raise ValueError('nonnegative square weights required')
    return gram_certificate(polynomials, [[w if i == j else 0 for j in range(len(weights))]
                                         for i, w in enumerate(weights)])


def quadratic_certificate(polynomial):
    """Discover a global nonnegative quadratic certificate via its unique affine Gram matrix."""
    if polynomial.degree() > 2:
        raise ValueError('quadratic discovery requires total degree <= 2')
    n = len(polynomial.variables)
    basis = (polynomial.constant(1),)+tuple(polynomial.variable(v) for v in polynomial.variables)
    a = [[Q(0)]*(n+1) for _ in range(n+1)]
    for e, c in polynomial._terms:
        indices = [i+1 for i, count in enumerate(e) for _ in range(count)]
        if not indices:
            a[0][0] += c
        elif len(indices) == 1:
            i = indices[0]; a[0][i] += c/2; a[i][0] += c/2
        else:
            i, j = indices
            if i == j:
                a[i][i] += c
            else:
                a[i][j] += c/2; a[j][i] += c/2
    return gram_certificate(basis, a)


def lower_bound_certificate(target, lower=0, *, inequalities=(), equalities=(),
                            terms=(), ideal=()):
    """terms=(constraint-index tuple, Gram packet); ideal=(equality index, polynomial).

    Empty index tuples supply the unconstrained SOS term. Products permit a
    preordering certificate. Every multiplier and domain equation is retained.
    """
    lower = rational(lower)
    ge, eq, terms, ideal = tuple(inequalities), tuple(equalities), tuple(terms), tuple(ideal)
    if len(ge)+len(eq) > 64 or len(terms)+len(ideal) > 128:
        raise WorkLimit('certificate domain or term budget exceeded')
    if any(p.variables != target.variables for p in ge+eq):
        raise ValueError('constraint variable order mismatch')
    rhs, encoded_terms, encoded_ideal = target.constant(0), [], []
    for indices, gram in terms:
        indices = tuple(indices)
        if len(indices) > 64 or any(type(i) is not int or not 0 <= i < len(ge) for i in indices):
            raise ValueError('invalid inequality product indices')
        check_gram(gram)
        sigma = Polynomial.from_packet(gram['polynomial'])
        term = target.coerce(sigma)
        for i in indices:
            term = term*ge[i]
        rhs = rhs+term
        encoded_terms.append({'indices': list(indices), 'gram': gram})
    for index, multiplier in ideal:
        if type(index) is not int or not 0 <= index < len(eq):
            raise ValueError('invalid equality index')
        rhs = rhs+target.coerce(multiplier)*eq[index]
        encoded_ideal.append({'index': index, 'multiplier': multiplier.packet()})
    if rhs != target-lower:
        raise ValueError('lower-bound polynomial identity failed')
    return {'schema': 'pp-semialgebraic-bound/1', 'target': target.packet(), 'lower': str(lower),
            'inequalities': [p.packet() for p in ge], 'equalities': [p.packet() for p in eq],
            'terms': encoded_terms, 'ideal': encoded_ideal,
            'scope': 'all real points satisfying listed inequalities >= 0 and equalities = 0',
            'formal_verification': False}


def check_lower_bound(packet, target=None, *, inequalities=None, equalities=None):
    if packet.get('schema') != 'pp-semialgebraic-bound/1' or packet.get('formal_verification') is not False:
        raise ValueError('invalid bound schema')
    p = Polynomial.from_packet(packet['target'])
    ge = tuple(Polynomial.from_packet(x) for x in packet['inequalities'])
    eq = tuple(Polynomial.from_packet(x) for x in packet['equalities'])
    if ((target is not None and p != target) or
        (inequalities is not None and ge != tuple(inequalities)) or
        (equalities is not None and eq != tuple(equalities))):
        raise ValueError('bound source or domain binding failed')
    actual = lower_bound_certificate(p, packet['lower'], inequalities=ge, equalities=eq,
        terms=[(t['indices'], t['gram']) for t in packet['terms']],
        ideal=[(t['index'], Polynomial.from_packet(t['multiplier'])) for t in packet['ideal']])
    if actual != packet:
        raise ValueError('noncanonical or altered bound packet')
    return True


def infeasibility_certificate(*, inequalities=(), equalities=(), terms=(), ideal=()):
    constraints = tuple(inequalities)+tuple(equalities)
    if not constraints:
        raise ValueError('a declared domain is required')
    return lower_bound_certificate(constraints[0].constant(-1), inequalities=inequalities,
                                   equalities=equalities, terms=terms, ideal=ideal)


def quadratic_minimum(polynomial):
    """Exact finite minimum and every minimizer for a convex rational quadratic.

    Returns one point plus a kernel basis for the complete affine tie set.
    Nonconvex and convex-unbounded quadratics raise instead of returning bounds.
    """
    if polynomial.degree() > 2:
        raise ValueError('quadratic objective required')
    vs = polynomial.variables
    zero = [0]*len(vs)
    H = matrix([[polynomial.derivative(v).derivative(w).evaluate(zero) for w in vs] for v in vs])
    psd_certificate(H)
    b = tuple(-polynomial.derivative(v).evaluate(zero) for v in vs)
    point = solve(H, b)
    if point is None:
        raise ValueError('convex quadratic is unbounded below')
    lower = polynomial.evaluate(point)
    gram = quadratic_certificate(polynomial-lower)
    bound = lower_bound_certificate(polynomial, lower, terms=[((), gram)])
    from .exact_linear import kernel
    return {'schema': 'pp-quadratic-minimum/1', 'bound': bound, 'point': list(map(str, point)),
            'tie_directions': [list(map(str, v)) for v in kernel(H)],
            'scope': 'complete affine set of real minimizers; rational point and basis',
            'formal_verification': False}


def lyapunov_certificate(operator, metric, alpha=0):
    a, p, alpha = matrix(operator), matrix(metric), rational(alpha)
    if len(a) != len(p) or alpha < 0:
        raise ValueError('common dimension and nonnegative decay rate required')
    metric_psd = psd_certificate(p)
    if not metric_psd['positive_definite']:
        raise ValueError('positive definite metric required')
    atp, pa = multiply(transpose(a), p), multiply(p, a)
    residual = tuple(tuple(-atp[i][j]-pa[i][j]-2*alpha*p[i][j]
                           for j in range(len(a))) for i in range(len(a)))
    return {'schema': 'pp-linear-lyapunov/1', 'operator': encode(a), 'metric': metric_psd,
            'alpha': str(alpha), 'residual': psd_certificate(residual),
            'scope': 'xdot=A*x; squared metric norm <= exp(-2*alpha*t) times initial norm for t>=0',
            'formal_verification': False}


def check_lyapunov(packet, operator=None):
    if packet.get('schema') != 'pp-linear-lyapunov/1' or packet.get('formal_verification') is not False:
        raise ValueError('invalid Lyapunov schema')
    a = matrix(packet['operator'])
    if operator is not None and a != matrix(operator):
        raise ValueError('Lyapunov operator binding failed')
    check_psd(packet['metric']); check_psd(packet['residual'])
    actual = lyapunov_certificate(a, packet['metric']['matrix'], packet['alpha'])
    if actual != packet:
        raise ValueError('Lyapunov residual or metadata failed')
    return True


def synthesize_lyapunov(operator, alpha=0):
    """Solve (A+alpha I)^T P+P(A+alpha I)=-I over Q, then check P>0."""
    a, alpha = matrix(operator), rational(alpha)
    n = len(a)
    if n > 8:
        raise WorkLimit('exact metric synthesis dimension exceeds 8')
    shifted = tuple(tuple(a[i][j]+alpha*int(i == j) for j in range(n)) for i in range(n))
    indices = [(i, j) for i in range(n) for j in range(i, n)]
    basis = []
    for i, j in indices:
        b = tuple(tuple(Q((u == i and v == j) or (u == j and v == i)) for v in range(n)) for u in range(n))
        left, right = multiply(transpose(shifted), b), multiply(b, shifted)
        basis.append(tuple(left[u][v]+right[u][v] for u, v in indices))
    coefficients = solve(transpose(basis), [-int(i == j) for i, j in indices])
    if coefficients is None:
        raise ValueError('Lyapunov equation has no solution')
    p = [[Q(0)]*n for _ in range(n)]
    for (i, j), c in zip(indices, coefficients):
        p[i][j] = p[j][i] = c
    return lyapunov_certificate(a, p, alpha)
