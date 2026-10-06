"""Exact polynomial matrix bridges for supplied flavor Hessians and metrics.

Bareiss elimination keeps determinants polynomial. A bordered determinant
compiles direct-g^T H^-1 o without computing a numerical inverse. Stability
uses exact leading principal minors and continuous polynomial certificates.
All input coefficients must already be rational; matching is upstream.
"""
from fractions import Fraction as Q
from . import polyalg as P
from .flavor_polynomial_bounds import exact, positive_halfline, verify_positive_halfline


def matrix(values):
    rows = tuple(tuple(exact(p) for p in row) for row in values)
    if not 1 <= len(rows) <= 24 or any(len(row) != len(rows) for row in rows):
        raise ValueError('square polynomial matrix of dimension 1..24 required')
    return rows


def constants(values):
    return matrix([[[x] for x in row] for row in values])


def determinant(values):
    """Fraction-free polynomial determinant, including exact row pivoting."""
    A = [list(row) for row in matrix(values)]
    n, sign, previous = len(A), 1, P.ONE
    for k in range(n-1):
        pivot_row = next((i for i in range(k,n) if not P.is_zero(A[i][k])),None)
        if pivot_row is None:
            return P.ZERO
        if pivot_row != k:
            A[k],A[pivot_row] = A[pivot_row],A[k]
            sign = -sign
        pivot = A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                value = P.subtract(P.mul(pivot,A[i][j]),P.mul(A[i][k],A[k][j]))
                A[i][j] = exact(P.exact_div(value,previous))
            A[i][k] = P.ZERO
        previous = pivot
    return P.scale(A[-1][-1],sign)


def _encode(H):
    return [[[str(c) for c in p] for p in row] for row in H]


def _interval_polynomial(f,lo,hi):
    """(1+t)^degree f((lo+hi*t)/(1+t)), mapping t>=0 to [lo,hi)."""
    degree = max(0,P.degree(f))
    out = P.ZERO
    for i,c in enumerate(f):
        out = P.add(out,P.scale(P.mul(P.power((lo,hi),i),P.power(P.poly([1,1]),degree-i)),c))
    return out


def positive_interval(coefficients,lo,hi):
    f = exact(coefficients);lo,hi = exact([lo])[0],exact([hi])[0]
    if lo >= hi or P.evaluate(f,hi) <= 0:
        raise ValueError('ordered interval and strictly positive right endpoint required')
    return {'schema':'pp-positive-rational-interval/1','coefficients':list(map(str,f)),
            'interval':[str(lo),str(hi)], 'right_endpoint_value':str(P.evaluate(f,hi)),
            'halfline':positive_halfline(_interval_polynomial(f,lo,hi)),
            'formal_verification':False}


def verify_interval(receipt):
    try:
        if receipt['schema'] != 'pp-positive-rational-interval/1' or receipt['formal_verification'] is not False:
            return False
        f = exact(receipt['coefficients']);lo,hi = map(Q,receipt['interval'])
        return (lo < hi and P.evaluate(f,hi)>0
                and Q(receipt['right_endpoint_value'])==P.evaluate(f,hi)
                and exact(receipt['halfline']['coefficients'])==_interval_polynomial(f,lo,hi)
                and verify_positive_halfline(receipt['halfline']))
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):
        return False


def positive_definite(values, *, interval=None):
    H = matrix(values);n = len(H)
    if interval is not None:
        interval=tuple(exact([v])[0] for v in interval)
        if len(interval)!=2:raise ValueError('two interval endpoints required')
    if any(H[i][j] != H[j][i] for i in range(n) for j in range(n)):
        raise ValueError('exact symmetric matrix required; reduce gauge directions upstream')
    minors = [determinant([row[:k] for row in H[:k]]) for k in range(1,n+1)]
    certs = [positive_halfline(f) if interval is None else positive_interval(f,*interval) for f in minors]
    return {'schema':'pp-flavor-matrix-positive/1','matrix':_encode(H),
            'interval':None if interval is None else list(map(str,interval)),
            'principal_minors':list(map(lambda p:list(map(str,p)),minors)),
            'positivity':certs,'dimension':n,'formal_verification':False}


def verify_positive_definite(receipt):
    try:
        if receipt['schema'] != 'pp-flavor-matrix-positive/1' or receipt['formal_verification'] is not False:
            return False
        H = matrix(receipt['matrix']);n = len(H)
        if n != receipt['dimension'] or any(H[i][j] != H[j][i] for i in range(n) for j in range(n)):
            return False
        if len(receipt['principal_minors']) != n or len(receipt['positivity']) != n:
            return False
        for k,(f,c) in enumerate(zip(receipt['principal_minors'],receipt['positivity']),1):
            f = exact(f)
            if f != determinant([row[:k] for row in H[:k]]) or f != exact(c['coefficients']):
                return False
            if receipt['interval'] is None:
                if not verify_positive_halfline(c):return False
            elif c['interval'] != receipt['interval'] or not verify_interval(c):return False
        return True
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):
        return False


def relaxed_response(values, observable_gradient, operator_gradient, direct=(0,)):
    """Compile the supplied relaxed linear response to an unreduced N/D.

    Keep the determinant denominator even when numerator factors cancel:
    physical stationarity still requires an invertible reduced Hessian.
    """
    H = matrix(values);n = len(H)
    if n >= 24:raise ValueError('bordered response dimension must be at most 23')
    g,o = tuple(map(exact,observable_gradient)),tuple(map(exact,operator_gradient))
    if len(g) != n or len(o) != n:raise ValueError('matching gradient dimensions required')
    direct = exact(direct)
    denominator = determinant(H)
    if P.is_zero(denominator):raise ValueError('identically singular Hessian')
    border = [list(row)+[v] for row,v in zip(H,o)]+[list(g)+[P.ZERO]]
    bordered = determinant(border)
    numerator = exact(P.add(P.mul(direct,denominator),bordered))
    return {'schema':'pp-flavor-relaxed-response/1','matrix':_encode(H),
            'observable_gradient':[list(map(str,p)) for p in g],
            'operator_gradient':[list(map(str,p)) for p in o],
            'direct':list(map(str,direct)), 'bordered_determinant':list(map(str,bordered)),
            'numerator':list(map(str,numerator)), 'denominator':list(map(str,denominator)),
            'meaning':'direct - observable_gradient^T H^-1 operator_gradient, only where det(H)!=0',
            'formal_verification':False}


def verify_response(receipt):
    try:
        rebuilt = relaxed_response(receipt['matrix'],receipt['observable_gradient'],receipt['operator_gradient'],receipt['direct'])
        return rebuilt == receipt
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):
        return False


def operator_norm_envelope(values, bound):
    """Prove ||E(x)||_2<bound for a real symmetric polynomial matrix."""
    E = matrix(values);b = exact([bound])[0]
    if b <= 0:raise ValueError('positive spectral envelope required')
    def shifted(sign):
        return [[P.add(P.scale(E[i][j],sign),(b if i==j else Q(0),))
                 for j in range(len(E))] for i in range(len(E))]
    return {'schema':'pp-flavor-matrix-norm/1','matrix':_encode(E),'bound':str(b),
            'plus':positive_definite(shifted(1)), 'minus':positive_definite(shifted(-1)),
            'formal_verification':False}


def verify_norm_envelope(receipt):
    try:
        if receipt['schema'] != 'pp-flavor-matrix-norm/1' or receipt['formal_verification'] is not False:
            return False
        E = matrix(receipt['matrix']);b = Q(receipt['bound'])
        if b<=0:return False
        for key,sign in [('plus',1),('minus',-1)]:
            wanted = [[P.add(P.scale(E[i][j],sign),(b if i==j else Q(0),)) for j in range(len(E))] for i in range(len(E))]
            if matrix(receipt[key]['matrix']) != matrix(wanted) or receipt[key]['interval'] is not None or not verify_positive_definite(receipt[key]):
                return False
        return True
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):
        return False


def rectangular_norm_envelope(values,bound):
    """Bound a cross-sector block through b^2 I-B^T B > 0."""
    B = tuple(tuple(exact(p) for p in row) for row in values)
    if not B or not B[0] or max(len(B),len(B[0]))>24 or any(len(row)!=len(B[0]) for row in B):
        raise ValueError('nonempty rectangular polynomial block of size at most 24 required')
    b = exact([bound])[0]
    if b<=0:raise ValueError('positive norm bound required')
    n=len(B[0])
    gram=[[P.subtract((b*b if i==j else Q(0),),
                     sum_polynomials(P.mul(row[i],row[j]) for row in B)) for j in range(n)] for i in range(n)]
    return {'schema':'pp-flavor-cross-sector-norm/1','block':_encode(B), 'bound':str(b),
            'gram_gap':positive_definite(gram),'formal_verification':False}


def sum_polynomials(values):
    out=P.ZERO
    for p in values:out=P.add(out,p)
    return out


def verify_rectangular_envelope(receipt):
    try:
        if receipt['schema']!='pp-flavor-cross-sector-norm/1' or receipt['formal_verification'] is not False:
            return False
        B=tuple(tuple(exact(p) for p in row) for row in receipt['block']);b=Q(receipt['bound'])
        if not B or not B[0] or max(len(B),len(B[0]))>24 or b<=0 or any(len(row)!=len(B[0]) for row in B):return False
        n=len(B[0])
        wanted=[[P.subtract((b*b if i==j else Q(0),),sum_polynomials(P.mul(row[i],row[j]) for row in B)) for j in range(n)] for i in range(n)]
        return (receipt['gram_gap']['interval'] is None
                and matrix(receipt['gram_gap']['matrix'])==matrix(wanted)
                and verify_positive_definite(receipt['gram_gap']))
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


def protected_response(values,observable_gradient,operator_gradient,budget,*,direct=(0,),interval=None):
    """A stable supplied Hessian and a uniform absolute relaxed-response bound."""
    response=relaxed_response(values,observable_gradient,operator_gradient,direct)
    stability=positive_definite(values,interval=interval)
    N,D=exact(response['numerator']),exact(response['denominator']);b=exact([budget])[0]
    if b<=0:raise ValueError('positive response budget required')
    residual=P.subtract(P.scale(P.mul(D,D),b*b),P.mul(N,N))
    positivity=positive_halfline(residual) if interval is None else positive_interval(residual,*interval)
    return {'schema':'pp-flavor-stable-response-budget/1','response':response,
            'stability':stability,'budget':str(b),'budget_residual':list(map(str,residual)),
            'positivity':positivity,'formal_verification':False}


def verify_protected_response(receipt):
    try:
        if receipt['schema']!='pp-flavor-stable-response-budget/1' or receipt['formal_verification'] is not False:
            return False
        r,s=receipt['response'],receipt['stability'];b=Q(receipt['budget'])
        if b<=0 or not verify_response(r) or not verify_positive_definite(s) or matrix(r['matrix'])!=matrix(s['matrix']):return False
        N,D=exact(r['numerator']),exact(r['denominator'])
        residual=P.subtract(P.scale(P.mul(D,D),b*b),P.mul(N,N))
        if residual!=exact(receipt['budget_residual']) or residual!=exact(receipt['positivity']['coefficients']):return False
        if s['interval'] is None:return verify_positive_halfline(receipt['positivity'])
        return s['interval']==receipt['positivity']['interval'] and verify_interval(receipt['positivity'])
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False
