"""Resultant-controlled perfect-power branches, with exact integer Bezout evidence.

All coefficients are ascending. The compiler reduces equations, not solves every branch.
"""
from fractions import Fraction as Q
from math import gcd
from itertools import product
from . import polyalg as P
from .exact_linear import solve
from .core import integer_power_root
from .divisor_square import WorkLimit, Budget, integer_roots, evaluate


def _poly(cs):
    cs=list(cs)
    if not cs or any(type(c) is not int for c in cs): raise ValueError('integer polynomial required')
    while len(cs)>1 and cs[-1]==0: cs.pop()
    if len(cs)<2: raise ValueError('two nonconstant polynomials required')
    if len(cs)>13 or any(abs(c).bit_length()>4096 for c in cs): raise WorkLimit('resultant input degree/bit limit exceeded')
    return cs


def _det(matrix, bit_limit=65536):
    """Fraction-free Bareiss determinant, including row pivot signs."""
    a=[list(r) for r in matrix]; n=len(a); previous=1; sign=1
    for k in range(n-1):
        row=next((i for i in range(k,n) if a[i][k]),None)
        if row is None:return 0
        if row!=k:a[k],a[row]=a[row],a[k];sign=-sign
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=a[i][j]*pivot-a[i][k]*a[k][j]
                if numerator%previous:raise AssertionError('Bareiss division not exact')
                a[i][j]=numerator//previous
                if abs(a[i][j]).bit_length()>bit_limit:raise WorkLimit('resultant intermediate bit limit exceeded')
            a[i][k]=0
        previous=pivot
    return sign*a[-1][-1]


def resultant_certificate(left,right):
    left=_poly(left);right=_poly(right);m=len(left)-1;n=len(right)-1;size=m+n
    columns=[]
    for cs,count in [(left,n),(right,m)]:
        for k in range(count):columns.append([0]*k+cs+[0]*(size-k-len(cs)))
    matrix=[list(r) for r in zip(*columns)]
    resultant=(-1)**(m*n)*_det(matrix)
    if resultant==0:raise ValueError('common polynomial factor: resultant descent not applicable')
    coefficients=solve(matrix,[resultant]+[0]*(size-1))
    if coefficients is None or any(c.denominator!=1 for c in coefficients):raise AssertionError('integral resultant cofactors missing')
    u=[int(c) for c in coefficients[:n]];v=[int(c) for c in coefficients[n:]]
    packet={'schema':'pp-resultant-bezout/1','left':left,'right':right,'resultant':resultant,'u':u,'v':v}
    check_resultant(packet,left,right);return packet


def check_resultant(packet,left,right):
    left=_poly(left);right=_poly(right)
    if packet['left']!=left or packet['right']!=right:raise ValueError('polynomial source binding mismatch')
    if type(packet['resultant']) is not int or packet['resultant']==0:raise ValueError('nonzero integer obstruction required')
    for name in ('u','v'):
        if not packet[name] or any(type(x) is not int for x in packet[name]):raise ValueError('integer Bezout coefficients required')
    identity=P.add(P.mul(P.poly(left),P.poly(packet['u'])),P.mul(P.poly(right),P.poly(packet['v'])))
    if identity!=P.poly([packet['resultant']]):raise ValueError('polynomial Bezout identity failed')
    return True # Any nonzero Bezout constant gives a sound exceptional-prime set.


def _factor(n,budget):
    out={};p=2
    while p*p<=n:
        budget.spend()
        while n%p==0:out[p]=out.get(p,0)+1;n//=p;budget.spend()
        p=3 if p==2 else p+2
    if n>1:out[n]=out.get(n,0)+1
    return out


def compile_descent(left,right,degree=2,*,work_limit=100000,branch_limit=10000):
    if type(degree) is not int or not 2<=degree<=64:raise ValueError('power degree must be 2..64')
    if type(branch_limit) is not int or branch_limit<1:raise ValueError('positive branch budget required')
    cert=resultant_certificate(left,right);budget=Budget(work_limit)
    factors=_factor(abs(cert['resultant']),budget);primes=sorted(factors)
    expected=degree**len(primes)*(2 if degree%2==0 else 1)
    if expected>branch_limit:raise WorkLimit('exceptional exponent branch budget exceeded')
    branches=[]
    for residues in product(range(degree),repeat=len(primes)):
        ca=cb=1
        for p,e in zip(primes,residues):ca*=p**e;cb*=p**((-e)%degree)
        for sign in ((1,-1) if degree%2==0 else (1,)):
            branches.append({'left_coefficient':sign*ca,'right_coefficient':sign*cb,
                             'exceptional_left_exponents':list(residues)})
    zeros=sorted(set(integer_roots(tuple(cert['left']),budget)+integer_roots(tuple(cert['right']),budget)))
    return {'schema':'pp-resultant-power-descent/1','bezout':cert,'degree':degree,
            'exceptional_primes':primes,'resultant_factorization':[[p,e] for p,e in sorted(factors.items())],
            'branches':branches,'zero_inputs':zeros,'reduction_complete':True,'branches_solved':False,'kernel_checked':False,
            'scope':'all integer inputs; nonzero branch roots are signed for odd degree and positive magnitudes for even degree'}


def classify_input(packet,n):
    """Recover a branch and power roots without factoring the evaluated values."""
    if type(n) is not int:raise ValueError('integer input required')
    cert=packet['bezout'];check_resultant(cert,cert['left'],cert['right'])
    a=evaluate(cert['left'],n);b=evaluate(cert['right'],n);d=packet['degree']
    root=integer_power_root(a*b,d)
    if root is None:return {'status':'NOT_A_POWER','input':n,'values':[a,b]}
    if a==0 or b==0:return {'status':'ZERO','input':n,'values':[a,b],'root':0}
    for i,branch in enumerate(packet['branches']):
        ca=branch['left_coefficient'];cb=branch['right_coefficient']
        if a%ca or b%cb:continue
        u=integer_power_root(a//ca,d);v=integer_power_root(b//cb,d)
        if u is not None and v is not None:
            return {'status':'BRANCH','input':n,'values':[a,b],'branch':i,'factor_roots':[u,v],'root':root}
    raise ValueError('descent packet missing a required branch')


def gcd_receipt(certificate,n):
    check_resultant(certificate,certificate['left'],certificate['right'])
    if type(n) is not int:raise ValueError('integer input required')
    a=evaluate(certificate['left'],n);b=evaluate(certificate['right'],n);g=gcd(a,b)
    if g==0 or certificate['resultant']%g:raise AssertionError('gcd does not divide Bezout constant')
    return {'input':n,'values':[a,b],'gcd':g,'obstruction':certificate['resultant'],
            'evaluated_bezout':evaluate(certificate['u'],n)*a+evaluate(certificate['v'],n)*b}


def check_descent(packet,*,work_limit=100000,branch_limit=10000):
    cert=packet['bezout'];expected=compile_descent(cert['left'],cert['right'],packet['degree'],work_limit=work_limit,branch_limit=branch_limit)
    if expected!=packet:raise ValueError('source-bound descent certificate does not replay')
    return True


def finite_descent_population(packet,lower,upper,*,cell_limit=100000):
    """Connect the reduction to graph populations on an explicit integer interval."""
    from .graph_counting import GraphPopulation, predicate_factor
    check_descent(packet)
    if any(type(v) is not int for v in (lower,upper)) or upper<lower:raise ValueError('ordered integer bounds required')
    if upper-lower+1>cell_limit:raise WorkLimit('finite descent population interval budget exceeded')
    domains=[list(range(lower,upper+1))]
    factor=predicate_factor(domains,[0],lambda n:classify_input(packet,n)['status']!='NOT_A_POWER',cell_limit=cell_limit)
    return GraphPopulation({'domains':domains,'factors':[factor]},cell_limit=cell_limit)
