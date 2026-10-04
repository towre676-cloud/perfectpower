"""Exact multiplicative constraints recovered from August 2025 exponent work.

Rows A encode product_j x_j**A[i,j] = rhs[i], with positive integers x_j.
Signed exponents mean exact rational products. Completeness requires an
explicit coercive row combination; no numerical logarithms are used.
"""
from fractions import Fraction as Q
from math import lcm
from .integer_lifting import solve_integer,smith_certificate,_solve_with_certificate
from .integral_lattice import _matrix
from .exact_linear import solve,transpose


class MonomialLimit(ValueError):
    """A complete computation exceeded its budget; no truncated answer."""


class _Budget:
    def __init__(self,limit):
        if type(limit) is not int or limit<1:raise ValueError('positive integer work budget required')
        self.limit,self.used=limit,0
    def spend(self):
        self.used+=1
        if self.used>self.limit:raise MonomialLimit('monomial work budget exceeded')


def _constants(values,count):
    out=tuple(values)
    if len(out)!=count or any(type(x) not in (int,Q) or x<=0 for x in out):
        raise ValueError('one exact positive rational constant per row required')
    return tuple(map(Q,out))


def _power(value,exponent,bit_limit):
    if value==1:return Q(1)
    if abs(exponent)*max(value.numerator.bit_length(),value.denominator.bit_length())>bit_limit:
        raise MonomialLimit('multiplicative intermediate bit budget exceeded')
    return value**exponent


def _product(values,exponents,bit_limit):
    out=Q(1)
    for value,exponent in zip(values,exponents):
        out*=_power(Q(value),exponent,bit_limit)
        if max(out.numerator.bit_length(),out.denominator.bit_length())>bit_limit:
            raise MonomialLimit('multiplicative intermediate bit budget exceeded')
    return out


def _factor(n,budget):
    # Trial division supplies a proof of primality for the final cofactor;
    # probable-prime tests cannot underpin a complete valuation chart.
    remaining=n;out={};p=2
    while p*p<=remaining:
        budget.spend();e=0
        while remaining%p==0:
            budget.spend();remaining//=p;e+=1
        if e:out[p]=e
        p=3 if p==2 else p+2
    if remaining>1:out[remaining]=out.get(remaining,0)+1
    return out


def _valuation(value,p):
    n,d=value.numerator,value.denominator;a=b=0
    while n%p==0:n//=p;a+=1
    while d%p==0:d//=p;b+=1
    return a-b,Q(n,d)


def coercive_weights(matrix,weights=None):
    """Find/check w with c=w*A strictly positive in every coordinate.

    Automatic choices: sum all rows, or solve A^t*w=1 over Q and clear
    denominators. Failure means this detector found no certificate; it is
    not a declaration that the original integer solution set is infinite.
    """
    a=_matrix(matrix);m,n=len(a),len(a[0])
    if weights is None:
        weights=[1]*m
        c=[sum(a[i][j] for i in range(m)) for j in range(n)]
        if any(x<=0 for x in c):
            rational=solve(transpose(a),[1]*n)
            if rational is None:raise ValueError('supply a coercive integer row combination')
            denominator=lcm(*(x.denominator for x in rational))
            weights=[int(x*denominator) for x in rational]
    weights=tuple(weights)
    if len(weights)!=m or any(type(x) is not int for x in weights):
        raise ValueError('matching integer row weights required')
    c=[sum(weights[i]*a[i][j] for i in range(m)) for j in range(n)]
    if any(x<=0 for x in c):raise ValueError('row combination must be strictly positive in every column')
    return list(weights),c


def solve_monomial(matrix,rhs,*,weights=None,work_limit=1_000_000,
                   point_limit=100_000,bit_limit=100_000):
    """All positive integer solutions, when a coercive combination is checked.

    Combining rows yields product x_j**c_j=C, c_j>0. Thus every prime in a
    solution divides C and each prime valuation is bounded by v_p(C)/c_j.
    Finite nonnegative valuation fibres are joined, then original equations
    are checked by rational substitution. All budgets fail without a list.
    """
    a=_matrix(matrix);m,n=len(a),len(a[0]);rhs=_constants(rhs,m)
    if n>32 or m>128:raise MonomialLimit('monomial dimension budget exceeded')
    if any(type(v) is not int or v<1 for v in (point_limit,bit_limit)):
        raise ValueError('positive integer point and bit budgets required')
    budget=_Budget(work_limit);w,c=coercive_weights(a,weights)
    constant=_product(rhs,w,bit_limit)
    common={'matrix':[list(row) for row in a],'rhs':[str(x) for x in rhs],
            'domain':'positive integers','coercive_weights':w,'positive_exponents':c,
            'coercive_constant':str(constant),'complete':True,'execution_verified':False}
    if constant.denominator!=1:
        return dict(common,status='EMPTY_NONINTEGRAL_PRODUCT',points=[],work_used=budget.used)
    if n==1:
        # A single positive coordinate is pinned by x**c=C. Root extraction
        # avoids factoring an enormous known power just to rediscover its root.
        from .divisor_sum import exact_root
        budget.spend();value=constant.numerator;degree=c[0]
        if degree==1:root=value
        elif degree>value.bit_length():root=1 if value==1 else None
        else:root=exact_root(value,degree)
        if root is None:
            return dict(common,status='EMPTY_POWER_PRODUCT',points=[],method='exact positive power root',work_used=budget.used)
        for row,target in zip(a,rhs):
            budget.spend()
            if _product([root],row,bit_limit)!=target:
                return dict(common,status='EMPTY_FIXED_POINT_CONFLICT',points=[],method='exact positive power root',work_used=budget.used)
        return dict(common,status='MONOMIAL_COMPLETE_FINITE',points=[[root]],method='exact positive power root',work_used=budget.used)
    factors=_factor(constant.numerator,budget)
    residue=list(rhs);valuations={}
    for p in factors:
        column=[]
        for i,value in enumerate(residue):
            v,unit=_valuation(value,p);column.append(v);residue[i]=unit
        valuations[p]=column
    if any(value!=1 for value in residue):
        return dict(common,status='EMPTY_PRIME_SUPPORT_OBSTRUCTION',points=[],
                    factorization=[[p,e] for p,e in factors.items()],
                    unsupported_rhs_units=[str(x) for x in residue],work_used=budget.used)
    profiles=[]
    for p,total in factors.items():
        b=valuations[p]
        linear=solve_integer(a,b)
        if linear['status']!='INTEGER_AFFINE_FIBRE':
            return dict(common,status='EMPTY_VALUATION_OBSTRUCTION',points=[],prime=p,
                        obstruction=linear,factorization=[[p,e] for p,e in factors.items()],work_used=budget.used)
        accepted=[]
        def walk(index,remaining,vector):
            budget.spend()
            if index==n-1:
                if remaining%c[index]:return
                candidate=vector+[remaining//c[index]]
                if all(sum(x*y for x,y in zip(row,candidate))==target for row,target in zip(a,b)):
                    accepted.append(candidate)
                return
            for value in range(remaining//c[index]+1):
                walk(index+1,remaining-c[index]*value,vector+[value])
        walk(0,total,[])
        profiles.append({'prime':p,'coercive_valuation':total,'rhs_valuations':b,
                         'profiles':accepted,'integer_fibre':linear})
        if not accepted:
            return dict(common,status='EMPTY_NONNEGATIVE_VALUATION_FIBRE',points=[],
                        factorization=[[p,e] for p,e in factors.items()],valuation_profiles=profiles,
                        work_used=budget.used)
    points=[[1]*n]
    for chart in profiles:
        if len(points)*len(chart['profiles'])>point_limit:raise MonomialLimit('complete monomial point list exceeds budget')
        joined=[];p=chart['prime']
        for point in points:
            for exponents in chart['profiles']:
                budget.spend();joined.append([x*p**e for x,e in zip(point,exponents)])
        points=joined
    for point in points:
        for row,value in zip(a,rhs):
            budget.spend()
            if _product(point,row,bit_limit)!=value:raise AssertionError('monomial source substitution failed')
    return dict(common,status='MONOMIAL_COMPLETE_FINITE',points=sorted(points),
                factorization=[[p,e] for p,e in factors.items()],valuation_profiles=profiles,
                work_used=budget.used)


def eliminate_exponents(matrix,eliminated,*,rhs=None,bit_limit=100_000,**budgets):
    """All integer row combinations cancelling the selected variable exponents.

    Returns a saturated basis in row-combination coordinates. Each resulting
    Laurent relation is a consequence on nonzero variables. It is not a
    complete existential projection onto retained variable values: roots,
    signs and integer lifting may add further restrictions.
    """
    a=_matrix(matrix);m,n=len(a),len(a[0]);indices=tuple(eliminated)
    if not indices or len(set(indices))!=len(indices) or any(type(j) is not int or not 0<=j<n for j in indices):
        raise ValueError('distinct in-range eliminated columns required')
    if type(bit_limit) is not int or bit_limit<1:raise ValueError('positive integer bit budget required')
    rhs=_constants(rhs if rhs is not None else [1]*m,m)
    equations=[[row[j] for row in a] for j in indices]
    kernel=solve_integer(equations,[0]*len(equations),**budgets)
    relations=[]
    for combination in kernel['kernel_basis']:
        exponents=[sum(combination[i]*a[i][j] for i in range(m)) for j in range(n)]
        if any(exponents[j] for j in indices):raise AssertionError('elimination failed')
        relations.append({'combination':combination,'exponents':exponents,
                          'rhs':str(_product(rhs,combination,bit_limit))})
    return {'status':'COMPLETE_ROW_COMBINATION_MODULE','relations':relations,
            'eliminated_columns':list(indices),'certificate':kernel['certificate'],
            'domain':'nonzero variables for Laurent consequences; positive integers for valuation solving',
            'projection_complete':False,'execution_verified':False}


def solve_rational_monomial(matrix,rhs,*,work_limit=1_000_000,bit_limit=100_000,**budgets):
    """Complete positive-rational multiplicative fibre, or prime obstruction.

    x_i = particular_i * product_j parameter_j**kernel[j][i], with every
    parameter an arbitrary positive rational. All prime valuations use the
    saturated Z-kernel, so denominator clearing cannot lose solutions.
    """
    a=_matrix(matrix);m,n=len(a),len(a[0]);rhs=_constants(rhs,m)
    if n>32 or m>128:raise MonomialLimit('monomial dimension budget exceeded')
    if type(bit_limit) is not int or bit_limit<1:raise ValueError('positive integer bit budget required')
    budget=_Budget(work_limit);initial=solve_integer(a,[0]*m,**budgets)
    cert=initial['certificate'];primes=set();cache={}
    for value in rhs:
        for integer in (value.numerator,value.denominator):
            if integer.bit_length()>bit_limit:raise MonomialLimit('rational input bit budget exceeded')
            if integer not in cache:cache[integer]=_factor(integer,budget)
            primes.update(cache[integer])
    point=[Q(1)]*n;charts=[]
    common={'matrix':[list(row) for row in a],'rhs':[str(v) for v in rhs],
            'domain':'positive rationals','certificate':cert,'execution_verified':False}
    for p in sorted(primes):
        values=[_valuation(value,p)[0] for value in rhs]
        chart=_solve_with_certificate(cert,values)
        if chart['status']!='INTEGER_AFFINE_FIBRE':
            return dict(common,status='RATIONAL_MONOMIAL_PRIME_OBSTRUCTION',prime=p,
                        obstruction=chart,complete=True,work_used=budget.used)
        for i,e in enumerate(chart['particular']):
            point[i]*=_power(Q(p),e,bit_limit)
            if max(point[i].numerator.bit_length(),point[i].denominator.bit_length())>bit_limit:
                raise MonomialLimit('rational point bit budget exceeded')
        charts.append({'prime':p,'rhs_valuations':values,'particular_valuations':chart['particular']})
    for row,value in zip(a,rhs):
        if _product(point,row,bit_limit)!=value:raise AssertionError('rational monomial substitution failed')
    return dict(common,status='RATIONAL_MONOMIAL_FIBRE',particular=[str(x) for x in point],
                parameter_exponents=initial['kernel_basis'],parameter_count=n-cert['rank'],
                parameter_domain='arbitrary positive rationals',complete=True,
                prime_charts=charts,work_used=budget.used)


OLD_VARIABLES=('T','K','P','tau','R','E','g','a','zeta')
OLD_MATRIX=((6,3,-4,0,0,0,0,0,0),(0,18,0,1,-9,0,0,0,0),
            (0,0,0,-5,0,60,-24,0,0),(0,0,0,0,0,-2,0,5,-1))


def recovered_2025_packet():
    cert=smith_certificate(OLD_MATRIX)
    kernel=solve_integer(OLD_MATRIX,[0]*4)
    elimination=eliminate_exponents(OLD_MATRIX,[1,5])
    # Preserve the historical explicit consequences in the original coordinates.
    combinations=((6,-1,0,0),(0,0,1,30));consequences=[]
    for combination in combinations:
        exponents=[sum(combination[i]*OLD_MATRIX[i][j] for i in range(4)) for j in range(9)]
        consequences.append({'combination':list(combination),'exponents':exponents})
    return {'source_date':'2025-08-17','variables':OLD_VARIABLES,'matrix':OLD_MATRIX,
            'smith_certificate':cert,'integer_kernel':kernel,
            'corrected_smith_factors':[1,1,1,3],'historical_claimed_factors':[1,1,1,1],
            'cube_compatibility':'rhs[2]/rhs[1] must be a rational cube','hidden_variable_elimination':elimination,
            'historical_consequences':consequences,
            'interpretation':'Five free integral exponent directions, not evidence of a B5 Weyl action or a physical law.',
            'execution_verified':False}
