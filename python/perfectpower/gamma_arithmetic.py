"""Exact structural Gamma arithmetic on nonnegative integer indices.

No floating Gamma evaluation: finite shifts become polynomials, factorial
ratios become finite prime-valuation sums, and consecutive ratios become
polynomial-coefficient recurrences. Analytic continuation is not presumed.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, gcd, isqrt
import json
from . import polyalg as P
from .divisor_square import WorkLimit
from .residue_cover import integer_polynomial,evaluate


def _natural(n):
    if type(n) is not int or n<0 or n.bit_length()>4096:
        raise ValueError('nonnegative integer index of at most 4096 bits required')


def _degree(d):
    if type(d) is not int or not 2<=d<=64:raise ValueError('power exponent in [2,64] required')


def _budget(n):
    if type(n) is not int or n<1:raise ValueError('positive work budget required')


def _slopes(values):
    values=tuple(values)
    if len(values)>32 or any(type(a) is not int or not 1<=a<=4096 for a in values):
        raise ValueError('at most 32 positive integer slopes in [1,4096] required')
    return values


def _prime(p):
    return type(p) is int and 2<=p<=2000000 and all(p%q for q in range(2,isqrt(p)+1))


def _same(a,b):return json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)


def normalize(spec):
    """Compile fixed-width expressions to numerator/denominator, preserving domain."""
    if not isinstance(spec,dict):raise ValueError('structured Gamma expression required')
    kind=spec.get('kind')
    allowed={'gamma_shift':{'kind','a','b','shift'},'rising':{'kind','a','b','width'},
             'binomial':{'kind','width'},'finite_product':{'kind','factors'}}
    if kind not in allowed or not set(spec)<=allowed[kind]:raise ValueError('unsupported expression or field')
    denominator=1;poly=P.ONE
    if kind in ('gamma_shift','rising'):
        a=spec.get('a',1);b=spec.get('b',1);width=spec.get('shift' if kind=='gamma_shift' else 'width')
        if type(a) is not int or type(b) is not int or abs(a)>1000000 or abs(b)>1000000:
            raise ValueError('bounded integer slope and base required')
        if kind=='gamma_shift' and (a<0 or b<1):
            raise ValueError('nonnegative slope and positive Gamma base required')
        factors=[(b+j,a) for j in range(width)] if type(width) is int and 0<=width<=64 else None
    elif kind=='binomial':
        width=spec.get('width')
        factors=[(-j,1) for j in range(width)] if type(width) is int and 0<=width<=64 else None
        if factors is not None:denominator=factorial(width)
    else:
        factors=spec.get('factors')
        if not isinstance(factors,(list,tuple)) or len(factors)>64:raise ValueError('at most 64 affine factors required')
        for factor in factors:
            if not isinstance(factor,(list,tuple)) or len(factor)!=2 or any(type(c) is not int or abs(c)>1000000 for c in factor):
                raise ValueError('integer affine factors [constant,slope] required')
    if factors is None:raise ValueError('fixed width in [0,64] required')
    for factor in factors:poly=P.mul(poly,P.poly(factor))
    coefficients=integer_polynomial(int(c) for c in poly)
    common=gcd(denominator,gcd(*coefficients))
    coefficients=tuple(c//common for c in coefficients);denominator//=common
    return {'schema':'pp-gamma-normalization/1','source':spec,'numerator':coefficients,
            'denominator':denominator,'domain':{'index':'n','lower':0},
            'meaning':'exact finite product on the stated natural-index domain',
            'execution_verified':False}


def verify_normalization(receipt):
    try:return _same(normalize(receipt['source']),receipt)
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def analyze_expression(spec,d=2,*,interval=None,work_limit=100000):
    """D*y^d=N(n) becomes (D*y)^d=D^(d-1)*N(n), with image checks."""
    from .simplifier import analyze_power
    _degree(d);normal=normalize(spec);den=normal['denominator']
    transformed=tuple(c*den**(d-1) for c in normal['numerator'])
    clipped=None
    if interval is not None:
        if not isinstance(interval,(list,tuple)) or len(interval)!=2 or any(type(x) is not int for x in interval) or interval[0]>interval[1]:
            raise ValueError('ordered closed integer interval required')
        clipped=[max(0,interval[0]),interval[1]]
    try:
        analysis=analyze_power(transformed,d,interval=clipped if clipped is not None and clipped[0]<=clipped[1] else None,work_limit=work_limit)
    except WorkLimit as error:
        analysis={'schema':'pp-symbolic-power-residual/1','global':{'status':'UNRESOLVED','points':None},
                  'bounded':None if clipped is None else {'status':'UNRESOLVED','interval':clipped,'reason':str(error)},
                  'residual':{'scale':den,'degree':d,'numerator':normal['numerator']},'reason':str(error)}
    def lift(points):return sorted((n,z//den) for n,z in points if n>=0 and z%den==0)
    global_result=analysis['global'];bounded=analysis['bounded']
    global_points=lift(global_result['points']) if global_result['status']=='COMPLETE' else None
    if clipped is not None and clipped[0]>clipped[1]:bounded={'status':'COMPLETE','interval':clipped,'points':[],'scope':'empty natural-index domain'}
    elif bounded is not None:bounded={**bounded,'points':lift(bounded['points'])} if bounded['status']=='COMPLETE' else bounded
    return {'schema':'pp-gamma-power-analysis/1','normalization':normal,'degree':d,
            'transformed_analysis':analysis,'image_condition':{'witness_divisible_by':den,'index_at_least':0},
            'global_status':global_result['status'],'global_points':global_points,'bounded':bounded,
            'requested_interval':interval,'work_limit':work_limit,'execution_verified':False}


def verify_expression(receipt):
    try:return _same(receipt,analyze_expression(receipt['normalization']['source'],receipt['degree'],interval=receipt['requested_interval'],work_limit=receipt['work_limit']))
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def _legendre(n,p):
    terms=[]
    while n:
        n//=p
        if n:terms.append(n)
    return sum(terms),terms


def legendre(n,p):
    _natural(n)
    if not _prime(p):raise ValueError('certified prime at most 2000000 required')
    exponent,terms=_legendre(n,p)
    return {'prime':p,'factorial_index':n,'exponent':exponent,'floor_terms':terms}


def valuation(n,numerator,denominator,p):
    _natural(n);a=_slopes(numerator);b=_slopes(denominator)
    if not _prime(p):raise ValueError('certified prime at most 2000000 required')
    top=[_legendre(c*n,p) for c in a];bottom=[_legendre(c*n,p) for c in b]
    return {'prime':p,'exponent':sum(e for e,_ in top)-sum(e for e,_ in bottom),
            'numerator_terms':[t for _,t in top],'denominator_terms':[t for _,t in bottom]}


def landau(numerator,denominator,*,work_limit=100000):
    """Finite exact certificate of Landau's balanced step-function criterion."""
    a=_slopes(numerator);b=_slopes(denominator);_budget(work_limit)
    if sum(a)!=sum(b):raise ValueError('balanced slopes required for the periodic criterion')
    if (sum(a)+sum(b)+1)*max(1,len(a)+len(b))>work_limit:
        raise WorkLimit('Landau breakpoint estimate exceeds budget')
    breaks=sorted({Q(0),Q(1)}|{Q(j,c) for c in a+b for j in range(1,c)})
    intervals=[]
    for left,right in zip(breaks,breaks[1:]):
        delta=sum((c*left).numerator//(c*left).denominator for c in a)-sum((c*left).numerator//(c*left).denominator for c in b)
        intervals.append({'left':str(left),'right':str(right),'delta':delta})
    return {'schema':'pp-landau/1','numerator':a,'denominator':b,'balanced':True,
            'integral_for_all_n':all(c['delta']>=0 for c in intervals),'intervals':intervals,
            'work_limit':work_limit,'execution_verified':False,'theorem':'Landau balanced factorial-ratio criterion; finite rational step certificate'}


def verify_landau(receipt):
    try:return _same(receipt,landau(receipt['numerator'],receipt['denominator'],work_limit=receipt['work_limit']))
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


@lru_cache(maxsize=8)
def _primes(limit):
    sieve=bytearray(b'\1')*(limit+1)
    sieve[:2]=b'\0'*min(2,limit+1)
    for p in range(2,isqrt(limit)+1):
        if sieve[p]:sieve[p*p:limit+1:p]=b'\0'*(((limit-p*p)//p)+1)
    return tuple(i for i in range(2,limit+1) if sieve[i])


CHEAP_PRIMES=(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97)


def factorial_power(n,numerator,denominator,d=2,*,complete=False,work_limit=100000):
    """Try cheap obstruction witnesses before any full prime enumeration."""
    _natural(n);_degree(d);_budget(work_limit);a=_slopes(numerator);b=_slopes(denominator)
    if type(complete) is not bool:raise ValueError('complete must be Boolean')
    result={'schema':'pp-factorial-power/1','n':n,'numerator':a,'denominator':b,'degree':d,
            'requested_complete':complete,'work_limit':work_limit,'status':'UNRESOLVED','valuations':[],
            'factorials_constructed':0,'execution_verified':False}
    if n==0:result.update(status='POWER',proof={'kind':'zero_index','root_factorization':[]});return result
    # Cancel identical slopes before recognizing the parameterized family.
    aa=list(a);bb=list(b)
    for c in list(aa):
        if c in bb:aa.remove(c);bb.remove(c)
    if not aa and not bb:
        result.update(status='POWER',proof={'kind':'cancelled_identity','root_factorization':[]});return result
    if aa==[2] and sorted(bb)==[1,1]:
        result.update(status='NOT_POWER',proof={'kind':'central_binomial','theorem':'PerfectPower.GammaArithmetic.central_not_power'});return result
    bound=max(a+b,default=0)*n;work=0;checked=set()
    for p in CHEAP_PRIMES:
        if p>bound:break
        row=valuation(n,a,b,p);cost=sum(len(t)+1 for t in row['numerator_terms']+row['denominator_terms'])
        if work+cost>work_limit:result['reason']='division budget exceeded';return result
        work+=cost;result['valuations'].append(row);checked.add(p)
        e=row['exponent']
        if e<0 or e%d:
            result.update(status='NOT_INTEGER' if e<0 else 'NOT_POWER',proof={'kind':'prime_obstruction','prime':p,'exponent':e},division_work=work);return result
    result['unit_filters']=[]
    for p,depth in ((2,3),(3,2),(5,1)):
        cost=(len(a)+len(b))*(p**depth+(bound.bit_length()+1))
        if work+cost>work_limit:continue
        local=local_factorial_obstruction(n,a,b,d,p,depth,work_limit=work_limit)
        result['unit_filters'].append(local);work+=cost
        if local['obstruction']:
            result.update(status='NOT_POWER',proof={'kind':'unit_obstruction','prime':p,'depth':depth},division_work=work);return result
    if not complete and bound<=97 and set(_primes(bound))<=checked:
        roots=[[row['prime'],row['exponent']//d] for row in result['valuations'] if row['exponent']]
        result.update(status='POWER',proof={'kind':'all_prime_valuations','largest_factorial_index':bound,'root_factorization':roots},division_work=work);return result
    if not complete:
        result.update(reason='tested primes and units give only necessary conditions',division_work=work);return result
    if bound>min(2000000,work_limit):
        result.update(reason='complete prime sieve exceeds budget',division_work=work);return result
    for p in _primes(bound):
        if p in checked:continue
        row=valuation(n,a,b,p);cost=sum(len(t)+1 for t in row['numerator_terms']+row['denominator_terms'])
        if work+cost>work_limit:result.update(reason='division budget exceeded',division_work=work);return result
        work+=cost;result['valuations'].append(row);e=row['exponent']
        if e<0 or e%d:
            result.update(status='NOT_INTEGER' if e<0 else 'NOT_POWER',proof={'kind':'prime_obstruction','prime':p,'exponent':e},division_work=work);return result
    roots=[[row['prime'],row['exponent']//d] for row in result['valuations'] if row['exponent']]
    result.update(status='POWER',proof={'kind':'all_prime_valuations','largest_factorial_index':bound,'root_factorization':roots},division_work=work)
    return result


def verify_factorial_power(receipt):
    try:return _same(receipt,factorial_power(receipt['n'],receipt['numerator'],receipt['denominator'],receipt['degree'],complete=receipt['requested_complete'],work_limit=receipt['work_limit']))
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def scan_factorial(numerator,denominator,d=2,*,lo=0,hi=100,work_limit=100000):
    _natural(lo);_natural(hi);_budget(work_limit)
    if lo>hi:raise ValueError('ordered natural interval required')
    if hi-lo+1>work_limit:raise WorkLimit('index budget exceeded')
    receipts=[];hits=[]
    for n in range(lo,hi+1):
        row=factorial_power(n,numerator,denominator,d,complete=True,work_limit=work_limit)
        if row['status']=='UNRESOLVED':raise WorkLimit('an index remains unresolved; no partial complete hit list')
        receipts.append(row)
        if row['status']=='POWER':hits.append(n)
    return {'schema':'pp-factorial-scan/1','interval':[lo,hi],'hits':hits,'receipts':receipts,'complete':True,'execution_verified':False}


def hypergeometric(numerator,denominator):
    """Q(n) A(n+1)=P(n) A(n), without cancelling transient factors."""
    a=_slopes(numerator);b=_slopes(denominator)
    if sum(a)+sum(b)>128:raise WorkLimit('hypergeometric polynomial degree budget exceeded')
    top=P.ONE;bottom=P.ONE
    for c in a:
        for j in range(1,c+1):top=P.mul(top,P.poly((j,c)))
    for c in b:
        for j in range(1,c+1):bottom=P.mul(bottom,P.poly((j,c)))
    if sum(a)+sum(b)>128:raise WorkLimit('hypergeometric polynomial degree budget exceeded')
    return {'schema':'pp-hypergeometric/1','numerator_slopes':a,'denominator_slopes':b,
            'P':[int(c) for c in top],'Q':[int(c) for c in bottom],'initial':'1','domain':'n >= 0',
            'denominator_nonzero':'each c*n+j is positive on the domain','execution_verified':False,
            'generating_function_equation':{'theta_Q_shift':[int(c) for c in P.compose_linear(bottom,-1,1)],
                'x_theta_P':[int(c) for c in top],'constant_boundary':int(evaluate(bottom,-1)),
                'meaning':'Q(theta-1) F = x P(theta) F + Q(-1) A(0); formal series, not analytic convergence'}}


def hypergeometric_terms(receipt,count,*,bit_limit=16384):
    if not _same(receipt,hypergeometric(receipt['numerator_slopes'],receipt['denominator_slopes'])):raise ValueError('invalid recurrence certificate')
    if type(count) is not int or not 0<=count<=100000 or type(bit_limit) is not int or bit_limit<1:raise ValueError('bounded term and bit budgets required')
    out=[];value=Q(1)
    for n in range(count):
        if max(value.numerator.bit_length(),value.denominator.bit_length())>bit_limit:raise WorkLimit('exact sequence bit budget exceeded')
        out.append(str(value));value*=Q(evaluate(receipt['P'],n),evaluate(receipt['Q'],n))
    return out


@lru_cache(maxsize=16)
def _unit_prefix(p,depth):
    modulus=p**depth;prefix=[1]
    for k in range(1,modulus+1):prefix.append(prefix[-1]*(k if k%p else 1)%modulus)
    return tuple(prefix)


def factorial_unit(n,p,depth,*,work_limit=100000):
    """Strip all p powers BEFORE modular inversion, recursively retaining units."""
    _natural(n);_budget(work_limit)
    if not _prime(p) or type(depth) is not int or not 1<=depth<=16:raise ValueError('prime and depth in [1,16] required')
    modulus=p**depth
    if modulus>work_limit:raise WorkLimit('unit block exceeds budget')
    prefix=_unit_prefix(p,depth)
    unit=1;current=n;levels=[]
    while current:
        blocks,remainder=divmod(current,modulus)
        part=pow(prefix[-1],blocks,modulus)*prefix[remainder]%modulus
        levels.append({'index':current,'blocks':blocks,'remainder':remainder,'unit':part})
        unit=unit*part%modulus;current//=p
    return {'n':n,'prime':p,'depth':depth,'modulus':modulus,'valuation':_legendre(n,p)[0],
            'unit':unit,'levels':levels,'work_limit':work_limit,'execution_verified':False}


def ratio_unit(n,numerator,denominator,p,depth,*,work_limit=100000):
    _natural(n);a=_slopes(numerator);b=_slopes(denominator)
    top=[factorial_unit(c*n,p,depth,work_limit=work_limit) for c in a]
    bottom=[factorial_unit(c*n,p,depth,work_limit=work_limit) for c in b]
    modulus=p**depth;unit=1
    for row in top:unit=unit*row['unit']%modulus
    for row in bottom:unit=unit*pow(row['unit'],-1,modulus)%modulus
    return {'n':n,'numerator_slopes':a,'denominator_slopes':b,'work_limit':work_limit,'prime':p,'depth':depth,'modulus':modulus,'exponent':sum(r['valuation'] for r in top)-sum(r['valuation'] for r in bottom),'unit':unit,'numerator_units':top,'denominator_units':bottom,'execution_verified':False}


def local_factorial_obstruction(n,numerator,denominator,d,p,depth,*,work_limit=100000):
    """Necessary valuation AND unit power tests; survival is not a solution."""
    from .factored_sieve import power_residue
    _degree(d)
    receipt=ratio_unit(n,numerator,denominator,p,depth,work_limit=work_limit)
    e=receipt['exponent']
    obstruction=e<0 or e%d!=0 or not power_residue(receipt['unit'],d,p,depth)
    return {'schema':'pp-factorial-local/1','degree':d,'ratio_unit':receipt,
            'obstruction':obstruction,'scope':'necessary local conditions only','execution_verified':False}


def analyze_gamma(spec,d=2,*,n=None,interval=None,complete=False,work_limit=100000):
    """One entry point: exact normalization OR factorial structure and queries."""
    _degree(d);_budget(work_limit)
    if type(complete) is not bool:raise ValueError('complete must be Boolean')
    if not isinstance(spec,dict):raise ValueError('structured expression required')
    kind=spec.get('kind')
    canonical=None
    if kind=='factorial':
        if not set(spec)<={'kind','a'}:raise ValueError('unsupported factorial field')
        a=spec.get('a',1)
        if type(a) is not int or not 0<=a<=4096:raise ValueError('factorial slope in [0,4096] required')
        canonical={'kind':'factorial_ratio','numerator':[a] if a else [],'denominator':[]}
    elif kind=='central_binomial':
        if set(spec)!={'kind'}:raise ValueError('unsupported central-binomial field')
        canonical={'kind':'factorial_ratio','numerator':[2],'denominator':[1,1]}
    elif kind=='multinomial':
        if set(spec)!={'kind','parts'}:raise ValueError('multinomial parts required')
        parts=_slopes(spec['parts']);total=sum(parts)
        if total>4096:raise ValueError('multinomial total slope at most 4096 required')
        canonical={'kind':'factorial_ratio','numerator':[total] if total else [],'denominator':list(parts)}
    elif kind=='binomial_linear':
        if set(spec)!={'kind','top','bottom'}:raise ValueError('linear top and bottom slopes required')
        a,b=spec['top'],spec['bottom']
        if type(a) is not int or type(b) is not int or not 0<=b<=a<=4096:raise ValueError('0 <= bottom <= top <= 4096 required')
        canonical={'kind':'factorial_ratio','numerator':[a] if a else [],'denominator':[v for v in (b,a-b) if v]}
    if canonical is not None:
        result=analyze_gamma(canonical,d,n=n,interval=interval,complete=complete,work_limit=work_limit)
        result['input_source']=spec
        return result
    if spec.get('kind')!='factorial_ratio':
        if n is not None:interval=[n,n]
        return analyze_expression(spec,d,interval=interval,work_limit=work_limit)
    if set(spec)!={'kind','numerator','denominator'}:raise ValueError('factorial-ratio slopes required')
    a=_slopes(spec['numerator']);b=_slopes(spec['denominator']);integrality=None;recurrence=None;attempts=[]
    if sum(a)==sum(b):
        try:integrality=landau(a,b,work_limit=work_limit)
        except WorkLimit as error:attempts.append(str(error))
    try:recurrence=hypergeometric(a,b)
    except WorkLimit as error:attempts.append(str(error))
    aa=list(a);bb=list(b)
    for c in list(aa):
        if c in bb:aa.remove(c);bb.remove(c)
    global_result={'status':'UNRESOLVED','scope':'all nonnegative integer n'}
    if aa==[2] and sorted(bb)==[1,1]:
        global_result={'status':'COMPLETE','scope':'all nonnegative integer n','points':[(0,y) for y in ([-1,1] if d%2==0 else [1])],
                       'theorem':'PerfectPower.GammaArithmetic.central_not_int_power'}
    elif not aa and not bb:
        global_result={'status':'GENERATOR','scope':'all nonnegative integer n','generator':{'n':'any nonnegative integer','y':[-1,1] if d%2==0 else [1]}}
    point=None if n is None else factorial_power(n,a,b,d,complete=complete,work_limit=work_limit)
    bounded=None
    if interval is not None:
        if not isinstance(interval,(list,tuple)) or len(interval)!=2 or any(type(x) is not int for x in interval) or interval[0]>interval[1]:
            raise ValueError('ordered closed integer interval required')
        lo,hi=max(0,interval[0]),interval[1]
        if lo>hi:bounded={'status':'COMPLETE','interval':[lo,hi],'hits':[],'receipts':[]}
        elif global_result['status']=='COMPLETE':
            points=[p for p in global_result['points'] if lo<=p[0]<=hi]
            bounded={'status':'COMPLETE','interval':[lo,hi],'hits':sorted({p[0] for p in points}),'points':points,'proof':'restriction of complete global theorem'}
        elif global_result['status']=='GENERATOR':
            bounded={'status':'GENERATOR','interval':[lo,hi],'generator':global_result['generator'],'complete':True}
        else:
            try:bounded={'status':'COMPLETE',**scan_factorial(a,b,d,lo=lo,hi=hi,work_limit=work_limit)}
            except WorkLimit as error:bounded={'status':'UNRESOLVED','interval':[lo,hi],'reason':str(error)}
    return {'schema':'pp-gamma-compiler/1','source':spec,'degree':d,'global':global_result,
            'integrality':integrality,'hypergeometric':recurrence,'point':point,'bounded':bounded,
            'attempts':attempts,'parameters':{'n':n,'interval':interval,'complete':complete,'work_limit':work_limit},'execution_verified':False}


def verify_gamma(receipt):
    try:
        if receipt['schema']=='pp-gamma-power-analysis/1':return verify_expression(receipt)
        return _same(receipt,analyze_gamma(receipt.get('input_source',receipt['source']),receipt['degree'],**receipt['parameters']))
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def finite_mellin(indices,s):
    """Exact Gamma(s)*Z(s) for a finite positive hit set and integer s>0."""
    indices=tuple(indices)
    if len(indices)>100000 or any(type(n) is not int or n<1 or n.bit_length()>4096 for n in indices) or len(set(indices))!=len(indices):
        raise ValueError('distinct positive integer hit indices required')
    if type(s) is not int or not 1<=s<=64:raise ValueError('positive integer Mellin exponent at most 64 required')
    if s*sum(n.bit_length() for n in indices)>1000000:
        raise WorkLimit('finite Mellin rational denominator estimate exceeds bit budget')
    z=sum((Q(1,n**s) for n in indices),Q(0));value=factorial(s-1)*z
    return {'schema':'pp-finite-mellin/1','indices':indices,'s':s,'Gamma_s':factorial(s-1),
            'Z_s':str(z),'integral':str(value),'domain':'finite positive hit set; s positive integer',
            'identity':'integral_0^infinity sum(exp(-t*n))*t^(s-1) dt = Gamma(s)*sum(n^(-s))','execution_verified':False}


def beta_period(m):
    """Exact symbolic branch-path reference; no marked period-matrix claim."""
    if type(m) is not int or not 3<=m<=1000000:raise ValueError('curve exponent at least three required')
    return {'schema':'pp-beta-period/1','m':m,'curve':'y^2=1-x^m','path':'x from 0 to 1; positive real square-root branch',
            'beta_arguments':[str(Q(1,m)),'1/2'],'prefactor':str(Q(1,m)),
            'gamma_numerator':[str(Q(1,m)),'1/2'],'gamma_denominator':str(Q(1,m)+Q(1,2)),
            'scope':'exact symbolic integral identity; no numerical error estimate or full period matrix','execution_verified':False}


def verify_unit(receipt):
    try:return _same(receipt,factorial_unit(receipt['n'],receipt['prime'],receipt['depth'],work_limit=receipt['work_limit']))
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def verify_ratio_unit(receipt):
    try:return _same(receipt,ratio_unit(receipt['n'],receipt['numerator_slopes'],receipt['denominator_slopes'],receipt['prime'],receipt['depth'],work_limit=receipt['work_limit']))
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def verify_local(receipt):
    try:
        r=receipt['ratio_unit']
        return _same(receipt,local_factorial_obstruction(r['n'],r['numerator_slopes'],r['denominator_slopes'],receipt['degree'],r['prime'],r['depth'],work_limit=r['work_limit']))
    except (ValueError,TypeError,KeyError,ArithmeticError):return False
