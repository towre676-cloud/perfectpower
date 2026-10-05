"""Primitive coefficient-bearing power charts via exact prime-exponent lines.

Nonzero coefficients, positive exponents, all signs, and one zero chart.
Factorization is bounded trial division; exhaustion raises WorkLimit.
"""
import json
from math import gcd
from fractions import Fraction as Q
from . import polyalg as P
from .residue_cover import integer_polynomial
from .polynomial_composition import _AlgebraBudget
from .polynomial_charts import _predicate
from .semilinear_domains import semilinear_domain
from .divisor_square import WorkLimit


def factor_integer(n, *, work_limit=100000):
    if type(n) is not int or n < 1:
        raise ValueError('positive coefficient with at most 4096 bits required')
    if n.bit_length()>4096:raise WorkLimit('coefficient bit budget exceeded')
    if type(work_limit) is not int or work_limit < 1: raise ValueError('positive factor budget required')
    factors = {}; p = 2; used = 0
    while p*p <= n:
        used += 1
        if used > work_limit: raise WorkLimit('coefficient factorization budget exceeded')
        while n % p == 0:
            factors[p] = factors.get(p,0)+1; n //= p
        p = 3 if p == 2 else p+2
    if n > 1: factors[n] = factors.get(n,0)+1
    return factors


def primitive_power_charts(c,p,d,q,*,factor_limit=100000):
    if any(type(v) is not int for v in (c,p,d,q)) or not c or not d or not 1 <= p <= 64 or not 1 <= q <= 64:
        raise ValueError('nonzero integer coefficients and exponents in [1,64] required')
    fc=factor_integer(abs(c),work_limit=factor_limit);fd=factor_integer(abs(d),work_limit=factor_limit)
    g=gcd(p,q);a=p//g;b=q//g;rows=[];alpha=beta=1;obstruction=None
    for prime in sorted(fc.keys()|fd.keys()):
        delta=fd.get(prime,0)-fc.get(prime,0)
        if delta%g:
            obstruction={'prime':prime,'difference':delta,'gcd':g};break
        rhs=delta//g
        u=(rhs*pow(a,-1,b))%b if b>1 else 0
        v=(a*u-rhs)//b
        shift=max(0,(-v+a-1)//a)
        u+=b*shift;v+=a*shift
        assert u>=0 and v>=0 and (u<b or v<a) and p*u-q*v==delta
        if max(prime.bit_length()*u,prime.bit_length()*v)>16384:
            raise WorkLimit('primitive chart coefficient bit budget exceeded')
        alpha*=prime**u;beta*=prime**v
        if max(alpha.bit_length(),beta.bit_length())>16384: raise WorkLimit('primitive chart coefficient bit budget exceeded')
        rows.append({'prime':prime,'left_valuation':fc.get(prime,0),'right_valuation':fd.get(prime,0),
                     'left_exponent':u,'right_exponent':v})
    signs=[] if obstruction else [[sx,sy] for sx in (1,-1) for sy in (1,-1)
                                  if (1 if c>0 else -1)*sx**p==(1 if d>0 else -1)*sy**q]
    # Zero is kept independently: incompatible signs/valuations still allow x=y=0.
    return {'schema':'pp-primitive-power-charts/1','left_coefficient':c,'left_power':p,
            'right_coefficient':d,'right_power':q,'gcd':g,'left_step':b,'right_step':a,
            'left_factors':[[k,v] for k,v in sorted(fc.items())],
            'right_factors':[[k,v] for k,v in sorted(fd.items())],
            'valuation_rows':rows,'left_scale':None if obstruction else alpha,
            'right_scale':None if obstruction else beta,'signs':signs,'zero_point':[0,0],
            'obstruction':obstruction,'complete':True,'execution_verified':False}


def verify_primitive_charts(result,*,factor_limit=100000):
    try:
        rebuilt=primitive_power_charts(result['left_coefficient'],result['left_power'],
                                       result['right_coefficient'],result['right_power'],factor_limit=factor_limit)
        return rebuilt==result
    except (ValueError,TypeError,KeyError,ArithmeticError,WorkLimit): return False


def primitive_points(result,t):
    if type(t) is not int or t<0 or t.bit_length()>16384: raise ValueError('bounded nonnegative parameter required')
    if t==0:return [(0,0)]
    if not result['signs']:return []
    a,b=result['left_scale'],result['right_scale'];u,v=result['left_step'],result['right_step']
    if max(a.bit_length()+t.bit_length()*u,b.bit_length()+t.bit_length()*v)>1000000:
        raise WorkLimit('evaluated point bit budget exceeded')
    return sorted((sx*a*t**u,sy*b*t**v) for sx,sy in result['signs'])


def coefficient_presentations(coefficients,*,factor_limit=100000,algebra_limit=2000000):
    f=integer_polynomial(coefficients);n=len(f)-1
    if n<2:return []
    factors=factor_integer(abs(f[-1]),work_limit=factor_limit);budget=_AlgebraBudget(algebra_limit);found=[]
    for p in range(n,1,-1):
        if n%p:continue
        c=(1 if f[-1]>0 else -1)
        lead=1
        for prime,e in factors.items():c*=prime**(e%p);lead*=prime**(e//p)
        m=n//p;root=[Q(0)]*m+[Q(lead)]
        for j in range(1,m+1):
            current=budget.power(P.poly(root),p);index=n-j
            known=current[index] if index<len(current) else Q(0)
            root[m-j]=(Q(f[index],c)-known)/(p*lead**(p-1));budget.check(root)
        if any(v.denominator!=1 for v in root):continue
        coordinate=integer_polynomial(int(v) for v in root)
        residual=P.subtract(P.poly(f),P.scale(budget.power(P.poly(coordinate),p),c))
        if len(residual)==1:found.append({'coefficient':c,'power':p,'coordinate':list(coordinate),'offset':int(residual[0])})
    return found


def _coordinate(root,scale,sign,power):
    if len(root)==2:
        b,a=root;numerator=[-b]+[0]*(power-1)+[scale*sign]
        if a<0:numerator=[-v for v in numerator]
        return {'kind':'polynomial','numerator':numerator,'denominator':abs(a)}
    return {'kind':'fibre','coordinate':list(root),'target':[0]*power+[scale*sign]}


def _zero_coordinate(root):
    if len(root)==2:
        b,a=root
        return {'kind':'polynomial','numerator':[-b if a>0 else b],'denominator':abs(a)}
    return {'kind':'fibre','coordinate':list(root),'target':[0]}


def parameterize_coefficients(left,right,*,factor_limit=100000,algebra_limit=2000000,
                             period_limit=65536,node_limit=100000):
    left=integer_polynomial(left);right=integer_polynomial(right)
    base={'schema':'pp-coefficient-polynomial-charts/1','left':list(left),'right':list(right),
          'domain':'all integer x and y','execution_verified':False}
    lp=coefficient_presentations(left,factor_limit=factor_limit,algebra_limit=algebra_limit)
    rp=coefficient_presentations(right,factor_limit=factor_limit,algebra_limit=algebra_limit)
    pairs=[(a,b) for a in lp for b in rp if a['offset']==b['offset']]
    if not pairs:return {**base,'status':'UNRESOLVED','complete':False,'points':None,'reason':'no common-offset integral coefficient-power presentations'}
    a,b=min(pairs,key=lambda pair:(len(pair[0]['coordinate'])+len(pair[1]['coordinate']),-pair[0]['power']-pair[1]['power']))
    primitive=primitive_power_charts(a['coefficient'],a['power'],b['coefficient'],b['power'],factor_limit=factor_limit)
    charts=[{'signs':[1,1],'zero_chart':True,'x':_zero_coordinate(a['coordinate']),'y':_zero_coordinate(b['coordinate'])}]
    for sx,sy in primitive['signs']:
        charts.append({'signs':[sx,sy],'zero_chart':False,
                       'x':_coordinate(a['coordinate'],primitive['left_scale'],sx,primitive['left_step']),
                       'y':_coordinate(b['coordinate'],primitive['right_scale'],sy,primitive['right_step'])})
    used=0
    for i,chart in enumerate(charts):
        predicate=_predicate(chart,i)
        if i==0:predicate['args'][0]={'poly':[0,1],'relation':'='}
        chart['predicate']=predicate
        if used>=node_limit:raise WorkLimit('shared coefficient-domain node budget exceeded')
        chart['parameter_domain']=semilinear_domain(predicate,node_limit=node_limit-used,period_limit=period_limit)
        used+=chart['parameter_domain']['root_nodes']
    empty=all(c['parameter_domain']['cardinality']==0 for c in charts)
    return {**base,'status':'COMPLETE' if empty else 'GENERATOR','points':[] if empty else None,'complete':True,
            'left_presentation':a,'right_presentation':b,'primitive':primitive,'charts':charts,'root_nodes':used,
            'image_scope':'complete semilinear parameter images' if all(c[n]['kind']=='polynomial' for c in charts for n in ('x','y')) else 'complete integer fibres per parameter; nonlinear image not classified'}


def verify_coefficient_parameterization(result,**kwargs):
    try:
        rebuilt=parameterize_coefficients(result['left'],result['right'],**kwargs)
        return all(json.dumps(result[k],sort_keys=True)==json.dumps(v,sort_keys=True) for k,v in rebuilt.items())
    except (ValueError,TypeError,KeyError,ArithmeticError,WorkLimit):return False
