"""Exact certificates for rational quotient maps and reciprocal discovery.

Candidate maps are u=N(x)/D(x), v=y S(x)/T(x). Coefficients lie in Q(t).
Discovery is complete only for the explicitly tested candidate list.
"""
from fractions import Fraction as Q
from .rational_functions import RationalFunction as RF, AlgebraBudget, solve_many, determinant
from . import field_polynomials as F
from .curve_families import CurveFamily
from .elliptic_quotients import discover_elliptic_quotients


def parse_source(specification):
    if not isinstance(specification,dict) or 'coefficients' not in specification or set(specification)-{'coefficients','work_limit','degree_limit','bit_limit'}:raise ValueError('source coefficients and optional algebra budgets required')
    raw=specification['coefficients']
    if not isinstance(raw,list) or not 4<=len(raw)<=9:raise ValueError('source x degree three through eight required')
    limits={k:specification[k] for k in ('work_limit','degree_limit','bit_limit') if k in specification};budget=AlgebraBudget(**limits)
    f=F.trim([RF.parse(a,budget) for a in raw])
    if f[-1]!=1 or any(a.d!=(1,) or len(a.n)>9 for a in f):raise ValueError('monic polynomial parameter coefficients of degree at most eight required')
    if len(F.extended_gcd(f,F.derivative(f))[0])!=1:raise ValueError('generically singular source')
    return f,limits,budget


def resultant_discriminant(f):
    m=len(f)-1;dx=F.derivative(f);zero=f[0].coerce(0);matrix=[]
    for k in range(m-1):matrix.append([zero]*k+list(reversed(f))+[zero]*(m-2-k))
    for k in range(m):matrix.append([zero]*k+list(reversed(dx))+[zero]*(m-1-k))
    return (-1)**(m*(m-1)//2)*determinant(matrix)/f[-1]


def verify_rational_quotient(specification,candidate):
    f,limits,budget=parse_source(specification);zero=f[0].coerce(0);one=zero.coerce(1)
    allowed={'u_numerator','u_denominator','v_numerator','v_denominator','target_degree','label'}
    if not isinstance(candidate,dict) or set(candidate)-allowed or 'u_numerator' not in candidate:raise ValueError('bounded rational-map candidate required')
    def read(key,default):
        raw=candidate.get(key,default)
        if not isinstance(raw,list) or not 1<=len(raw)<=9:raise ValueError('rational-map polynomial degree at most eight required')
        return F.trim([RF.parse(v,budget) for v in raw])
    n,d,s,t=read('u_numerator',[0,0,1]),read('u_denominator',[1]),read('v_numerator',[1]),read('v_denominator',[1])
    if not any(d) or not any(t) or not any(s):raise ValueError('nonzero map denominator and y multiplier required')
    common=F.extended_gcd(n,d)[0];n=F.divide(n,common)[0];d=F.divide(d,common)[0]
    du=F.add(F.product(F.derivative(n),d),F.scale(F.product(n,F.derivative(d)),-1))
    if not any(du):raise ValueError('constant quotient coordinate')
    degree=candidate.get('target_degree',3)
    if type(degree) is not int or degree not in (3,4,5,6):raise ValueError('target degree three through six required')
    source_genus=(len(f)-2)//2;target_genus=(degree-1)//2
    if not target_genus<source_genus:raise ValueError('quotient target must have smaller positive genus')
    columns=[F.product(F.product(F.power(n,j),F.power(d,degree-j)),F.power(t,2)) for j in range(degree+1)]
    target=F.product(F.product(f,F.power(s,2)),F.power(d,degree))
    length=max(len(target),*(len(c) for c in columns));pad=lambda a:a+[zero]*(length-len(a))
    sol=solve_many(list(map(list,zip(*(pad(c) for c in columns)))),[[v] for v in pad(target)])
    if sol is None:return dict(found=False,label=candidate.get('label'),reason='no target polynomial of the declared degree satisfies the exact map identity')
    q=[r[0] for r in sol]
    if not q[-1]:return dict(found=False,label=candidate.get('label'),reason='target has smaller degree than declared')
    discriminant=resultant_discriminant(q)
    if not discriminant:return dict(found=False,label=candidate.get('label'),reason='target curve is generically singular')
    replay=[zero]
    for a,c in zip(q,columns):replay=F.add(replay,F.scale(c,a))
    if pad(replay)!=pad(target):raise AssertionError('quotient identity replay failed')
    rational=lambda a,b:dict(numerator=[v.packet() for v in a],denominator=[v.packet() for v in b])
    pullbacks=[]
    for i in range(target_genus):
        pullbacks.append(rational(F.product(F.product(F.power(n,i),du),t),F.product(F.power(d,i+2),s)))
    packet=dict(schema='pp-rational-curve-quotient/1',found=True,label=candidate.get('label'),
        source_genus=source_genus,target_genus=target_genus,map_degree=max(len(n),len(d))-1,
        u=rational(n,d),v_over_y=rational(s,t),target_coefficients=[v.packet() for v in q],
        target_discriminant=discriminant.packet(),identity_checked=True,holomorphic_pullbacks=pullbacks,
        identity='P(x) S(x)^2 D(x)^degree = T(x)^2 sum_j q_j N(x)^j D(x)^(degree-j)',
        domain='affine denominators D and T nonzero; extension over exceptional points requires the projective curve charts',
        execution_verified=False,scope='actual nonconstant rational map between the declared generically smooth hyperelliptic curves; candidate-list search is not a classification of all covers or Jacobian factors')
    if degree==4:
        # A rational branch point gives an explicit cubic chart. The default
        # reciprocal candidates have the fixed branch u=+/-2.
        for root in (-2,2,0,1,-1):
            if F.evaluate(q,one*root):continue
            shifted=F.shift(q,one*root);a=shifted[1]
            if not a:continue
            cubic=[a*a*shifted[4],a*shifted[3],shifted[2],one]
            packet['cubic_chart']=dict(branch_root=root,coefficients=[v.packet() for v in cubic],
                map='X=q_prime(root)/(u-root); Y=q_prime(root) v/(u-root)^2',
                exceptional_locus='u=root or q_prime(root)=0')
            if all(v.d==(1,) for v in cubic):
                family=CurveFamily(dict(coefficients=[list(map(str,v.n)) for v in cubic],**limits),_parameter_degree_limit=128)
                packet['elliptic_connection']=family.evidence();packet['elliptic_observable']=family.observable()
            break
    elif degree==3 and q[-1]==1 and all(v.d==(1,) for v in q):
        family=CurveFamily(dict(coefficients=[list(map(str,v.n)) for v in q],**limits),_parameter_degree_limit=128)
        packet['elliptic_connection']=family.evidence();packet['elliptic_observable']=family.observable()
    packet['algebra_work']=budget.work
    return packet


def discover_rational_quotients(specification,candidates=None):
    f,_,_=parse_source(specification);zero=f[0].coerce(0)
    if candidates is None:
        candidates=[]
        if len(f)==7:
            even=discover_elliptic_quotients(specification)
            if even['found']:
                h=RF.parse(even['center']);z=[-h,h.coerce(1)]
                candidates.append(dict(label='translated reflection',u_numerator=[a.packet() for a in F.power(z,2)],target_degree=3))
            if f==list(reversed(f)):
                for sign in (1,-1):
                    candidates.append(dict(label='reciprocal involution' if sign==1 else 'reciprocal involution with sheet sign',
                        u_numerator=[1,0,1],u_denominator=[0,1],v_numerator=[sign,1],v_denominator=[0,0,1],target_degree=4))
    if not isinstance(candidates,list) or len(candidates)>32:raise ValueError('at most 32 declared quotient candidates required')
    results=[verify_rational_quotient(specification,c) for c in candidates]
    return dict(schema='pp-rational-quotient-search/1',tested_candidates=len(results),quotients=[r for r in results if r['found']],
        rejected=[r for r in results if not r['found']],
        scope='automatic translated-reflection and reciprocal-involution templates, or the complete supplied finite candidate list; not all rational maps')
