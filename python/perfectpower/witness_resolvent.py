"""Exact formal witness resolvents, with polynomial identity certificates.

For supplied A, s, H the output series is H (I-z A)^-1 s. No spectral
diagonalization, guessed prefix, analytic convergence or OEIS claim is used.
Finite polynomial transients are retained when a denominator loses degree.
"""
from fractions import Fraction as Q
from . import exact_linear as E, polyalg as P
from .core import mul
from .observable_machine import _q, _matrix, _apply
from .divisor_square import WorkLimit


def _poly(xs):
    xs=tuple(xs)
    if not 1<=len(xs)<=129:raise ValueError('polynomial coefficient budget exceeded')
    return P.poly(map(_q,xs))


def _inputs(operator,seed,readouts):
    seed=tuple(map(_q,seed));n=len(seed);h=tuple(readouts)
    if not 1<=n<=64 or not 1<=len(h)<=64:raise ValueError('state/readout shape budget exceeded')
    return _matrix(operator,n,n),seed,_matrix(h,len(h),n)


def reduced_fraction(numerator,denominator):
    p,d=_poly(numerator),_poly(denominator)
    if not d[0]:raise ValueError('formal denominator must have nonzero constant')
    g=P.gcd_poly(p,d);p=P.exact_div(p,g);d=P.exact_div(d,g)
    c=1/d[0]
    return _poly(P.scale(p,c)),_poly(P.scale(d,c))


def witness_resolvent(operator,seed,readouts,*,work_limit=2000000):
    a,s,h=_inputs(operator,seed,readouts);n=len(s)
    if type(work_limit) is not int or work_limit<1:raise ValueError('positive work budget required')
    if n**4+len(h)*n*n>work_limit:raise WorkLimit('Krylov discovery shape estimate exceeds budget')
    orbit=[];v=s
    while any(v) and (not orbit or E.rank(orbit+[v])>len(orbit)):
        orbit.append(v);v=tuple(map(_q,_apply(a,v)))
    r=len(orbit);c=tuple(map(_q,E.solve(E.transpose(orbit),v))) if r else ()
    d=_poly((1,)+tuple(-x for x in reversed(c)))
    # Vector polynomial V satisfies (I-z A)V=D s, even for nilpotent A.
    vectors=tuple(tuple(_q(sum((d[j] if j<len(d) else 0)*orbit[i-j][t] for j in range(i+1)))
                        for t in range(n)) for i in range(r)) or (tuple(Q(0) for _ in s),)
    outputs=[]
    for row in h:
        raw=_poly(sum(x*y for x,y in zip(row,v)) for v in vectors)
        p,q=reduced_fraction(raw,d)
        outputs.append({'numerator':p,'denominator':q,
            'recurrence_order':0 if P.is_zero(p) else max(P.degree(q),P.degree(p)+1)})
    receipt={'schema':'pp-witness-resolvent/1','operator':a,'seed':s,'readouts':h,
        'reachable_dimension':r,'denominator':d,'vector_numerator':vectors,'outputs':outputs,
        'execution_verified':False,'field':'Q',
        'scope':'all nonnegative powers of the supplied exact matrix and readouts; formal series, not an external sequence definition'}
    if not verify_resolvent(receipt):raise AssertionError('polynomial resolvent replay failed')
    return receipt


def verify_resolvent(receipt):
    """Replay coefficient identities; no Krylov discovery or term fitting."""
    try:
        if receipt['schema']!='pp-witness-resolvent/1' or receipt['execution_verified'] is not False or receipt['field']!='Q':return False
        a,s,h=_inputs(receipt['operator'],receipt['seed'],receipt['readouts']);n=len(s)
        r=receipt['reachable_dimension'];d=_poly(receipt['denominator'])
        if type(r) is not int or not 0<=r<=n or d[0]!=1 or P.degree(d)>r:return False
        vectors=tuple(tuple(map(_q,v)) for v in receipt['vector_numerator'])
        if len(vectors)!=max(1,r) or any(len(v)!=n for v in vectors):return False
        if E.rank(vectors)!=r:return False
        zero=tuple(Q(0) for _ in s)
        for i in range(max(len(vectors)+1,len(d))):
            current=vectors[i] if i<len(vectors) else zero
            previous=_apply(a,vectors[i-1]) if 0<i<=len(vectors) else zero
            if tuple(_q(x-y) for x,y in zip(current,previous))!=tuple((d[i] if i<len(d) else 0)*x for x in s):return False
        if len(receipt['outputs'])!=len(h):return False
        for row,out in zip(h,receipt['outputs']):
            raw=_poly(sum(x*y for x,y in zip(row,v)) for v in vectors)
            p,q=_poly(out['numerator']),_poly(out['denominator'])
            if q[0]!=1 or P.degree(P.gcd_poly(p,q))!=0 or mul(raw,q)!=mul(p,d):return False
            expected=0 if P.is_zero(p) else max(P.degree(q),P.degree(p)+1)
            if type(out['recurrence_order']) is not int or out['recurrence_order']!=expected:return False
        # Reachable dimension is discovery metadata, not a minimality theorem.
        return True
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,OverflowError):return False


def resolvent_value(receipt,index,output=0,*,bit_limit=8192):
    if not verify_resolvent(receipt):raise ValueError('invalid witness resolvent certificate')
    if type(index) is not int or not 0<=index<2**64:raise ValueError('nonnegative 64-bit index required')
    if type(output) is not int or not 0<=output<len(receipt['outputs']):raise ValueError('invalid output index')
    if type(bit_limit) is not int or not 1<=bit_limit<=8192:raise ValueError('bit budget must be 1 through 8192')
    from .recurrence import from_generating_function
    out=receipt['outputs'][output];model=from_generating_function(_poly(out['numerator']),_poly(out['denominator']))
    # Binary polynomial powering, checking growth after every reduced product.
    mod=model.annihilator;value=P.ONE;base=P.divmod_poly(P.X,mod)[1]
    def checked(xs):
        if any(max(abs(x.numerator).bit_length(),x.denominator.bit_length())>bit_limit for x in xs):raise WorkLimit('resolvent coefficient growth exceeds budget')
        return xs
    for bit in bin(index)[2:]:
        value=checked(P.divmod_poly(mul(value,value),mod)[1])
        if bit=='1':value=checked(P.divmod_poly(mul(value,base),mod)[1])
    return checked((sum(x*model.initial[i] for i,x in enumerate(value)),))[0]


def compare_resolvents(left,right,*,left_output=0,right_output=0):
    if not verify_resolvent(left) or not verify_resolvent(right):raise ValueError('invalid witness certificates')
    if any(type(i) is not int or not 0<=i<len(r['outputs']) for i,r in ((left_output,left),(right_output,right))):raise ValueError('invalid output index')
    a,b=left['outputs'][left_output],right['outputs'][right_output]
    delta=P.add(mul(_poly(a['numerator']),_poly(b['denominator'])),P.scale(mul(_poly(b['numerator']),_poly(a['denominator'])),-1))
    delta=_poly(delta)
    if P.is_zero(delta):return {'status':'EQUAL_FOR_ALL_NONNEGATIVE_INDICES','cross_difference':delta,'execution_verified':False}
    # Both denominators have constant one, so the first nonzero numerator
    # coefficient is precisely the first nonzero formal-series coefficient.
    first=next(i for i,x in enumerate(delta) if x)
    return {'status':'DIFFERENT','first_index':first,'difference':delta[first],
        'cross_difference':delta,'execution_verified':False}


def subsequence_resolvent(operator,seed,readouts,*,offset=0,step=1,work_limit=2000000):
    """Compile H A^(offset+step*n) seed, including singular A and step zero."""
    a,s,h=_inputs(operator,seed,readouts);n=len(s)
    if any(type(x) is not int or not 0<=x<2**64 for x in (offset,step)):raise ValueError('nonnegative 64-bit offset/step required')
    if type(work_limit) is not int or work_limit<1:raise ValueError('positive work budget required')
    if 2*n**3*(offset.bit_length()+step.bit_length())+n**4+len(h)*n*n>work_limit:raise WorkLimit('subsequence power estimate exceeds budget')
    def power(k):
        value=E.identity(n)
        for bit in bin(k)[2:]:
            value=_matrix(E.multiply(value,value),n,n)
            if bit=='1':value=_matrix(E.multiply(value,a),n,n)
        return value
    return witness_resolvent(power(step),_apply(power(offset),s),h,work_limit=work_limit)
