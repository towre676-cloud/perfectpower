"""Complete integer cubic collision geometry via an exact positive quadratic."""
from math import isqrt
from . import polyalg as P
from .divisor_square import WorkLimit
from .observable_machine import _q


def cubic_collisions(coefficients,work_limit=100000):
    f=P.poly(tuple(map(_q,coefficients)))
    if P.degree(f)!=3 or any(c.denominator!=1 for c in f):raise ValueError('integer cubic required')
    if type(work_limit) is not int or work_limit<1:raise ValueError('positive collision budget required')
    _,c,b,a=map(int,f);radius=4*b*b-12*a*c
    bound=isqrt(radius//(3*a*a)) if radius>=0 else 0
    if bound>work_limit:raise WorkLimit('cubic collision ellipse exceeds work budget')
    pairs=[]
    for difference in range(1,bound+1):
        remainder=radius-3*a*a*difference*difference;u=isqrt(remainder)
        if u*u!=remainder:continue
        for root in sorted({u,-u}):
            numerator=root-2*b
            if numerator%(3*a):continue
            total=numerator//(3*a)
            if (total-difference)%2:continue
            x,y=(total-difference)//2,(total+difference)//2
            if P.evaluate(f,x)!=P.evaluate(f,y):raise AssertionError('collision equation replay')
            pairs.append((x,y))
    return dict(schema='pp-cubic-collisions/1',coefficients=list(map(int,f)),radius=radius,difference_bound=bound,
        pairs=sorted(pairs),complete=True,execution_verified=False,
        identity='(3*a*(x+y)+2*b)^2+3*a^2*(x-y)^2=4*b^2-12*a*c',
        scope='all off-diagonal integer pairs x<y for the supplied cubic, before domain restriction')
