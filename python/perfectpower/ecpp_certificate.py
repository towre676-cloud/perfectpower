"""Exact Atkin-Morain certificate arithmetic, independent of the generator.

Affine additions reject nonunit denominators; the nonzero cofactor multiple
has projective Z=1 and stays nonzero at every prime divisor of the modulus.
Terminal primes are proved by exhaustive trial division, not probable-prime
rounds. The strict integer Hasse bound deliberately strengthens PARI's bound.
"""
from math import gcd, isqrt
from .core import floor_nth_root

BRAINPOOL384_PRIME = int('8cb91e82a3386d280f5d6f7e50e641df152f7109ed5456b412b1da197fb71123acd3a729901d1a71874700133107ec53',16)


def affine_add(left, right, a, n):
    if left is None: return right
    if right is None: return left
    x,y = left; u,v = right
    if x==u:
        if (y+v)%n==0: return None
        if y!=v: raise ValueError('mixed same-abscissa addition')
        numerator,denominator = 3*x*x+a, 2*y
    else:
        numerator,denominator = v-y,u-x
    if gcd(denominator,n)!=1: raise ValueError('nonunit elliptic denominator')
    slope = numerator*pow(denominator,-1,n)%n
    xx = (slope*slope-x-u)%n
    return xx,(slope*(x-xx)-y)%n


def affine_multiply(point, scalar, a, n):
    if type(scalar) is not int or scalar<0 or scalar.bit_length()>8192:
        raise ValueError('bounded nonnegative literal scalar required')
    out = None
    while scalar:
        if scalar&1: out=affine_add(out,point,a,n)
        scalar//=2
        if scalar: point=affine_add(point,point,a,n)
    return out


def terminal_prime(n):
    if type(n) is not int or not 2<=n<=10**14: return False
    if n in (2,3): return True
    if n%2==0 or n%3==0: return False
    limit=isqrt(n);d=5
    while d<=limit:
        if n%d==0 or (d+2<=limit and n%(d+2)==0): return False
        d+=6
    return True


def ecpp_chain_details(certificate, target=None):
    if type(certificate) is not list or not 1<=len(certificate)<=256:
        raise ValueError('bounded nonempty ECPP chain required')
    expected=target; details=[]
    for row in certificate:
        if type(row) is not list or len(row)!=5:
            raise ValueError('five-component ECPP row required')
        n,t,s,a,point=row
        if any(type(x) is not int or abs(x).bit_length()>4096 for x in (n,t,s,a)):
            raise ValueError('bounded literal integer certificate required')
        if n<5 or n%2==0 or (expected is not None and n!=expected):
            raise ValueError('modulus or chain-link mismatch')
        if type(point) is not list or len(point)!=2 or any(type(x) is not int or not 0<=x<n for x in point):
            raise ValueError('canonical affine point required')
        m=n+1-t
        if t*t>=4*n or s<=0 or m<=0 or m%s:
            raise ValueError('trace or cofactor mismatch')
        q=m//s
        root=floor_nth_root(n,4); ceiling=root+int(root**4<n)
        if not (ceiling+1)**2<q<n:
            raise ValueError('large-prime Hasse bound failed')
        x,y=point; b=(y*y-x*x*x-a*x)%n
        if gcd(4*a**3+27*b*b,n)!=1:
            raise ValueError('singular reduction at a divisor')
        cofactor_point=affine_multiply(tuple(point),s,a,n)
        if cofactor_point is None or affine_multiply(cofactor_point,q,a,n) is not None:
            raise ValueError('elliptic point-order conditions failed')
        details.append(dict(modulus_bits=n.bit_length(),prime_factor_bits=q.bit_length(),
                            trace=t,cofactor=s,large_prime=q,curve_b=b,
                            cofactor_point=list(cofactor_point)))
        expected=q
    if not terminal_prime(expected): raise ValueError('terminal trial-division proof failed')
    return dict(stages=len(details),terminal_prime=expected,terminal_trial_bound=isqrt(expected),
                target=certificate[0][0],rows=details)


def verify_ecpp(certificate, target=None):
    try: ecpp_chain_details(certificate,target);return True
    except (ValueError,TypeError,IndexError,ArithmeticError):return False
