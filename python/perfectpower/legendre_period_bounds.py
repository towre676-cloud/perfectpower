"""Exact rational enclosures of normalized real Legendre periods.

Classical Euler integral identity supplies the analytic interpretation. The
positive hypergeometric series and a proved elementary tail estimate supply
rational bounds. This mathematical derivation is documented, not Lean checked.
"""
from fractions import Fraction as Q
from .connection_polytope import exact


def rational_text(value):
    """Decimal output without changing Python's global integer-string limits."""
    value=Q(value)
    def digits(n):
        sign='-' if n<0 else '';n=abs(n)
        if n.bit_length()<12000:return sign+str(n)
        chunks=[]
        while n:
            n,r=divmod(n,10**9);chunks.append(r)
        return sign+str(chunks[-1])+''.join(f'{r:09d}' for r in reversed(chunks[:-1]))
    return digits(value.numerator) if value.denominator==1 else digits(value.numerator)+'/'+digits(value.denominator)


def rational_value(text):
    def number(s):
        sign=-1 if s.startswith('-') else 1;s=s.lstrip('-');n=0
        for i in range(0,len(s),9):n=n*10**len(s[i:i+9])+int(s[i:i+9])
        return sign*n
    pieces=text.split('/')
    return Q(number(pieces[0]),number(pieces[1]) if len(pieces)==2 else 1)


def normalized_period_interval(lam,terms=64):
    lam=exact(lam)
    if not 0<=lam<1 or type(terms) is not int or not 1<=terms<=10000:
        raise ValueError('rational parameter in [0,1) and terms 1..10000 required')
    a=Q(1);s=Q(0);p=Q(1)
    for n in range(terms):
        s+=a*p
        a*=Q((2*n+1)**2,4*(n+1)**2)
        p*=lam
    tail=a*p/(1-lam)
    return {'lambda':rational_text(lam),'terms':terms,'lower':rational_text(s),'upper':rational_text(s+tail),
            'tail_bound':rational_text(tail),'next_coefficient':rational_text(a),
            'normalization':'F(lambda)=2*K(lambda)/pi; real cycle period divided by 2*pi',
            'bound_method':'positive coefficients decreasing; tail <= a_N*lambda^N/(1-lambda)',
            'formalized':False,'scope':'exact rational interval under classical Euler period identity'}


def legendre_period_packet(lam,terms=64):
    lam=exact(lam)
    if not 0<lam<1:raise ValueError('smooth real Legendre parameter in (0,1) required')
    a=normalized_period_interval(lam,terms);b=normalized_period_interval(1-lam,terms)
    lo=rational_value(b['lower'])/rational_value(a['upper']);hi=rational_value(b['upper'])/rational_value(a['lower'])
    return {'schema':'pp-legendre-period-interval/1','lambda':rational_text(lam),
            'real_period_over_2pi':a,'imaginary_period_over_2pi_i':b,
            'tau_real':0,'tau_imaginary_interval':[rational_text(lo),rational_text(hi)],
            'curve':'y^2=x*(x-1)*(x-lambda)',
            'cycles':'real cycle over [0,lambda]; complementary imaginary cycle over [lambda,1], oriented for Im(tau)>0',
            'formalized':False,'analytic_identity':'classical Euler integral and branch substitution; no general curve period solver'}
