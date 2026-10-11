"""Exact quadratic surds, Euclidean continued fractions and certified exhaustion."""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import isqrt
from .euclid_geometry import rational
from .divisor_square import WorkLimit


@dataclass(frozen=True)
class QuadraticSurd:
    D:int
    a:Q=Q(0)
    b:Q=Q(1)
    def __post_init__(self):
        if type(self.D) is not int or self.D<2 or isqrt(self.D)**2==self.D:raise ValueError('positive nonsquare integer radicand required')
        if self.D.bit_length()>4096:raise WorkLimit('radicand bit limit exceeded')
        object.__setattr__(self,'a',rational(self.a));object.__setattr__(self,'b',rational(self.b))
    def _coerce(self,x):
        if not isinstance(x,QuadraticSurd):return QuadraticSurd(self.D,rational(x),Q(0))
        if x.D!=self.D:raise ValueError('different quadratic fields are not silently merged')
        return x
    def __add__(self,x):
        x=self._coerce(x);return QuadraticSurd(self.D,self.a+x.a,self.b+x.b)
    def __radd__(self,x):return self+x
    def __rsub__(self,x):return self._coerce(x)-self
    def __rmul__(self,x):return self*x
    def __rtruediv__(self,x):return self._coerce(x)/self
    def __neg__(self):return QuadraticSurd(self.D,-self.a,-self.b)
    def __sub__(self,x):return self+-self._coerce(x)
    def __mul__(self,x):
        x=self._coerce(x);return QuadraticSurd(self.D,self.a*x.a+self.D*self.b*x.b,self.a*x.b+self.b*x.a)
    def inverse(self):
        norm=self.a*self.a-self.D*self.b*self.b
        if norm==0:raise ZeroDivisionError('zero quadratic surd')
        return QuadraticSurd(self.D,self.a/norm,-self.b/norm)
    def __truediv__(self,x):return self*self._coerce(x).inverse()
    def sign(self):
        a,b=self.a,self.b
        if b==0:return (a>0)-(a<0)
        if a==0:return (b>0)-(b<0)
        if (a>0)==(b>0):return 1 if a>0 else -1
        delta=a*a-self.D*b*b
        return ((delta>0)-(delta<0))*(1 if a>0 else -1)
    def compare(self,x):return (self-self._coerce(x)).sign()
    def floor(self):
        s=isqrt(self.D);ends=[self.a+self.b*s,self.a+self.b*(s+1)]
        lo=min(ends).__floor__();hi=max(ends).__ceil__()+1
        while lo+1<hi:
            mid=(lo+hi)//2
            if self.compare(mid)>=0:lo=mid
            else:hi=mid
        return lo
    def receipt(self):return {'D':self.D,'a':str(self.a),'b':str(self.b),'sign':self.sign(),'floor':self.floor()}


def sqrt_continued_fraction(D,*,step_limit=4096):
    if type(step_limit) is not int or not 1<=step_limit<=65536:raise ValueError('continued-fraction step budget must be 1..65536')
    QuadraticSurd(D);a0=isqrt(D);m=0;den=1;a=a0;seen={};states=[]
    for _ in range(step_limit):
        m=den*a-m;num=D-m*m
        if num<=0 or num%den:raise AssertionError('invalid quadratic complete quotient')
        den=num//den;a=(a0+m)//den;state=(m,den,a)
        if state in seen:
            start=seen[state]
            if start!=0:raise AssertionError('unexpected preperiod for sqrt(D)')
            return {'schema':'pp-sqrt-cf/1','D':D,'a0':a0,'period':[s[2] for s in states],
                    'states':[list(s) for s in states],'repeat_state':list(state),'periodic_replay_checked':True}
        seen[state]=len(states);states.append(state)
    raise WorkLimit('quadratic continued fraction step budget exceeded')


def pell_from_cf(D,*,step_limit=4096):
    cf=sqrt_continued_fraction(D,step_limit=step_limit);period=cf['period'];p0,p1=0,1;q0,q1=1,0;rows=[]
    for k in range(2*len(period)+1):
        a=cf['a0'] if k==0 else period[(k-1)%len(period)]
        p=a*p1+p0;q=a*q1+q0;norm=p*p-D*q*q
        if max(p.bit_length(),q.bit_length())>65536:raise WorkLimit('Pell convergent bit limit exceeded')
        rows.append({'coefficient':a,'p':p,'q':q,'norm':norm})
        if norm==1 and q>0:
            return {'schema':'pp-cf-pell-unit/1','continued_fraction':cf,'convergents':rows,'unit':[p,q],
                    'norm_checked':True,'fundamentality_kernel_checked':False,
                    'scope':'first positive norm-one convergent; standard continued-fraction minimality is not kernel-certified by this receipt'}
        p0,p1=p1,p;q0,q1=q1,q
    raise AssertionError('norm-one unit missing in two periods')


def sqrt_exhaustion(value,epsilon,*,step_limit=4096):
    if type(step_limit) is not int or not 0<=step_limit<=65536:raise ValueError('exhaustion step budget must be 0..65536')
    value=rational(value);epsilon=rational(epsilon)
    if value<0 or epsilon<=0:raise ValueError('nonnegative radicand and positive tolerance required')
    lo=Q(0);hi=Q(max(1,value.__ceil__()));steps=[];initial=hi-lo
    for k in range(step_limit+1):
        if hi-lo<=epsilon:
            return {'schema':'pp-sqrt-exhaustion/1','radicand':str(value),'epsilon':str(epsilon),
                    'initial_width':str(initial),'lower':str(lo),'upper':str(hi),'steps':steps,
                    'halving_bound':str(initial/Q(2**len(steps))), 'exact_rational':lo==hi}
        if k==step_limit:break
        mid=(lo+hi)/2;comparison=(mid*mid>value)-(mid*mid<value)
        steps.append({'midpoint':str(mid),'square_comparison':comparison})
        if comparison>0:hi=mid
        elif comparison<0:lo=mid
        else:lo=hi=mid
    raise WorkLimit('exhaustion step budget exceeded; tolerance not attained')


def check_exhaustion(packet):
    result=sqrt_exhaustion(packet['radicand'],packet['epsilon'],step_limit=len(packet['steps']))
    if result!=packet:raise ValueError('exhaustion certificate does not replay')
    return True


def euclidean_gcd(a,b):
    if type(a) is not int or type(b) is not int:raise ValueError('integer Euclidean inputs required')
    x,y=abs(a),abs(b);u0,u1=1,0;v0,v1=0,1;rows=[]
    while y:
        q,r=divmod(x,y);rows.append([x,y,q,r]);x,y=y,r;u0,u1=u1,u0-q*u1;v0,v1=v1,v0-q*v1
    return {'schema':'pp-euclidean-gcd/1','a':a,'b':b,'gcd':x,'u':u0*(-1 if a<0 else 1),
            'v':v0*(-1 if b<0 else 1),'divisions':rows}


def check_gcd(packet):
    a,b,g,u,v=(packet[k] for k in ('a','b','gcd','u','v'))
    if any(type(x) is not int for x in (a,b,g,u,v)) or g<0:raise ValueError('invalid gcd certificate')
    if a*u+b*v!=g or (g==0 and (a!=0 or b!=0)) or (g>0 and (a%g or b%g)):raise ValueError('gcd Bezout/divisibility certificate failed')
    if packet!=euclidean_gcd(a,b):raise ValueError('Euclidean transcript failed')
    return True


def check_cf(packet):
    D=packet['D'];QuadraticSurd(D);a0=isqrt(D)
    if packet['a0']!=a0 or not packet['states']:raise ValueError('invalid initial continued fraction')
    m=0;den=1;a=a0
    for state in packet['states']+[packet['repeat_state']]:
        m=den*a-m;num=D-m*m
        if num<=0 or num%den:raise ValueError('invalid complete quotient')
        den=num//den;a=(a0+m)//den
        if state!=[m,den,a]:raise ValueError('continued-fraction recurrence failed')
        if QuadraticSurd(D,Q(m,den),Q(1,den)).floor()!=a:raise ValueError('quotient floor incorrect')
    if packet['repeat_state']!=packet['states'][0] or len({tuple(s) for s in packet['states']})!=len(packet['states']):raise ValueError('period witness invalid')
    if packet['period']!=[s[2] for s in packet['states']]:raise ValueError('period coefficients mismatch')
    return True


def isolate_root(coefficients,lower,upper,epsilon,*,step_limit=4096):
    """Sturm-counted exhaustion of exactly one distinct real polynomial root.

    Repeated roots are handled by squarefree reduction. Endpoints must not be roots.
    """
    from . import polyalg as P
    if type(step_limit) is not int or not 0<=step_limit<=65536:raise ValueError('root isolation step budget must be 0..65536')
    coefficients=list(coefficients)
    if not coefficients or any(type(x) is not int for x in coefficients):raise ValueError('integer polynomial required')
    while len(coefficients)>1 and coefficients[-1]==0:coefficients.pop()
    if len(coefficients)<2:raise ValueError('nonconstant polynomial required')
    if len(coefficients)>33:raise WorkLimit('root isolation degree limit exceeded')
    p=P.poly(coefficients);squarefree=P.exact_div(p,P.gcd_poly(p,P.derivative(p)))
    chain=[squarefree,P.derivative(squarefree)]
    while True:
        remainder=P.divmod_poly(chain[-2],chain[-1])[1]
        if P.is_zero(remainder):break
        chain.append(P.scale(remainder,-1))
    def evaluate(cs,x):
        v=Q(0)
        for c in reversed(cs):v=v*x+c
        return v
    def variation(x):
        signs=[(v>0)-(v<0) for cs in chain if (v:=evaluate(cs,x))!=0]
        return sum(a!=b for a,b in zip(signs,signs[1:]))
    lo,hi,eps=map(rational,(lower,upper,epsilon))
    if lo>=hi or eps<=0:raise ValueError('ordered interval and positive tolerance required')
    if evaluate(squarefree,lo)==0 or evaluate(squarefree,hi)==0:raise ValueError('root-free endpoints required')
    if variation(lo)-variation(hi)!=1:raise ValueError('interval must contain exactly one distinct real root')
    initial=hi-lo;steps=[]
    for k in range(step_limit+1):
        if hi-lo<=eps:
            return {'schema':'pp-sturm-exhaustion/1','coefficients':coefficients,'initial_interval':[str(rational(lower)),str(rational(upper))],
                    'epsilon':str(eps),'interval':[str(lo),str(hi)],'steps':steps,
                    'width_bound':str(initial/Q(2**len(steps))),'exact_rational_root':lo==hi,
                    'sturm_chain':[[str(x) for x in cs] for cs in chain]}
        if k==step_limit:break
        mid=(lo+hi)/2
        if evaluate(squarefree,mid)==0:
            steps.append({'midpoint':str(mid),'keep':'EXACT'});lo=hi=mid
        elif variation(lo)-variation(mid)==1:
            steps.append({'midpoint':str(mid),'keep':'LEFT'});hi=mid
        else:
            steps.append({'midpoint':str(mid),'keep':'RIGHT'});lo=mid
    raise WorkLimit('Sturm exhaustion budget exceeded')


def check_root_isolation(packet):
    result=isolate_root(packet['coefficients'],*packet['initial_interval'],packet['epsilon'],step_limit=len(packet['steps']))
    if result!=packet:raise ValueError('Sturm exhaustion certificate failed')
    return True
