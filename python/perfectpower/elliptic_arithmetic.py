"""Exact rational Weierstrass arithmetic, model maps and division fibres."""
from fractions import Fraction as Q
from functools import lru_cache
from math import gcd, lcm, isqrt
from . import polyalg as P
from .divisor_square import WorkLimit


def integer_literal(s):
    if not isinstance(s,str) or not s: raise ValueError('integer literal required')
    sign=-1 if s[0]=='-' else 1
    if s[0] in '+-': s=s[1:]
    if not s.isascii() or not s.isdigit() or len(s)>20000: raise ValueError('bounded decimal integer required')
    n=0
    for i in range(0,len(s),9): n=n*10**len(s[i:i+9])+int(s[i:i+9])
    return sign*n


def q(v, bits=65536):
    if type(v) is int: a=Q(v)
    elif isinstance(v,Q): a=v
    elif isinstance(v,str):
        parts=v.split('/')
        if len(parts)>2: raise ValueError('rational literal required')
        a=Q(integer_literal(parts[0]),integer_literal(parts[1]) if len(parts)==2 else 1)
    else: raise ValueError('exact integer, rational or rational literal required')
    if max(abs(a.numerator).bit_length(),a.denominator.bit_length())>bits: raise WorkLimit('rational bit budget')
    return a


def decimal(n):
    if n==0:return '0'
    sign='-' if n<0 else ''; n=abs(n); a=[]
    while n:n,r=divmod(n,10**9);a.append(r)
    return sign+str(a[-1])+''.join(f'{v:09d}' for v in reversed(a[:-1]))


def rational_literal(a):
    a=q(a);return decimal(a.numerator)+(('/'+decimal(a.denominator)) if a.denominator!=1 else '')


def point(p):
    if p is None:return None
    if not isinstance(p,(list,tuple)) or len(p)!=2:raise ValueError('point is [x,y] or infinity null')
    return tuple(q(v,12000) for v in p)


def encode_point(p):return None if p is None else [rational_literal(v) for v in p]


def sqrtq(a):
    if a<0:return None
    n,d=isqrt(a.numerator),isqrt(a.denominator)
    return Q(n,d) if n*n==a.numerator and d*d==a.denominator else None


def primes(bound):
    if type(bound) is not int or not 2<=bound<=20000:raise ValueError('prime bound 2 through 20000')
    return [p for p in range(2,bound+1) if all(p%d for d in range(2,isqrt(p)+1))]


def rational_roots(f,node_limit=100000):
    """Complete rational roots: monic integral transform and integer Sturm tree."""
    root_budget(node_limit)
    f=P.monic(P.poly(f));n=P.degree(f)
    if n<1:return []
    D=lcm(*(c.denominator for c in f));g=P.poly(c*D**(n-i) for i,c in enumerate(f))
    sf=P.exact_div(g,P.gcd_poly(g,P.derivative(g)));chain=P.sturm_chain(sf)
    # Integer Fujiwara bound, substantially tighter than the Cauchy bound.
    def ceiling_root(m,k):
        lo=0;hi=1<<((m.bit_length()+k-1)//k)
        while lo<hi:
            mid=(lo+hi)//2
            if mid**k>=m:hi=mid
            else:lo=mid+1
        return lo
    b=2*max([ceiling_root(abs(int(c)),n-i) for i,c in enumerate(g[:-1])]+[1])
    stack=[(-b-1,b)];out=[];used=0
    while stack:
        a,b=stack.pop();used+=1
        if used>node_limit:raise WorkLimit('complete rational-root Sturm budget exhausted')
        va,vb=P._sign_changes(chain,a),P._sign_changes(chain,b)
        if va==vb:continue
        if b-a==1:
            if P.evaluate(g,b)==0:out.append(Q(b,D))
        else:
            mid=(a+b)//2;stack.extend([(mid,b),(a,mid)])
    return sorted(out)


def root_budget(node_limit):
    if type(node_limit) is not int or not 1 <= node_limit <= 100000:
        raise ValueError('root node budget 1 through 100000 required')


def rational_root_certificate(f, node_limit=100000):
    """Reduce rational roots to an integer Sturm certificate, with no divisor scan.

    If f is monic and D clears its coefficients, a rational root r gives
    the algebraic integer D*r. Being rational, D*r is an integer.
    """
    from .sturm_fibres import root_certificate
    root_budget(node_limit)
    f=P.poly(q(c) for c in f)
    if P.is_zero(f):raise ValueError('zero polynomial has infinitely many roots')
    f=P.monic(f);n=P.degree(f);D=lcm(*(c.denominator for c in f))
    g=[int(c*D**(n-i)) for i,c in enumerate(f)]
    if max(abs(c).bit_length() for c in g)>12000:
        raise WorkLimit('rational-root certificate coefficient budget')
    certificate=root_certificate(g,node_limit=node_limit)
    # Bound the emitted signed-remainder data too: intermediate Sturm
    # coefficients can be larger than the original polynomial coefficients.
    from .elliptic_certificate_verifier import CheckBudget
    try:CheckBudget(2000000).packet(certificate)
    except ValueError as error:raise WorkLimit('rational-root packet exceeds replay allocation budget') from error
    return dict(schema='pp-rational-roots/1',coefficients=[rational_literal(c) for c in f],
                denominator_scale=rational_literal(Q(D)),integer_certificate=certificate,
                roots=[rational_literal(Q(r,D)) for r in certificate['roots']])


def reconstruct(a,m):
    bound=isqrt(m//2);r0,r1=m,a;t0,t1=0,1
    while abs(r1)>bound:
        if not r1:return None
        k=r0//r1;r0,r1=r1,r0-k*r1;t0,t1=t1,t0-k*t1
    if not t1 or abs(t1)>bound or gcd(r1,t1)!=1:return None
    return Q(r1,t1) if (r1-a*t1)%m==0 else None


def discovered_roots(f):
    """Bounded p-adic discovery; every returned candidate is checked exactly."""
    f=P.poly(f);D=lcm(*(c.denominator for c in f));g=tuple(int(c*D) for c in f);dg=P.derivative(g)
    target=min(65536,4*max(abs(c).bit_length() for c in g)+128)
    for p in (3,5,7,11,13,17,19):
        if g[-1]%p==0:continue
        roots=[r for r in range(p) if P.evaluate(g,r)%p==0 and P.evaluate(dg,r)%p]
        for r in roots:
            m=p
            while m.bit_length()<=target:
                mm=m*m;r=(r-int(P.evaluate(g,r))*pow(int(P.evaluate(dg,r)),-1,mm))%mm;m=mm
                if m.bit_length()<24:continue
                a=reconstruct(r,m)
                if a is not None and P.evaluate(f,a)==0:yield a;break


class EllipticCurve:
    def __init__(self,specification):
        if isinstance(specification,dict) and set(specification)!={'ainvs'}:raise ValueError('only ainvs is supported')
        raw=specification.get('ainvs') if isinstance(specification,dict) else specification
        if not isinstance(raw,(list,tuple)):raise ValueError('Weierstrass coefficient list required')
        if len(raw)==2:raw=[0,0,0,*raw]
        if len(raw)!=5:raise ValueError('five Weierstrass a-invariants required')
        self.a=tuple(q(v,8192) for v in raw);a1,a2,a3,a4,a6=self.a
        self.b2=a1*a1+4*a2;self.b4=2*a4+a1*a3;self.b6=a3*a3+4*a6
        self.b8=a1*a1*a6+4*a2*a6-a1*a3*a4+a2*a3*a3-a4*a4
        self.c4=self.b2**2-24*self.b4;self.c6=-self.b2**3+36*self.b2*self.b4-216*self.b6
        self.discriminant=-self.b2**2*self.b8-8*self.b4**3-27*self.b6**2+9*self.b2*self.b4*self.b6
        if not self.discriminant:raise ValueError('singular Weierstrass equation')
        self.cubic=(self.b6/4,self.b4/2,self.b2/4,Q(1));self.specification={'ainvs':[rational_literal(v) for v in self.a]}

    def contains(self,p):
        p=point(p)
        if p is None:return True
        x,y=p;a1,a2,a3,a4,a6=self.a
        return y*y+a1*x*y+a3*y==x**3+a2*x*x+a4*x+a6

    def checked(self,p):
        p=point(p)
        if not self.contains(p):raise ValueError('point is not on the curve')
        return p

    def neg(self,p):
        p=self.checked(p)
        return None if p is None else (p[0],-p[1]-self.a[0]*p[0]-self.a[2])

    def add(self,left,right):
        a=self.checked(left);b=self.checked(right)
        if a is None:return b
        if b is None:return a
        x,y=a;u,v=b;a1,a2,a3,a4,a6=self.a
        if x==u:
            if y+v+a1*x+a3==0:return None
            slope=(3*x*x+2*a2*x+a4-a1*y)/(2*y+a1*x+a3)
        else:slope=(v-y)/(u-x)
        xx=slope*slope+a1*slope-a2-x-u
        yy=-(slope+a1)*xx-(y-slope*x)-a3
        return self.checked((xx,yy))

    def mul(self,p,n):
        if type(n) is not int or abs(n).bit_length()>8192:raise ValueError('bounded integer scalar required')
        p=self.checked(p)
        if n<0:p=self.neg(p);n=-n
        out=None
        while n:
            if n&1:out=self.add(out,p)
            n>>=1
            if n:p=self.add(p,p)
        return out

    def complete(self,p):
        p=self.checked(p)
        return None if p is None else (p[0],p[1]+(self.a[0]*p[0]+self.a[2])/2)

    def uncomplete(self,p):return None if p is None else self.checked((p[0],p[1]-(self.a[0]*p[0]+self.a[2])/2))

    def integral_cubic(self):
        s=lcm(*(c.denominator for c in self.a))
        return s,tuple(map(int,[16*s**6*self.b6,8*s**4*self.b4,s*s*self.b2,1]))

    def integral_point(self,p):
        p=self.complete(p);s,_=self.integral_cubic()
        return None if p is None else (4*s*s*p[0],8*s**3*p[1])

    @lru_cache(maxsize=256)
    def two_torsion(self):
        s,f=self.integral_cubic();return tuple(self.uncomplete((r/(4*s*s),Q(0))) for r in rational_roots(f))

    def halves(self,p,node_limit=100000):
        root_budget(node_limit)
        p=self.checked(p)
        if p is None:return [None,*self.two_torsion()]
        x0,_=self.complete(p);C,B,A,_=self.cubic
        f=(B*B-4*A*C-4*x0*C,-8*C-4*x0*B,-2*B-4*x0*A,-4*x0,Q(1))
        def test(xs):
            for x in xs:
                y=sqrtq(P.evaluate(self.cubic,x))
                if y is None:continue
                for yy in {y,-y}:
                    r=self.uncomplete((x,yy))
                    if self.mul(r,2)==p:return r
        r=test(discovered_roots(f))
        if r is None:r=test(rational_roots(f,node_limit))
        if r is None:return []
        out=[self.add(r,t) for t in (None,*self.two_torsion())]
        assert all(self.mul(h,2)==p for h in out)
        return sorted(out,key=lambda v:encode_point(v) or [])

    def summary(self):return dict(schema='pp-elliptic-curve/1',**self.specification,discriminant=rational_literal(self.discriminant),c4=rational_literal(self.c4),c6=rational_literal(self.c6),j=rational_literal(self.c4**3/self.discriminant))
    def evidence(self):return dict(self.summary(),equation='y^2+a1*x*y+a3*y=x^3+a2*x^2+a4*x+a6',cubic=[rational_literal(v) for v in self.cubic],coordinate_identity_checked=True)
    def point_add(self,left,right):return encode_point(self.add(left,right))
    def point_multiply(self,p,scalar):return encode_point(self.mul(p,scalar))
    def division_polynomial(self,p):
        p=self.checked(p)
        if p is None:raise ValueError('affine target required')
        x0,_=self.complete(p);C,B,A,_=self.cubic
        return P.poly((B*B-4*A*C-4*x0*C,-8*C-4*x0*B,-2*B-4*x0*A,-4*x0,Q(1)))

    def rational_halves(self,p,node_limit=100000):
        """Complete Q-rational [2] fibre with independently replayable evidence."""
        root_budget(node_limit);p=self.checked(p)
        torsion=rational_root_certificate(self.cubic,node_limit)
        used=torsion['integer_certificate']['nodes_checked']
        two=[self.uncomplete((q(r),Q(0))) for r in torsion['roots']]
        anchor=None;division=None
        if p is None:
            out=[None,*two];method='two_torsion'
        else:
            f=self.division_polynomial(p)
            def lift(xs):
                for x in xs:
                    y=sqrtq(P.evaluate(self.cubic,x))
                    if y is not None:
                        for yy in sorted({y,-y}):
                            h=self.uncomplete((x,yy))
                            if self.mul(h,2)==p:return h
                return None
            anchor=lift(discovered_roots(f))
            if anchor is None:
                if used>=node_limit:raise WorkLimit('shared halving root budget exhausted')
                division=rational_root_certificate(f,node_limit-used)
                used+=division['integer_certificate']['nodes_checked']
                anchor=lift(q(r) for r in division['roots'])
            out=[] if anchor is None else [self.add(anchor,t) for t in (None,*two)]
            method='empty_division_fibre' if anchor is None else 'torsion_coset'
        out=sorted(out,key=lambda v:encode_point(v) or [])
        return dict(schema='pp-rational-halves/1',curve=self.specification,target=encode_point(p),
                    points=[encode_point(h) for h in out],complete=True,execution_verified=False,
                    method=method,anchor=encode_point(anchor),two_torsion_certificate=torsion,
                    division_certificate=division,node_limit=node_limit,root_nodes=used)

    def rational_thirds(self,p,node_limit=100000):
        from .elliptic_division import rational_thirds
        return rational_thirds(self,p,node_limit)

    def rational_division(self,p,scalar,node_limit=100000,branch_limit=64):
        from .elliptic_division import rational_division
        return rational_division(self,p,scalar,node_limit,branch_limit)

    def model_transport(self,p,target):
        other=EllipticCurve(target);mapping=self.isomorphism(other)
        if mapping is None:raise ValueError('unsupported rational model isomorphism')
        return dict(map=mapping,point=encode_point(self.transport(p,other)))

    def two_isogeny(self,kernel,p=None):
        return dict(map=self.isogeny(kernel),point=encode_point(self.isogeny_point(p,kernel)))

    def independence(self,points,prime_bound=500,halving_limit=32,node_limit=100000):
        from .elliptic_certificates import certify_independence
        return certify_independence(self,points,prime_bound,halving_limit,node_limit)

    def isogeny(self,kernel):
        t=self.checked(kernel)
        if t is None or self.mul(t,2) is not None:raise ValueError('nonidentity rational two-torsion kernel required')
        r=t[0];C,B0,A0,_=self.cubic;A=3*r+A0;B=3*r*r+2*A0*r+B0
        target=EllipticCurve([0,-2*A,0,A*A-4*B,0]);Nu=(B,A,1);z=P.X;z2=P.power(z,2)
        lhs=P.mul((0,B,A,1),P.power(P.add(z2,(-B,)),2))
        rhs=P.add(P.mul(P.power(Nu,3),z),P.add(P.scale(P.mul(P.power(Nu,2),z2),-2*A),P.scale(P.mul(Nu,P.power(z,3)),A*A-4*B)))
        assert P.poly(lhs)==P.poly(rhs)
        return dict(schema='pp-rational-two-isogeny/1',source=self.specification,target=target.specification,kernel=encode_point(t),shift=rational_literal(r),A=rational_literal(A),B=rational_literal(B),degree=2,identity_checked=True,map='z=x-r; u=z+A+B/z; v=Y*(1-B/z^2)',differential_pullback='du/v=dx/Y')

    def isogeny_point(self,p,kernel):
        edge=self.isogeny(kernel);p=self.complete(p)
        if p is None or p[0]==q(edge['shift']):return None
        z=p[0]-q(edge['shift']);A=q(edge['A']);B=q(edge['B']);out=(z+A+B/z,p[1]*(1-B/z**2))
        return EllipticCurve(edge['target']).checked(out)

    def isomorphism(self,target):
        target=target if isinstance(target,EllipticCurve) else EllipticCurve(target)
        p=-self.c4/48;r=-self.c6/864;pp=-target.c4/48;rr=-target.c6/864
        if bool(p)!=bool(pp) or bool(r)!=bool(rr):return None
        ratio=pp/p if p else rr/r;n=4 if p else 6
        if ratio<=0:return None
        def root(a,k):
            lo=0;hi=1<<((a.bit_length()+k-1)//k)
            while lo<hi:
                mid=(lo+hi)//2
                if mid**k<a:lo=mid+1
                else:hi=mid
            return lo if lo**k==a else None
        a,b=root(ratio.numerator,n),root(ratio.denominator,n)
        if a is None or b is None:return None
        u=Q(a,b)
        if pp!=u**4*p or rr!=u**6*r:return None
        return dict(source=self.specification,target=target.specification,scale=rational_literal(u),identity_checked=True,differential_scale=rational_literal(1/u))

    def transport(self,p,target):
        target=target if isinstance(target,EllipticCurve) else EllipticCurve(target);m=self.isomorphism(target)
        if m is None:raise ValueError('models are not rationally isomorphic by the supported scaling')
        p=self.complete(p)
        if p is None:return None
        u=q(m['scale']);x=u*u*(p[0]+self.b2/12)-target.b2/12
        return target.uncomplete((x,u**3*p[1]))

    def scan(self,numerators=10,denominators=3):
        if type(numerators) is not int or type(denominators) is not int or not 0<=numerators<=10000 or not 1<=denominators<=100:raise ValueError('bounded rational-x search required')
        out=set()
        for d in range(1,denominators+1):
            for n in range(-numerators,numerators+1):
                x=Q(n,d);y=sqrtq(P.evaluate(self.cubic,x))
                if y is not None:out.update(self.uncomplete((x,yy)) for yy in {y,-y})
        return dict(points=[encode_point(p) for p in sorted(out)],complete_within_search=True,numerators=numerators,denominators=denominators)
