"""Exact experimental kernels. Finite searches never imply global completeness."""
from fractions import Fraction
from math import isqrt, gcd
import json

def cube_floor(n):
    if n < 0:
        r=cube_floor(-n)
        return -r if r**3 == -n else -r-1
    lo,hi=0,1
    while hi**3<=n: hi*=2
    while hi-lo>1:
        m=(lo+hi)//2
        if m**3<=n: lo=m
        else: hi=m
    return lo

def mordell(k, upper, moduli=(16,27,5,7,13)):
    if k==0: raise ValueError('singular curve')
    lower=cube_floor(-k)
    if lower**3+k<0: lower+=1
    filters=[(q,{r for r in range(q) if (r**3+k)%q in {y*y%q for y in range(q)}}) for q in moduli]
    points=[]; survivors=0
    for x in range(lower,upper+1):
        if any(x%q not in rs for q,rs in filters): continue
        survivors+=1; v=x**3+k; y=isqrt(v)
        if y*y==v:
            points.append([x,y])
            if y: points.append([x,-y])
    return {'k':k,'x_interval':[lower,upper],'points':sorted(points),'survivors':survivors,'status':'bounded_search','missing_premise':'proved global upper x bound','filters':[{'modulus':q,'accepted':sorted(rs)} for q,rs in filters]}

def reduced_forms(delta):
    """Primitive positive definite reduced forms, negative order discriminant."""
    if delta>=0 or delta%4 not in (0,1): raise ValueError('negative discriminant required')
    out=[]
    for a in range(1,isqrt((-delta)//3)+1):
        for b in range(-a,a+1):
            if (b*b-delta)%(4*a): continue
            c=(b*b-delta)//(4*a)
            if a>c or gcd(gcd(a,abs(b)),c)!=1: continue
            if (abs(b)==a or a==c) and b<0: continue
            out.append([a,b,c])
    return out

def unit_cubes(order):
    return {'order':order,'cube_image':sorted({3*j%order for j in range(order)}),'quotient_size':gcd(order,3),'all_cubes':gcd(order,3)==1}

def orbit(n):
    a,b=1,0
    for _ in range(n): a,b=a+2*b,a+b
    return a,b

def convergents(n):
    p0,p1,q0,q1=0,1,1,0; out=[]
    for j in range(n):
        c=1 if j==0 else 2
        p0,p1=p1,c*p1+p0; q0,q1=q1,c*q1+q0
        out.append((p1,q1))
    return out

def recurrence_terms(a0,a1,c,d,n):
    if n==0:return []
    out=[a0]
    if n>1:out.append(a1)
    while len(out)<n:out.append(c*out[-1]+d*out[-2])
    return out

def gf_coeffs(numerator,denominator,n):
    """Formal coefficient division over Q; denominator constant nonzero."""
    if not denominator or denominator[0]==0:raise ValueError('nonunit constant')
    out=[]
    for i in range(n):
        rhs=Fraction(numerator[i] if i<len(numerator) else 0)
        rhs-=sum(Fraction(denominator[j])*out[i-j] for j in range(1,min(i+1,len(denominator))))
        out.append(rhs/Fraction(denominator[0]))
    return out

def triple(m,n):
    if not m>n>0:raise ValueError('m > n > 0 required')
    return m*m-n*n,2*m*n,m*m+n*n

def quartic_point(a,b,x,y):
    """v²=a u⁴+b u² -> Y²=X³+b X², X=a u²,Y=a u v."""
    if a==0 or y*y!=a*x**4+b*x*x:raise ValueError('not a point')
    X,Y=a*x*x,a*x*y
    assert Y*Y==X**3+b*X**2
    return X,Y

def even_quartic_point(a,b,c,u,v):
    """v²=a u⁴+b u²+c -> Y²=X³+bX²+acX, degree-two map."""
    if a==0 or v*v!=a*u**4+b*u*u+c:raise ValueError('not a point')
    X,Y=a*u*u,a*u*v
    assert Y*Y==X**3+b*X**2+a*c*X
    return X,Y

def even_quartic_lifts(a,b,c,X,Y):
    if a==0:raise ValueError('a nonzero')
    if Y*Y!=X**3+b*X**2+a*c*X:raise ValueError('not a cubic point')
    if X==0:
        if c<0:return []
        v=isqrt(c)
        return sorted({(0,v),(0,-v)}) if v*v==c else []
    if X%a or X//a<0:return []
    u=isqrt(X//a)
    if u*u!=X//a:return []
    out=[]
    for z in (u,-u):
        if Y%(a*z)==0:
            v=Y//(a*z)
            if v*v==a*z**4+b*z*z+c:out.append((z,v))
    return sorted(set(out))

def lattice_count(period,residues,lo,hi):
    if period<=0:raise ValueError('positive period')
    if hi<lo:return 0
    return sum((hi-r)//period-(lo-1-r)//period for r in set(x%period for x in residues))

def monomial_pairs(a,b,N):
    """Positive solutions x^a=y^b, x,y <= N, exact integer algorithm."""
    if min(a,b)<1 or N<0:raise ValueError('positive exponents')
    g=gcd(a,b); aa,bb=a//g,b//g; out=[]; t=1
    while max(t**aa,t**bb)<=N:
        out.append((t**bb,t**aa));t+=1
    return out

def write_receipts(path,upper=100000):
    from pathlib import Path
    p=Path(path);p.mkdir(parents=True,exist_ok=True)
    rows=[mordell(k,upper) for k in range(-100,101) if k]
    (p/'mordell_scan.json').write_text(json.dumps({'scope':'all 200 nonsingular signed curves; not the unavailable 155-curve ledger','curves':rows},indent=2))
    classes=[{'D':D,'order_discriminant':-4*D,'forms':reduced_forms(-4*D),'class_number':len(reduced_forms(-4*D))} for D in range(1,101)]
    (p/'class_numbers.json').write_text(json.dumps(classes,indent=2))
    obs={'convergents_checked':100,'unit_groups':[unit_cubes(n) for n in (2,4,6)],'identities_checked':200}
    assert convergents(100)==[orbit(j+1) for j in range(100)]
    for j in range(200):
        a,b=orbit(j);c,d=orbit(2*j)
        assert a*a-2*b*b==(-1)**j and d==2*a*b and c==a*a+2*b*b
    (p/'orbit_checks.json').write_text(json.dumps(obs,indent=2))
    return rows
