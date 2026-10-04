"""Complete quartic enumeration with a Lean-proved coefficient bound."""
from math import isqrt
from .divisor_square import WorkLimit


def match(coefficients):
    f=list(coefficients)
    while len(f)>1 and f[-1]==0:f.pop()
    if len(f)!=5 or any(type(z) is not int for z in f) or f[4]<=0:return None
    L=isqrt(f[4])
    if L*L!=f[4] or f[3]%(2*L):return None
    a=f[3]//(2*L)
    if (f[2]-a*a)%(2*L):return None
    b=(f[2]-a*a)//(2*L)
    c,d=f[1]-2*a*b,f[0]-b*b
    if not c and not d:return None
    return L,a,b,c,d


def solve(L,a,b,c,d,*,work_limit=100_000):
    if any(type(z) is not int for z in (L,a,b,c,d)) or L==0 or (c,d)==(0,0):
        raise ValueError('nonzero quadratic leading coefficient and nonzero perturbation required')
    if type(work_limit) is not int or work_limit<1:raise ValueError('positive work limit required')
    B=abs(a)+abs(b)+abs(c)+abs(d)+1
    if 2*B+1>work_limit:raise WorkLimit('complete interval exceeds work limit; no partial list returned')
    points=[]
    for x in range(-B,B+1):
        n=(L*x*x+a*x+b)**2+c*x+d
        if n<0:continue
        y=isqrt(n)
        if y*y==n:
            points.extend((x,z) for z in sorted({y,-y}))
    return {'points':points,'parameters':[L,a,b,c,d],'coordinate_bound':B,
            'fibres_examined':2*B+1,'complete':True,'execution_verified':False,
            'theorem':'PerfectPower.LinearPerturbation.complete'}


def emit_lean(L,a,b,c,d,name='quartic_points'):
    solve(L,a,b,c,d)
    if not name.isidentifier() or not name.isascii():raise ValueError('simple ASCII identifier required')
    return ('import PerfectPower.Tactic.LinearPerturbation\n'
            f'native_linear_perturbation {name} for {L}, {a}, {b}, {c}, {d}\n'
            f'#print axioms {name}_complete\n')


def match_square_leading(coefficients):
    f=list(coefficients)
    while len(f)>1 and f[-1]==0:f.pop()
    if len(f)!=5 or any(type(z) is not int for z in f) or f[4]<=0:return None
    L=isqrt(f[4])
    if L*L!=f[4]:return None
    z,w,v,u=f[:4]
    S=8*L**3;a=4*L*L*u;b=4*L*L*v-u*u
    c,d=S*S*w-2*a*b,S*S*z-b*b
    return (L,u,v,w,z) if c or d else None


def solve_square_leading(L,u,v,w,z,*,work_limit=100_000):
    if any(type(t) is not int for t in (L,u,v,w,z)) or not L:
        raise ValueError('integer coefficients and nonzero leading square root required')
    if type(work_limit) is not int or work_limit<1:raise ValueError('positive work limit required')
    S=8*L**3;a=4*L*L*u;b=4*L*L*v-u*u
    c,d=S*S*w-2*a*b,S*S*z-b*b
    if not c and not d:raise ValueError('zero normalized perturbation is excluded')
    B=abs(a)+abs(b)+abs(c)+abs(d)+1
    if 2*B+1>work_limit:raise WorkLimit('complete normalized interval exceeds work limit')
    points=[]
    for x in range(-B,B+1):
        n=L*L*x**4+u*x**3+v*x*x+w*x+z
        if n>=0 and isqrt(n)**2==n:
            y=isqrt(n);points.extend((x,t) for t in sorted({y,-y}))
    return {'points':points,'parameters':[L,u,v,w,z],'coordinate_bound':B,
            'fibres_examined':2*B+1,'complete':True,'execution_verified':False,
            'theorem':'PerfectPower.SquareLeadingQuartic.complete',
            'normalization_scale':S,'normalized_parameters':[8*L**4,a,b,c,d]}


def emit_square_leading(L,u,v,w,z,name='quartic_points'):
    solve_square_leading(L,u,v,w,z)
    if not name.isidentifier() or not name.isascii():raise ValueError('simple ASCII identifier required')
    return ('import PerfectPower.Tactic.SquareLeadingQuartic\n'
            f'native_square_leading_quartic {name} for {L}, {u}, {v}, {w}, {z}\n'
            f'#print axioms {name}_complete\n')
