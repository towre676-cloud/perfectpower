"""Equal-mass two-dimensional sunrise: exact relative telescoping certificate."""
from .rational_functions import RationalFunction as RF, AlgebraBudget, solve_many
from .symmetry_quotients import PolynomialCurve
from .differential_modules import DifferentialModule


def add(a,b):
    c=dict(a)
    for k,v in b.items():c[k]=c.get(k,0)+v
    return {k:v for k,v in c.items() if v}
def scale(a,c):return {k:v*c for k,v in a.items() if v*c}
def product(a,b):
    c={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():c[(i+k,j+l)]=c.get((i+k,j+l),0)+v*w
    return {k:v for k,v in c.items() if v}
def derivative(a,axis):return {(i-int(axis==0),j-int(axis==1)):(i if axis==0 else j)*v for (i,j),v in a.items() if (i if axis==0 else j)}
def swap(a):return {(j,i):v for (i,j),v in a.items()}


def sunrise_certificate():
    budget=AlgebraBudget();t=RF([0,1],budget=budget);z=t.coerce(0);one=t.coerce(1)
    f={(2,1):one,(1,2):one,(2,0):one,(0,2):one,(1,1):3-t,(1,0):one,(0,1):one}
    c2=t*(t-1)*(t-9);c1=3*t*t-20*t+9;c0=t-3
    q=add(add({(2,2):2*c2},scale(product({(1,1):one},f),c1)),scale(product(f,f),c0))
    fx,fy=derivative(f,0),derivative(f,1)
    def divergence(u):
        v=swap(u)
        return add(product(add(derivative(u,0),derivative(v,1)),f),scale(add(product(u,fx),product(v,fy)),-2))
    fixed={(0,2):3*one};target=add(q,scale(divergence(fixed),-1));states=[(i,j) for i in range(1,4) for j in range(5-i)]
    columns=[divergence({state:one}) for state in states];keys=sorted(set(target).union(*(set(v) for v in columns)))
    solution=solve_many([[c.get(k,z) for c in columns] for k in keys],[[target.get(k,z)] for k in keys])
    if solution is None:raise AssertionError('sunrise boundary telescope ansatz failed')
    u=add(fixed,{state:v[0] for state,v in zip(states,solution)})
    if divergence(u)!=q:raise AssertionError('sunrise telescope identity failed')
    quartic=[one,2-2*t,t*t-6*t+3,2-2*t,one];curve=PolynomialCurve(quartic,budget);op=curve.observable()
    expected=[(c0/c2).packet(),(c1/c2).packet(),one.packet()]
    if op['monic_operator']!=expected:raise AssertionError('sunrise absolute period operator differs')
    a=[[z,one,z],[-c0/c2,-c1/c2,-6/c2],[z,z,z]]
    packet=lambda p:[dict(x_power=i,y_power=j,coefficient=v.packet()) for (i,j),v in sorted(p.items())]
    return dict(schema='pp-sunrise-relative-certificate/1',symanzik=packet(f),elliptic_curve=curve.evidence(),period_operator=op,
      U=packet(u),V=packet(swap(u)),exact_divergence_identity_checked=True,
      identity='L(1/F)=partial_x(U/F^2)+partial_y(V/F^2)',boundary=dict(U_at_x_zero='3 y^2',V_at_y_zero='3 x^2',integrated_value=-6,
        calculation='-3 integral_0^infinity (1+y)^(-2)dy -3 integral_0^infinity (1+x)^(-2)dx = -6',infinity_terms_zero=True),
      relative_module=DifferentialModule.from_matrix(a,'sunrise relative state [I,Iprime,1]').evidence(),
      scope='equal masses, two dimensions, I=integral over positive affine quadrant dx dy/F, nonsingular Euclidean parameters; relative amplitude satisfies L I=-6, absolute periods satisfy L Pi=0')
