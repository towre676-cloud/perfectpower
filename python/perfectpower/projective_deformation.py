"""Binary-form tangent quotients by full projective coordinate motion."""
from . import field_polynomials as F
from .rational_functions import RationalFunction as RF, AlgebraBudget, solve_many
from .curve_families import encode_matrix


def field_rref(rows):
    a=[list(r) for r in rows];pivots=[]
    for c in range(len(a[0])):
        k=len(pivots);p=next((i for i in range(k,len(a)) if a[i][c]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k];v=a[k][c];a[k]=[x/v for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                v=a[i][c]
                if v:a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        pivots.append(c)
        if len(pivots)==len(a):break
    return a,pivots


def quotient(f,dt,binary_degree,*,with_tangent=False):
    d=binary_degree;zero=f[0].coerce(0);f=F.trim(f)
    if d not in (4,6,8) or not d-1<=len(f)-1<=d:raise ValueError('squarefree binary degree 4, 6 or 8 with at most one root at infinity required')
    common,_,_=F.extended_gcd(f,F.derivative(f))
    if len(common)!=1:raise ValueError('generically singular binary form')
    pad=lambda p:list(p)+[zero]*(d+1-len(p))
    dx=F.derivative(f)
    orbit=[pad(dx),pad(F.add(F.scale([zero]+dx,2),F.scale(f,-d))),
           pad(F.add(F.scale([zero]+f,d),F.scale([zero,zero]+dx,-1))),pad(f)]
    _,pivots=field_rref(orbit)
    if len(pivots)!=4:raise AssertionError('smooth binary form has deficient projective orbit')
    dt=pad(dt);speeds=solve_many([[o[i] for o in orbit] for i in pivots],[[dt[i]] for i in pivots]);speeds=[v[0] for v in speeds]
    residual=[dt[i]-sum((speeds[j]*orbit[j][i] for j in range(4)),zero) for i in range(d+1)]
    if any(residual[i] for i in pivots):raise AssertionError('projective tangent identity failed')
    packet=dict(schema='pp-projective-deformation/1',binary_degree=d,genus=(d-2)//2,
        orbit_generators=encode_matrix(orbit),generator_names=['Z d_X','X d_X-Z d_Z','X d_Z','form scaling'],
        coordinate_flow=[a.packet() for a in speeds],essential_tangent=[a.packet() for a in residual],
        pivot_coefficients=pivots,quotient_dimension=d-3,coordinate_only_generic=not any(residual),
        identity_checked=True,identity='F_parameter = sum flow_j orbit_j + essential_tangent',
        infinity_is_movable=True,execution_verified=False,
        scope='full PGL(2) plus form-scaling tangent quotient of a smooth binary branch form on the nonzero pivot chart; local tangent triviality does not establish a global rational isomorphism or integer-coordinate preservation')
    return (packet,residual) if with_tangent else packet


def projective_deformation(specification,binary_degree=None):
    if not isinstance(specification,dict) or 'coefficients' not in specification or set(specification)-{'coefficients','work_limit','degree_limit','bit_limit'}:raise ValueError('coefficient arrays and optional algebra budgets required')
    budget=AlgebraBudget(**{k:specification[k] for k in ('work_limit','degree_limit','bit_limit') if k in specification})
    raw=specification['coefficients']
    if not isinstance(raw,(list,tuple)) or not 4<=len(raw)<=9:raise ValueError('bounded binary form coefficient list required')
    f=[RF.parse(a,budget) for a in raw]
    if any(a.d!=(1,) or len(a.n)>9 for a in f):raise ValueError('polynomial parameter degree at most eight required')
    m=len(F.trim(f))-1;d=binary_degree if binary_degree is not None else m+(m%2)
    result=quotient(f,[a.derivative() for a in f],d);result['algebra_work']=budget.work
    return result
