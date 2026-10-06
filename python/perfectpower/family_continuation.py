"""Marked numerical periods with exact exclusion of parameter-path poles.

Rational complex path vertices are interpreted exactly (floats by decimal
repr). Sturm counts exclude polynomial zeros on entire segments. Numerical
roots, quadrature and ODE error estimates are not rigorous enclosures.
"""
import cmath
import math
from fractions import Fraction as Q
from . import polyalg as P
from .core import mul
from .observable_machine import _q
from .analytic_surface import pair
from .divisor_square import WorkLimit


def exact_point(value):
    def coordinate(x):
        if type(x) is float:
            if not math.isfinite(x): raise ValueError('finite coordinate required')
            x = repr(x)
        return _q(x)
    if isinstance(value,(list,tuple)):
        if len(value)!=2: raise ValueError('complex coordinates need [real, imaginary]')
        return tuple(map(coordinate,value))
    return coordinate(value),Q(0)


def numeric(point):
    value=complex(float(point[0]),float(point[1]))
    if not math.isfinite(value.real) or not math.isfinite(value.imag):raise ValueError('coordinate exceeds numerical range')
    return value


def pullback(polynomial,a,b):
    """Real/imaginary parts of p(a+s(b-a)), both exact polynomials in s."""
    ar,ai=a;dr,di=b[0]-ar,b[1]-ai
    real,imag=P.ZERO,P.ZERO
    for coefficient in reversed(polynomial):
        real,imag=P.add(P.add(mul(real,(ar,dr)),P.scale(mul(imag,(ai,di)),-1)),(coefficient,)),P.add(mul(real,(ai,di)),mul(imag,(ar,dr)))
        if any(max(abs(c.numerator).bit_length(),c.denominator.bit_length())>8192 for p in (real,imag) for c in p):
            raise WorkLimit('exact path polynomial bit budget')
    return real,imag


def path_certificate(family,path,extra=()):
    if not isinstance(path,(list,tuple)) or not 2<=len(path)<=256:raise ValueError('two through 256 path vertices required')
    points=[exact_point(v) for v in path]
    exclusions=[('family_discriminant',family.discriminant)]+list(extra)
    exclusions += [('connection_denominator',a.d) for row in family.connection for a in row]
    unique=[];seen=set()
    for label,p in exclusions:
        p=P.monic(P.poly(p))
        if p not in seen:unique.append((label,p));seen.add(p)
    records=[]
    for i,(a,b) in enumerate(zip(points,points[1:])):
        for label,p in unique:
            real,imag=pullback(p,a,b);common=P.gcd_poly(real,imag)
            if not common or not P.evaluate(common,0) or not P.evaluate(common,1):
                raise ValueError(f'parameter segment {i} meets {label}')
            chain=P.sturm_chain(P.exact_div(common,P.gcd_poly(common,P.derivative(common)))) if P.degree(common)>0 else []
            count=P.count_real_roots(chain,0,1) if chain else 0
            if count:raise ValueError(f'parameter segment {i} meets {label}')
            records.append(dict(segment=i,excluded=label,pullback_real=list(map(str,real)),pullback_imaginary=list(map(str,imag)),
                common_real_zero_polynomial=list(map(str,common)),sturm_chain=chain,interior_zero_count=count))
    return points,dict(schema='pp-family-path-exclusion/1',vertices=[[str(x),str(y)] for x,y in points],checks=records,
        exact_no_excluded_zero_on_segments=True,execution_verified=False,
        scope='Sturm exclusion on the supplied rational straight segments; does not bound numerical ODE error or distance to a pole')


def tolerance_value(tolerance):
    if type(tolerance) not in (int,float) or not math.isfinite(tolerance) or not 1e-13<=tolerance<=1e-2:
        raise ValueError('numerical tolerance in [1e-13,1e-2] required')
    return float(tolerance)


def marked_period(family,parameter,contour,tolerance=1e-10):
    import numpy as np
    from scipy.integrate import quad_vec
    tolerance=tolerance_value(tolerance);point=exact_point(parameter);t=numeric(point)
    # Exact endpoint exclusion also applies to complex rational parameters.
    path_certificate(family,[parameter,parameter])
    if not isinstance(contour,dict) or not {'center','radius'}<=set(contour) or set(contour)-{'center','radius','sheet','turns'}:
        raise ValueError('circle center, radius and optional sheet/turns required')
    center=numeric(exact_point(contour['center']));radius=float(_q(repr(contour['radius']) if type(contour['radius']) is float else contour['radius']))
    sheet=contour.get('sheet',0)
    if not math.isfinite(radius) or radius<=0 or type(sheet) is not int or sheet not in (0,1):
        raise ValueError('positive finite circle radius and sheet 0 or 1 required')
    coefficients=[a.evaluate(t) for a in family.f]
    roots=list(map(complex,np.roots(list(reversed(coefficients)))))
    scale=max(1.,radius,abs(center),max(map(abs,roots)))
    clearance=min(abs(abs(root-center)-radius) for root in roots)
    separation=min(abs(a-b) for i,a in enumerate(roots) for b in roots[i+1:])
    if clearance<1e-8*scale or separation<1e-8*scale:raise ValueError('numerical contour/root separation too small')
    inside=[r for r in roots if abs(r-center)<radius];outside=[r for r in roots if abs(r-center)>radius]
    turns=contour.get('turns',2//math.gcd(2,len(inside)))
    if type(turns) is not int or not 1<=turns<=8 or turns*len(inside)%2:
        raise ValueError('one through eight turns closing the lifted contour required')
    def log_polynomial(theta):
        phase=cmath.exp(1j*theta)
        return sum(math.log(radius)+1j*theta+cmath.log(1+(center-r)/radius/phase) for r in inside)+sum(cmath.log(center-r)+cmath.log(1+radius/(center-r)*phase) for r in outside)
    start=center+radius;adjustment=cmath.log(P.evaluate(coefficients,start))+2j*math.pi*sheet-log_polynomial(0.)
    def integrand(theta):
        phase=cmath.exp(1j*theta);x=center+radius*phase
        density=cmath.exp(-(log_polynomial(theta)+adjustment)/2)*1j*radius*phase
        return np.array([x**i*density for i in range(family.dimension)],complex)
    values,error=quad_vec(integrand,0.,2*math.pi*turns,epsabs=tolerance,epsrel=tolerance,limit=1000)
    return dict(schema='pp-marked-family-period/1',parameter=[str(x) for x in point],
        contour=dict(center=pair(center),radius=radius,sheet=sheet,turns=turns),period_vector=[pair(v) for v in values],
        enclosed_roots=len(inside),sheet_winding=len(inside)*turns,closed_lift=True,
        minimum_numerical_contour_clearance=clearance,minimum_numerical_root_separation=separation,
        polynomial_root_residual=max(abs(P.evaluate(coefficients,r)) for r in roots),quadrature_error_estimate=float(error),
        certified_error_bound=False,symplectic_basis_claim=False,
        marking='x circle traversed counterclockwise; initial y uses principal sqrt(P(center+radius,t)) times (-1)^sheet',
        scope='numerical period vector on the supplied closed lifted contour; root count and quadrature are numerical')


def integrate_segments(points,initial,rhs,tolerance):
    import numpy as np
    from scipy.integrate import solve_ivp
    state=np.array(initial,complex);trajectory=[state.copy()];calls=0
    for a,b in zip(points,points[1:]):
        start,delta=numeric(a),numeric(b)-numeric(a)
        if not delta:trajectory.append(state.copy());continue
        def derivative(s,v):
            nonlocal calls
            calls+=1
            if calls>200000:raise WorkLimit('numerical continuation evaluation budget')
            out=delta*np.asarray(rhs(start+s*delta,v),complex)
            if not np.all(np.isfinite(out)):raise ValueError('nonfinite numerical continuation derivative')
            return out
        result=solve_ivp(derivative,(0.,1.),state,method='DOP853',rtol=tolerance,atol=tolerance,max_step=.125)
        if not result.success or not np.all(np.isfinite(result.y[:,-1])):raise ValueError('numerical continuation failed')
        state=result.y[:,-1];trajectory.append(state.copy())
    return trajectory,calls


def matrix_value(matrix,t):
    import numpy as np
    return np.array([[complex(a.evaluate(t)) for a in row] for row in matrix])


def transport(family,path,tolerance=1e-10):
    import numpy as np
    tolerance=tolerance_value(tolerance);points,certificate=path_certificate(family,path);n=family.dimension
    def rhs(t,v):return (matrix_value(family.connection,t)@v.reshape(n,n)).reshape(-1)
    values,calls=integrate_segments(points,np.eye(n,dtype=complex).reshape(-1),rhs,tolerance)
    return dict(schema='pp-family-transport/1',path_exclusion=certificate,
        transfer_matrix=[[pair(v) for v in row] for row in values[-1].reshape(n,n)],
        vertex_transfer_matrices=[[[pair(v) for v in row] for row in value.reshape(n,n)] for value in values],
        numerical_evaluations=calls,tolerance=tolerance,certified_error_bound=False,
        closed_parameter_path=points[0]==points[-1],
        scope='numerical transport of the de Rham period state; a closed path gives this basis monodromy, not an integral symplectic homology matrix')


def period_path(family,path,contour,coefficients=None,mode='matrix',tolerance=1e-10):
    import numpy as np
    from .rational_functions import RationalFunction as RF
    tolerance=tolerance_value(tolerance)
    if mode not in ('matrix','scalar'):raise ValueError('matrix or scalar continuation mode required')
    packet,rows,operator=family._observable(coefficients)
    weights=[RF.parse(v) for v in (coefficients if coefficients is not None else [1]+[0]*(family.dimension-1))]
    extra=[('observable_denominator',a.d) for a in weights]
    if mode=='scalar':
        extra += [('scalar_operator_denominator',a.d) for a in operator]
        extra += [('scalar_leading_coefficient',P.poly(packet['scalar_leading_coefficient']))]
    points,certificate=path_certificate(family,path,extra)
    initial=marked_period(family,path[0],contour,tolerance);periods=np.array([complex(*v) for v in initial['period_vector']]);n=family.dimension
    if mode=='matrix':
        rhs=lambda t,v: matrix_value(family.connection,t)@v
        seed=periods
    else:
        seed=matrix_value(rows,numeric(points[0]))@periods if rows else np.zeros(1,complex)
        def rhs(t,v):
            if not rows:return np.zeros(1,complex)
            return np.array(list(v[1:])+[-sum(complex(a.evaluate(t))*value for a,value in zip(operator[:-1],v))],complex)
    values,calls=integrate_segments(points,seed,rhs,tolerance)
    trajectory=[]
    for point,state in zip(points,values):
        value=sum(complex(a.evaluate(numeric(point)))*v for a,v in zip(weights,state)) if mode=='matrix' else state[0]
        trajectory.append(dict(parameter=[str(x) for x in point],state=[pair(v) for v in state],observable=pair(value)))
    return dict(schema='pp-family-period-path/1',mode=mode,observable_order=packet['order'],initialization=initial,
        path_exclusion=certificate,trajectory=trajectory,numerical_evaluations=calls,tolerance=tolerance,
        certified_error_bound=False,scope='continued marked period observable; numerical quadrature and ODE propagation, exact polynomial exclusion on parameter segments')
