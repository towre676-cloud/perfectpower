"""Exact finite/branch/infinity overlap maps and local metric pullbacks."""
from fractions import Fraction as Q
from . import polyalg as P,bernstein_boxes as B
from .metric_boxes import chart_density,ceval,cmul,modsq


ONE={(0,0):Q(1)};X={(1,0):Q(1)};Y={(0,1):Q(1)}


def _compose(f,g):
    value=P.ZERO
    for c in reversed(f):value=P.add(P.mul(value,g),P.poly([c]))
    return value


def _data(coefficients,chart,branch=None):
    finite=chart_density(coefficients,'finite');source=chart_density(coefficients,chart,branch)
    f=P.poly(map(Q,finite['coefficients']));m=P.degree(f);g=finite['genus'];r=B.add(B.power(X,2),B.power(Y,2))
    if chart=='branch':
        b=Q(branch);z=cmul((X,Y),(X,Y));z=(B.add(z[0],{(0,0):b}),z[1]);den=ONE
        linear=P.poly([-b,1]);quotient=P.exact_div(f,linear)
        argument=P.poly([b,0,1]);lhs=_compose(f,argument);rhs=P.mul(P.poly([0,0,1]),_compose(quotient,argument))
        finite_n={}
        for j in range(g):finite_n=B.add(finite_n,B.power(modsq(z),j))
        if B.poly(source['numerator'])!=B.scale(finite_n,4):raise AssertionError('branch numerator pullback')
        jacobian=dict(numerator=B.encode(B.scale(r,4)),denominator=B.encode(ONE))
        identity=dict(route='branch_factorization',left=list(map(str,lhs)),right=list(map(str,rhs)),numerator_multiplier=4)
    elif chart=='infinity':
        k=2 if m%2 else 1
        z=(X,B.scale(Y,-1))
        if k==2:z=cmul(z,z)
        den=B.power(r,k)
        # t^(k*m) f(t^-k)=reverse(f)(t^k), an exact polynomial identity.
        lhs=P.poly([f[m-i//k] if i%k==0 else 0 for i in range(k*m+1)])
        argument=P.poly([0]*k+[1]);rhs=_compose(tuple(reversed(f)),argument)
        source_n={}
        for j in range(g):source_n=B.add(source_n,B.power(r,k*j))
        if k==2:source_n=B.scale(source_n,4)
        if B.poly(source['numerator'])!=source_n:raise AssertionError('infinity numerator pullback')
        jacobian=dict(numerator=B.encode({(0,0):Q(k*k)}),denominator=B.encode(B.power(r,k+1)))
        identity=dict(route='reciprocal_factorization',left=list(map(str,lhs)),right=list(map(str,rhs)),
            reciprocal_power=k,finite_density_squared_radial_exponent=k*m-2*k*(g-1),
            jacobian_squared_radial_exponent=-2*(k+1),source_numerator_multiplier=k*k)
        if k*m-2*k*(g-1)!=2*(k+1):raise AssertionError('metric radial exponents do not cancel')
    else:raise ValueError('source chart must be branch or infinity; target is finite')
    if lhs!=rhs:raise AssertionError('chart polynomial identity failed')
    return dict(coefficients=finite['coefficients'],chart=chart,branch=source['branch'],genus=g,
        real_numerator=B.encode(z[0]),imaginary_numerator=B.encode(z[1]),denominator=B.encode(den),
        jacobian_density=jacobian,identity=identity,
        claim='source density equals finite density evaluated at the map times |dx/dt|^2, away from map poles and finite-chart branch roots')


def certify_transition(coefficients,chart,source_box,target_box,branch=None,*,depth=3,node_limit=10000):
    data=_data(coefficients,chart,branch);target=B.rectangle(target_box);box=B.rectangle(source_box)
    nx,ny,den=(B.poly(data[k]) for k in ('real_numerator','imaginary_numerator','denominator'))
    a,b,c,d=target
    gaps=dict(denominator_positive=den,x_lower=B.add(nx,B.scale(den,-a)),x_upper=B.add(B.scale(den,b),B.scale(nx,-1)),
        y_lower=B.add(ny,B.scale(den,-c)),y_upper=B.add(B.scale(den,d),B.scale(ny,-1)))
    # Branch coordinates at t=0 would map into a singular finite chart.
    gaps['nonzero_parameter']=B.add(B.power(X,2),B.power(Y,2))
    witnesses={name:B.certify(gap,box,depth=depth,node_limit=node_limit) for name,gap in gaps.items()}
    return dict(schema='pp-chart-transition/1',data=data,source_box=list(map(str,box)),target_box=list(map(str,target)),
        witnesses=witnesses,complete=all(w['complete'] for w in witnesses.values()),kernel_checked=False,
        scope='one certified chart overlap; does not assert coverage of the entire compact curve')


def verify_transition(packet):
    try:
        data=packet['data']
        if packet['schema']!='pp-chart-transition/1' or packet['kernel_checked'] is not False or data!=_data(data['coefficients'],data['chart'],data['branch']):return False
        nx,ny,den=(B.poly(data[k]) for k in ('real_numerator','imaginary_numerator','denominator'))
        a,b,c,d=B.rectangle(packet['target_box'])
        gaps=dict(denominator_positive=den,x_lower=B.add(nx,B.scale(den,-a)),x_upper=B.add(B.scale(den,b),B.scale(nx,-1)),
            y_lower=B.add(ny,B.scale(den,-c)),y_upper=B.add(B.scale(den,d),B.scale(ny,-1)),nonzero_parameter=B.add(B.power(X,2),B.power(Y,2)))
        witnesses=packet['witnesses']
        return set(witnesses)==set(gaps) and all(witnesses[k]['sign']==1 and B.verify(witnesses[k]) and B.poly(witnesses[k]['polynomial'])==p and witnesses[k]['box']==packet['source_box'] for k,p in gaps.items()) and packet['complete']==all(w['complete'] for w in witnesses.values())
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


def transport_point(packet,point):
    if not verify_transition(packet) or not packet['complete']:raise ValueError('complete transition certificate required')
    x,y=map(Q,point);a,b,c,d=map(Q,packet['source_box'])
    if not a<=x<=b or not c<=y<=d:raise ValueError('point outside certified overlap')
    data=packet['data'];den=B.evaluate(data['denominator'],x,y)
    values=[B.evaluate(data[k],x,y)/den for k in ('real_numerator','imaginary_numerator')]
    jacobian=data['jacobian_density'];factor=B.evaluate(jacobian['numerator'],x,y)/B.evaluate(jacobian['denominator'],x,y)
    return dict(source_point=list(map(str,(x,y))),target_point=list(map(str,values)),density_multiplier=str(factor))
